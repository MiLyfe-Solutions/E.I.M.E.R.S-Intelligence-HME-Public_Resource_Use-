import V185TrunkScan23Chunk0597

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3535073 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 2, 5, 3]
def baseStart_3535073 : Nat := 118140960795 + 3535073 * 2 ^ 59
def prefixEnd_3535073 : Nat := 4983230072969 + 3 ^ 40 * 3535073 * 2
def baseEnd_3535073 : Nat := 1815191597731552744330001

theorem tailTrace_3535073 : CollatzResearch.WordTrace tailWord_3535073 prefixEnd_3535073 1815191597731552744330001 := by
  unfold tailWord_3535073
  simp only [CollatzResearch.WordTrace]
  refine ⟨128934704722041738247121873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85956469814694492164747915 128934704722041738247121873)
  ·
    refine ⟨96701028541531303685341405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128934704722041738247121873 96701028541531303685341405)
    ·
      refine ⟨36262885703074238882003027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96701028541531303685341405 36262885703074238882003027)
      ·
        refine ⟨54394328554611358323004541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36262885703074238882003027 54394328554611358323004541)
        ·
          refine ⟨20397873207979259371126703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54394328554611358323004541 20397873207979259371126703)
          ·
            refine ⟨30596809811968889056690055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20397873207979259371126703 30596809811968889056690055)
            ·
              refine ⟨45895214717953333585035083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30596809811968889056690055 45895214717953333585035083)
              ·
                refine ⟨68842822076930000377552625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45895214717953333585035083 68842822076930000377552625)
                ·
                  refine ⟨51632116557697500283164469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68842822076930000377552625 51632116557697500283164469)
                  ·
                    refine ⟨4840510927284140651546669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51632116557697500283164469 4840510927284140651546669)
                    ·
                      refine ⟨1815191597731552744330001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4840510927284140651546669 1815191597731552744330001)
                      ·
                        rfl

theorem cell23_3535073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_3535073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535073 prefixEnd_3535073 := by exact prefixLift 3535073
  have htrace : WordTrace (prefixWord ++ tailWord_3535073) baseStart_3535073 baseEnd_3535073 := by
    simpa [prefixWord, tailWord_3535073, baseEnd_3535073] using wordTrace_append hprefix tailTrace_3535073
  have hstable : (prefixWord ++ tailWord_3535073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535073).length < 2 ^ (prefixWord ++ tailWord_3535073).sum := by decide
  have hdescent : baseEnd_3535073 < baseStart_3535073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535127 : List Nat := [1, 1, 3, 4, 1, 4, 1, 2, 1, 5]
def baseStart_3535127 : Nat := 118140960795 + 3535127 * 2 ^ 59
def prefixEnd_3535127 : Nat := 4983230072969 + 3 ^ 40 * 3535127 * 2
def baseEnd_3535127 : Nat := 605073108562298511018251

theorem tailTrace_3535127 : CollatzResearch.WordTrace tailWord_3535127 prefixEnd_3535127 605073108562298511018251 := by
  unfold tailWord_3535127
  simp only [CollatzResearch.WordTrace]
  refine ⟨128936674263846105469587635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85957782842564070313058423 128936674263846105469587635)
  ·
    refine ⟨193405011395769158204381453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128936674263846105469587635 193405011395769158204381453)
    ·
      refine ⟨72526879273413434326643045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193405011395769158204381453 72526879273413434326643045)
      ·
        refine ⟨13598789863765018936245571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72526879273413434326643045 13598789863765018936245571)
        ·
          refine ⟨20398184795647528404368357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13598789863765018936245571 20398184795647528404368357)
          ·
            refine ⟨3824659649183911575819067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20398184795647528404368357 3824659649183911575819067)
            ·
              refine ⟨5736989473775867363728601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3824659649183911575819067 5736989473775867363728601)
              ·
                refine ⟨4302742105331900522796451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5736989473775867363728601 4302742105331900522796451)
                ·
                  refine ⟨6454113157997850784194677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4302742105331900522796451 6454113157997850784194677)
                  ·
                    refine ⟨605073108562298511018251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6454113157997850784194677 605073108562298511018251)
                    ·
                      rfl

theorem cell23_3535127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 5].length) (baseStart_3535127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535127 prefixEnd_3535127 := by exact prefixLift 3535127
  have htrace : WordTrace (prefixWord ++ tailWord_3535127) baseStart_3535127 baseEnd_3535127 := by
    simpa [prefixWord, tailWord_3535127, baseEnd_3535127] using wordTrace_append hprefix tailTrace_3535127
  have hstable : (prefixWord ++ tailWord_3535127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535127).length < 2 ^ (prefixWord ++ tailWord_3535127).sum := by decide
  have hdescent : baseEnd_3535127 < baseStart_3535127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535140 : List Nat := [2, 3, 1, 3, 1, 3, 1, 2, 1, 6]
def baseStart_3535140 : Nat := 118140960795 + 3535140 * 2 ^ 59
def prefixEnd_3535140 : Nat := 4983230072969 + 3 ^ 40 * 3535140 * 2
def baseEnd_3535140 : Nat := 605075333645134660730731

theorem tailTrace_3535140 : CollatzResearch.WordTrace tailWord_3535140 prefixEnd_3535140 605075333645134660730731 := by
  unfold tailWord_3535140
  simp only [CollatzResearch.WordTrace]
  refine ⟨64468574206399504344905437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85958098941866005793207249 64468574206399504344905437)
  ·
    refine ⟨24175715327399814129339539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64468574206399504344905437 24175715327399814129339539)
    ·
      refine ⟨36263572991099721194009309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24175715327399814129339539 36263572991099721194009309)
      ·
        refine ⟨13598839871662395447753491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36263572991099721194009309 13598839871662395447753491)
        ·
          refine ⟨20398259807493593171630237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13598839871662395447753491 20398259807493593171630237)
          ·
            refine ⟨7649347427810097439361339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20398259807493593171630237 7649347427810097439361339)
            ·
              refine ⟨11474021141715146159042009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7649347427810097439361339 11474021141715146159042009)
              ·
                refine ⟨8605515856286359619281507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11474021141715146159042009 8605515856286359619281507)
                ·
                  refine ⟨12908273784429539428922261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8605515856286359619281507 12908273784429539428922261)
                  ·
                    refine ⟨605075333645134660730731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12908273784429539428922261 605075333645134660730731)
                    ·
                      rfl

theorem cell23_3535140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_3535140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535140 prefixEnd_3535140 := by exact prefixLift 3535140
  have htrace : WordTrace (prefixWord ++ tailWord_3535140) baseStart_3535140 baseEnd_3535140 := by
    simpa [prefixWord, tailWord_3535140, baseEnd_3535140] using wordTrace_append hprefix tailTrace_3535140
  have hstable : (prefixWord ++ tailWord_3535140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535140).length < 2 ^ (prefixWord ++ tailWord_3535140).sum := by decide
  have hdescent : baseEnd_3535140 < baseStart_3535140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535144 : List Nat := [2, 1, 5, 1, 3, 1, 3, 1, 1, 5]
def baseStart_3535144 : Nat := 118140960795 + 3535144 * 2 ^ 59
def prefixEnd_3535144 : Nat := 4983230072969 + 3 ^ 40 * 3535144 * 2
def baseEnd_3535144 : Nat := 605076018286007322180725

theorem tailTrace_3535144 : CollatzResearch.WordTrace tailWord_3535144 prefixEnd_3535144 605076018286007322180725 := by
  unfold tailWord_3535144
  simp only [CollatzResearch.WordTrace]
  refine ⟨64468647152392258686478243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85958196203189678248637657 64468647152392258686478243)
  ·
    refine ⟨96702970728588388029717365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64468647152392258686478243 96702970728588388029717365)
    ·
      refine ⟨9065903505805161377786003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96702970728588388029717365 9065903505805161377786003)
      ·
        refine ⟨13598855258707742066679005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9065903505805161377786003 13598855258707742066679005)
        ·
          refine ⟨5099570722015403275004627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13598855258707742066679005 5099570722015403275004627)
          ·
            refine ⟨7649356083023104912506941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5099570722015403275004627 7649356083023104912506941)
            ·
              refine ⟨2868508531133664342190103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7649356083023104912506941 2868508531133664342190103)
              ·
                refine ⟨4302762796700496513285155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2868508531133664342190103 4302762796700496513285155)
                ·
                  refine ⟨6454144195050744769927733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4302762796700496513285155 6454144195050744769927733)
                  ·
                    refine ⟨605076018286007322180725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6454144195050744769927733 605076018286007322180725)
                    ·
                      rfl

theorem cell23_3535144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_3535144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535144 prefixEnd_3535144 := by exact prefixLift 3535144
  have htrace : WordTrace (prefixWord ++ tailWord_3535144) baseStart_3535144 baseEnd_3535144 := by
    simpa [prefixWord, tailWord_3535144, baseEnd_3535144] using wordTrace_append hprefix tailTrace_3535144
  have hstable : (prefixWord ++ tailWord_3535144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535144).length < 2 ^ (prefixWord ++ tailWord_3535144).sum := by decide
  have hdescent : baseEnd_3535144 < baseStart_3535144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535153 : List Nat := [1, 2, 2, 3, 4, 11]
def baseStart_3535153 : Nat := 118140960795 + 3535153 * 2 ^ 59
def prefixEnd_3535153 : Nat := 4983230072969 + 3 ^ 40 * 3535153 * 2
def baseEnd_3535153 : Nat := 7470093317629269264731

theorem tailTrace_3535153 : CollatzResearch.WordTrace tailWord_3535153 prefixEnd_3535153 7470093317629269264731 := by
  unfold tailWord_3535153
  simp only [CollatzResearch.WordTrace]
  refine ⟨128937622561751911910034113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85958415041167941273356075 128937622561751911910034113)
  ·
    refine ⟨96703216921313933932525585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128937622561751911910034113 96703216921313933932525585)
    ·
      refine ⟨72527412690985450449394189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96703216921313933932525585 72527412690985450449394189)
      ·
        refine ⟨27197779759119543918522821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72527412690985450449394189 27197779759119543918522821)
        ·
          refine ⟨5099583704834914484723029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27197779759119543918522821 5099583704834914484723029)
          ·
            refine ⟨7470093317629269264731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5099583704834914484723029 7470093317629269264731)
            ·
              rfl

theorem cell23_3535153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 11].length) (baseStart_3535153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535153 prefixEnd_3535153 := by exact prefixLift 3535153
  have htrace : WordTrace (prefixWord ++ tailWord_3535153) baseStart_3535153 baseEnd_3535153 := by
    simpa [prefixWord, tailWord_3535153, baseEnd_3535153] using wordTrace_append hprefix tailTrace_3535153
  have hstable : (prefixWord ++ tailWord_3535153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535153).length < 2 ^ (prefixWord ++ tailWord_3535153).sum := by decide
  have hdescent : baseEnd_3535153 < baseStart_3535153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535157 : List Nat := [1, 3, 3, 1, 2, 1, 4, 2, 2, 4]
def baseStart_3535157 : Nat := 118140960795 + 3535157 * 2 ^ 59
def prefixEnd_3535157 : Nat := 4983230072969 + 3 ^ 40 * 3535157 * 2
def baseEnd_3535157 : Nat := 605078243368843471893205

theorem tailTrace_3535157 : CollatzResearch.WordTrace tailWord_3535157 prefixEnd_3535157 605078243368843471893205 := by
  unfold tailWord_3535157
  simp only [CollatzResearch.WordTrace]
  refine ⟨128937768453737420593179725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85958512302491613728786483 128937768453737420593179725)
  ·
    refine ⟨48351663170151532722442397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128937768453737420593179725 48351663170151532722442397)
    ·
      refine ⟨18131873688806824770915899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48351663170151532722442397 18131873688806824770915899)
      ·
        refine ⟨27197810533210237156373849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18131873688806824770915899 27197810533210237156373849)
        ·
          refine ⟨20398357899907677867280387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27197810533210237156373849 20398357899907677867280387)
          ·
            refine ⟨30597536849861516800920581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20398357899907677867280387 30597536849861516800920581)
            ·
              refine ⟨5737038159349034400172609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30597536849861516800920581 5737038159349034400172609)
              ·
                refine ⟨4302778619511775800129457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5737038159349034400172609 4302778619511775800129457)
                ·
                  refine ⟨3227083964633831850097093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4302778619511775800129457 3227083964633831850097093)
                  ·
                    refine ⟨605078243368843471893205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3227083964633831850097093 605078243368843471893205)
                    ·
                      rfl

theorem cell23_3535157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_3535157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535157 prefixEnd_3535157 := by exact prefixLift 3535157
  have htrace : WordTrace (prefixWord ++ tailWord_3535157) baseStart_3535157 baseEnd_3535157 := by
    simpa [prefixWord, tailWord_3535157, baseEnd_3535157] using wordTrace_append hprefix tailTrace_3535157
  have hstable : (prefixWord ++ tailWord_3535157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535157).length < 2 ^ (prefixWord ++ tailWord_3535157).sum := by decide
  have hdescent : baseEnd_3535157 < baseStart_3535157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535193 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 2, 2, 5]
def baseStart_3535193 : Nat := 118140960795 + 3535193 * 2 ^ 59
def prefixEnd_3535193 : Nat := 4983230072969 + 3 ^ 40 * 3535193 * 2
def baseEnd_3535193 : Nat := 1815253215410092274829449

theorem tailTrace_3535193 : CollatzResearch.WordTrace tailWord_3535193 prefixEnd_3535193 1815253215410092274829449 := by
  unfold tailWord_3535193
  simp only [CollatzResearch.WordTrace]
  refine ⟨128939081481606998741490233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85959387654404665827660155 128939081481606998741490233)
  ·
    refine ⟨96704311111205249056117675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128939081481606998741490233 96704311111205249056117675)
    ·
      refine ⟨145056466666807873584176513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96704311111205249056117675 145056466666807873584176513)
      ·
        refine ⟨108792350000105905188132385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145056466666807873584176513 108792350000105905188132385)
        ·
          refine ⟨81594262500079428891099289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108792350000105905188132385 81594262500079428891099289)
          ·
            refine ⟨61195696875059571668324467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81594262500079428891099289 61195696875059571668324467)
            ·
              refine ⟨91793545312589357502486701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61195696875059571668324467 91793545312589357502486701)
              ·
                refine ⟨34422579492221009063432513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91793545312589357502486701 34422579492221009063432513)
                ·
                  refine ⟨25816934619165756797574385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34422579492221009063432513 25816934619165756797574385)
                  ·
                    refine ⟨19362700964374317598180789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25816934619165756797574385 19362700964374317598180789)
                    ·
                      refine ⟨1815253215410092274829449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19362700964374317598180789 1815253215410092274829449)
                      ·
                        rfl

theorem cell23_3535193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_3535193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535193 prefixEnd_3535193 := by exact prefixLift 3535193
  have htrace : WordTrace (prefixWord ++ tailWord_3535193) baseStart_3535193 baseEnd_3535193 := by
    simpa [prefixWord, tailWord_3535193, baseEnd_3535193] using wordTrace_append hprefix tailTrace_3535193
  have hstable : (prefixWord ++ tailWord_3535193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535193).length < 2 ^ (prefixWord ++ tailWord_3535193).sum := by decide
  have hdescent : baseEnd_3535193 < baseStart_3535193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535223 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 5]
def baseStart_3535223 : Nat := 118140960795 + 3535223 * 2 ^ 59
def prefixEnd_3535223 : Nat := 4983230072969 + 3 ^ 40 * 3535223 * 2
def baseEnd_3535223 : Nat := 1815268619829727157454311

theorem tailTrace_3535223 : CollatzResearch.WordTrace tailWord_3535223 prefixEnd_3535223 1815268619829727157454311 := by
  unfold tailWord_3535223
  simp only [CollatzResearch.WordTrace]
  refine ⟨128940175671498313865082323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85960117114332209243388215 128940175671498313865082323)
  ·
    refine ⟨193410263507247470797623485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128940175671498313865082323 193410263507247470797623485)
    ·
      refine ⟨72528848815217801549108807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193410263507247470797623485 72528848815217801549108807)
      ·
        refine ⟨108793273222826702323663211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72528848815217801549108807 108793273222826702323663211)
        ·
          refine ⟨163189909834240053485494817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108793273222826702323663211 163189909834240053485494817)
          ·
            refine ⟨122392432375680040114121113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163189909834240053485494817 122392432375680040114121113)
            ·
              refine ⟨91794324281760030085590835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122392432375680040114121113 91794324281760030085590835)
              ·
                refine ⟨137691486422640045128386253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91794324281760030085590835 137691486422640045128386253)
                ·
                  refine ⟨51634307408490016923144845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137691486422640045128386253 51634307408490016923144845)
                  ·
                    refine ⟨19362865278183756346179317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51634307408490016923144845 19362865278183756346179317)
                    ·
                      refine ⟨1815268619829727157454311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19362865278183756346179317 1815268619829727157454311)
                      ·
                        rfl

theorem cell23_3535223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_3535223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535223 prefixEnd_3535223 := by exact prefixLift 3535223
  have htrace : WordTrace (prefixWord ++ tailWord_3535223) baseStart_3535223 baseEnd_3535223 := by
    simpa [prefixWord, tailWord_3535223, baseEnd_3535223] using wordTrace_append hprefix tailTrace_3535223
  have hstable : (prefixWord ++ tailWord_3535223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535223).length < 2 ^ (prefixWord ++ tailWord_3535223).sum := by decide
  have hdescent : baseEnd_3535223 < baseStart_3535223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535240 : List Nat := [2, 1, 3, 3, 1, 1, 2, 2, 2, 1, 5]
def baseStart_3535240 : Nat := 118140960795 + 3535240 * 2 ^ 59
def prefixEnd_3535240 : Nat := 4983230072969 + 3 ^ 40 * 3535240 * 2
def baseEnd_3535240 : Nat := 1815277349000853590941733

theorem tailTrace_3535240 : CollatzResearch.WordTrace tailWord_3535240 prefixEnd_3535240 1815277349000853590941733 := by
  unfold tailWord_3535240
  simp only [CollatzResearch.WordTrace]
  refine ⟨64470397856218362884225587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85960530474957817178967449 64470397856218362884225587)
  ·
    refine ⟨96705596784327544326338381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64470397856218362884225587 96705596784327544326338381)
    ·
      refine ⟨36264598794122829122376893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96705596784327544326338381 36264598794122829122376893)
      ·
        refine ⟨13599224547796060920891335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36264598794122829122376893 13599224547796060920891335)
        ·
          refine ⟨20398836821694091381337003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13599224547796060920891335 20398836821694091381337003)
          ·
            refine ⟨30598255232541137072005505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20398836821694091381337003 30598255232541137072005505)
            ·
              refine ⟨22948691424405852804004129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30598255232541137072005505 22948691424405852804004129)
              ·
                refine ⟨17211518568304389603003097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22948691424405852804004129 17211518568304389603003097)
                ·
                  refine ⟨12908638926228292202252323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17211518568304389603003097 12908638926228292202252323)
                  ·
                    refine ⟨19362958389342438303378485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12908638926228292202252323 19362958389342438303378485)
                    ·
                      refine ⟨1815277349000853590941733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19362958389342438303378485 1815277349000853590941733)
                      ·
                        rfl

theorem cell23_3535240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_3535240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535240 prefixEnd_3535240 := by exact prefixLift 3535240
  have htrace : WordTrace (prefixWord ++ tailWord_3535240) baseStart_3535240 baseEnd_3535240 := by
    simpa [prefixWord, tailWord_3535240, baseEnd_3535240] using wordTrace_append hprefix tailTrace_3535240
  have hstable : (prefixWord ++ tailWord_3535240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535240).length < 2 ^ (prefixWord ++ tailWord_3535240).sum := by decide
  have hdescent : baseEnd_3535240 < baseStart_3535240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535327 : List Nat := [1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 4]
def baseStart_3535327 : Nat := 118140960795 + 3535327 * 2 ^ 59
def prefixEnd_3535327 : Nat := 4983230072969 + 3 ^ 40 * 3535327 * 2
def baseEnd_3535327 : Nat := 1815322021817794750553833

theorem tailTrace_3535327 : CollatzResearch.WordTrace tailWord_3535327 prefixEnd_3535327 1815322021817794750553833 := by
  unfold tailWord_3535327
  simp only [CollatzResearch.WordTrace]
  refine ⟨128943968863121539626868235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85962645908747693084578823 128943968863121539626868235)
  ·
    refine ⟨193415953294682309440302353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128943968863121539626868235 193415953294682309440302353)
    ·
      refine ⟨145061964971011732080226765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193415953294682309440302353 145061964971011732080226765)
      ·
        refine ⟨54398236864129399530085037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145061964971011732080226765 54398236864129399530085037)
        ·
          refine ⟨20399338824048524823781889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54398236864129399530085037 20399338824048524823781889)
          ·
            refine ⟨15299504118036393617836417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20399338824048524823781889 15299504118036393617836417)
            ·
              refine ⟨11474628088527295213377313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15299504118036393617836417 11474628088527295213377313)
              ·
                refine ⟨8605971066395471410032985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11474628088527295213377313 8605971066395471410032985)
                ·
                  refine ⟨6454478299796603557524739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8605971066395471410032985 6454478299796603557524739)
                  ·
                    refine ⟨9681717449694905336287109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6454478299796603557524739 9681717449694905336287109)
                    ·
                      refine ⟨1815322021817794750553833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9681717449694905336287109 1815322021817794750553833)
                      ·
                        rfl

theorem cell23_3535327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_3535327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535327 prefixEnd_3535327 := by exact prefixLift 3535327
  have htrace : WordTrace (prefixWord ++ tailWord_3535327) baseStart_3535327 baseEnd_3535327 := by
    simpa [prefixWord, tailWord_3535327, baseEnd_3535327] using wordTrace_append hprefix tailTrace_3535327
  have hstable : (prefixWord ++ tailWord_3535327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535327).length < 2 ^ (prefixWord ++ tailWord_3535327).sum := by decide
  have hdescent : baseEnd_3535327 < baseStart_3535327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535364 : List Nat := [2, 3, 2, 3, 1, 2, 1, 1, 1, 4, 3]
def baseStart_3535364 : Nat := 118140960795 + 3535364 * 2 ^ 59
def prefixEnd_3535364 : Nat := 4983230072969 + 3 ^ 40 * 3535364 * 2
def baseEnd_3535364 : Nat := 1815341020602011105791163

theorem tailTrace_3535364 : CollatzResearch.WordTrace tailWord_3535364 prefixEnd_3535364 1815341020602011105791163 := by
  unfold tailWord_3535364
  simp only [CollatzResearch.WordTrace]
  refine ⟨64472659181993747472982573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85963545575991663297310097 64472659181993747472982573)
  ·
    refine ⟨24177247193247655302368465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64472659181993747472982573 24177247193247655302368465)
    ·
      refine ⟨18132935394935741476776349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24177247193247655302368465 18132935394935741476776349)
      ·
        refine ⟨6799850773100903053791131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18132935394935741476776349 6799850773100903053791131)
        ·
          refine ⟨10199776159651354580686697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6799850773100903053791131 10199776159651354580686697)
          ·
            refine ⟨7649832119738515935515023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10199776159651354580686697 7649832119738515935515023)
            ·
              refine ⟨11474748179607773903272535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7649832119738515935515023 11474748179607773903272535)
              ·
                refine ⟨17212122269411660854908803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11474748179607773903272535 17212122269411660854908803)
                ·
                  refine ⟨25818183404117491282363205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17212122269411660854908803 25818183404117491282363205)
                  ·
                    refine ⟨4840909388272029615443101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25818183404117491282363205 4840909388272029615443101)
                    ·
                      refine ⟨1815341020602011105791163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4840909388272029615443101 1815341020602011105791163)
                      ·
                        rfl

theorem cell23_3535364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_3535364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535364 prefixEnd_3535364 := by exact prefixLift 3535364
  have htrace : WordTrace (prefixWord ++ tailWord_3535364) baseStart_3535364 baseEnd_3535364 := by
    simpa [prefixWord, tailWord_3535364, baseEnd_3535364] using wordTrace_append hprefix tailTrace_3535364
  have hstable : (prefixWord ++ tailWord_3535364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535364).length < 2 ^ (prefixWord ++ tailWord_3535364).sum := by decide
  have hdescent : baseEnd_3535364 < baseStart_3535364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535371 : List Nat := [1, 1, 1, 1, 7, 2, 2, 3, 1, 4]
def baseStart_3535371 : Nat := 118140960795 + 3535371 * 2 ^ 59
def prefixEnd_3535371 : Nat := 4983230072969 + 3 ^ 40 * 3535371 * 2
def baseEnd_3535371 : Nat := 605114871655530859467877

theorem tailTrace_3535371 : CollatzResearch.WordTrace tailWord_3535371 prefixEnd_3535371 605114871655530859467877 := by
  unfold tailWord_3535371
  simp only [CollatzResearch.WordTrace]
  refine ⟨128945573674962135141469967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85963715783308090094313311 128945573674962135141469967)
  ·
    refine ⟨193418360512443202712204951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128945573674962135141469967 193418360512443202712204951)
    ·
      refine ⟨290127540768664804068307427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193418360512443202712204951 290127540768664804068307427)
      ·
        refine ⟨435191311152997206102461141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290127540768664804068307427 435191311152997206102461141)
        ·
          refine ⟨10199796355148372018026433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 435191311152997206102461141 10199796355148372018026433)
          ·
            refine ⟨7649847266361279013519825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10199796355148372018026433 7649847266361279013519825)
            ·
              refine ⟨5737385449770959260139869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7649847266361279013519825 5737385449770959260139869)
              ·
                refine ⟨2151519543664109722552451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5737385449770959260139869 2151519543664109722552451)
                ·
                  refine ⟨3227279315496164583828677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2151519543664109722552451 3227279315496164583828677)
                  ·
                    refine ⟨605114871655530859467877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3227279315496164583828677 605114871655530859467877)
                    ·
                      rfl

theorem cell23_3535371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 3, 1, 4].length) (baseStart_3535371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535371 prefixEnd_3535371 := by exact prefixLift 3535371
  have htrace : WordTrace (prefixWord ++ tailWord_3535371) baseStart_3535371 baseEnd_3535371 := by
    simpa [prefixWord, tailWord_3535371, baseEnd_3535371] using wordTrace_append hprefix tailTrace_3535371
  have hstable : (prefixWord ++ tailWord_3535371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535371).length < 2 ^ (prefixWord ++ tailWord_3535371).sum := by decide
  have hdescent : baseEnd_3535371 < baseStart_3535371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535384 : List Nat := [2, 1, 2, 3, 3, 3, 1, 2, 6]
def baseStart_3535384 : Nat := 118140960795 + 3535384 * 2 ^ 59
def prefixEnd_3535384 : Nat := 4983230072969 + 3 ^ 40 * 3535384 * 2
def baseEnd_3535384 : Nat := 201705698912789003060119

theorem tailTrace_3535384 : CollatzResearch.WordTrace tailWord_3535384 prefixEnd_3535384 201705698912789003060119 := by
  unfold tailWord_3535384
  simp only [CollatzResearch.WordTrace]
  refine ⟨64473023911957519180846603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85964031882610025574462137 64473023911957519180846603)
  ·
    refine ⟨96709535867936278771269905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64473023911957519180846603 96709535867936278771269905)
    ·
      refine ⟨72532151900952209078452429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96709535867936278771269905 72532151900952209078452429)
      ·
        refine ⟨27199556962857078404419661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72532151900952209078452429 27199556962857078404419661)
        ·
          refine ⟨10199833861071404401657373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27199556962857078404419661 10199833861071404401657373)
          ·
            refine ⟨3824937697901776650621515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10199833861071404401657373 3824937697901776650621515)
            ·
              refine ⟨5737406546852664975932273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3824937697901776650621515 5737406546852664975932273)
              ·
                refine ⟨4303054910139498731949205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5737406546852664975932273 4303054910139498731949205)
                ·
                  refine ⟨201705698912789003060119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4303054910139498731949205 201705698912789003060119)
                  ·
                    rfl

theorem cell23_3535384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 6].length) (baseStart_3535384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535384 prefixEnd_3535384 := by exact prefixLift 3535384
  have htrace : WordTrace (prefixWord ++ tailWord_3535384) baseStart_3535384 baseEnd_3535384 := by
    simpa [prefixWord, tailWord_3535384, baseEnd_3535384] using wordTrace_append hprefix tailTrace_3535384
  have hstable : (prefixWord ++ tailWord_3535384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535384).length < 2 ^ (prefixWord ++ tailWord_3535384).sum := by decide
  have hdescent : baseEnd_3535384 < baseStart_3535384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535422 : List Nat := [4, 2, 1, 4, 2, 1, 1, 3, 1, 4]
def baseStart_3535422 : Nat := 118140960795 + 3535422 * 2 ^ 59
def prefixEnd_3535422 : Nat := 4983230072969 + 3 ^ 40 * 3535422 * 2
def baseEnd_3535422 : Nat := 605123600826657292955299

theorem tailTrace_3535422 : CollatzResearch.WordTrace tailWord_3535422 prefixEnd_3535422 605123600826657292955299 := by
  unfold tailWord_3535422
  simp only [CollatzResearch.WordTrace]
  refine ⟨16118429224722171356447065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85964955865184913901051013 16118429224722171356447065)
  ·
    refine ⟨12088821918541628517335299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16118429224722171356447065 12088821918541628517335299)
    ·
      refine ⟨18133232877812442776002949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12088821918541628517335299 18133232877812442776002949)
      ·
        refine ⟨3399981164589833020500553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18133232877812442776002949 3399981164589833020500553)
        ·
          refine ⟨2549985873442374765375415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3399981164589833020500553 2549985873442374765375415)
          ·
            refine ⟨3824978810163562148063123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2549985873442374765375415 3824978810163562148063123)
            ·
              refine ⟨5737468215245343222094685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3824978810163562148063123 5737468215245343222094685)
              ·
                refine ⟨2151550580717003708285507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5737468215245343222094685 2151550580717003708285507)
                ·
                  refine ⟨3227325871075505562428261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2151550580717003708285507 3227325871075505562428261)
                  ·
                    refine ⟨605123600826657292955299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3227325871075505562428261 605123600826657292955299)
                    ·
                      rfl

theorem cell23_3535422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_3535422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535422 prefixEnd_3535422 := by exact prefixLift 3535422
  have htrace : WordTrace (prefixWord ++ tailWord_3535422) baseStart_3535422 baseEnd_3535422 := by
    simpa [prefixWord, tailWord_3535422, baseEnd_3535422] using wordTrace_append hprefix tailTrace_3535422
  have hstable : (prefixWord ++ tailWord_3535422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535422).length < 2 ^ (prefixWord ++ tailWord_3535422).sum := by decide
  have hdescent : baseEnd_3535422 < baseStart_3535422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535434 : List Nat := [3, 1, 2, 1, 1, 4, 2, 3, 1, 1, 4]
def baseStart_3535434 : Nat := 118140960795 + 3535434 * 2 ^ 59
def prefixEnd_3535434 : Nat := 4983230072969 + 3 ^ 40 * 3535434 * 2
def baseEnd_3535434 : Nat := 1815376964247825831915841

theorem tailTrace_3535434 : CollatzResearch.WordTrace tailWord_3535434 prefixEnd_3535434 1815376964247825831915841 := by
  unfold tailWord_3535434
  simp only [CollatzResearch.WordTrace]
  refine ⟨32236967868433474225253339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85965247649155931267342237 32236967868433474225253339)
  ·
    refine ⟨48355451802650211337880009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32236967868433474225253339 48355451802650211337880009)
    ·
      refine ⟨36266588851987658503410007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48355451802650211337880009 36266588851987658503410007)
      ·
        refine ⟨54399883277981487755115011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36266588851987658503410007 54399883277981487755115011)
        ·
          refine ⟨81599824916972231632672517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54399883277981487755115011 81599824916972231632672517)
          ·
            refine ⟨15299967171932293431126097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81599824916972231632672517 15299967171932293431126097)
            ·
              refine ⟨11474975378949220073344573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15299967171932293431126097 11474975378949220073344573)
              ·
                refine ⟨4303115767105957527504215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11474975378949220073344573 4303115767105957527504215)
                ·
                  refine ⟨6454673650658936291256323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4303115767105957527504215 6454673650658936291256323)
                  ·
                    refine ⟨9682010475988404436884485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6454673650658936291256323 9682010475988404436884485)
                    ·
                      refine ⟨1815376964247825831915841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9682010475988404436884485 1815376964247825831915841)
                      ·
                        rfl

theorem cell23_3535434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_3535434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535434 prefixEnd_3535434 := by exact prefixLift 3535434
  have htrace : WordTrace (prefixWord ++ tailWord_3535434) baseStart_3535434 baseEnd_3535434 := by
    simpa [prefixWord, tailWord_3535434, baseEnd_3535434] using wordTrace_append hprefix tailTrace_3535434
  have hstable : (prefixWord ++ tailWord_3535434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535434).length < 2 ^ (prefixWord ++ tailWord_3535434).sum := by decide
  have hdescent : baseEnd_3535434 < baseStart_3535434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535444 : List Nat := [2, 4, 1, 1, 1, 3, 2, 1, 4, 4]
def baseStart_3535444 : Nat := 118140960795 + 3535444 * 2 ^ 59
def prefixEnd_3535444 : Nat := 4983230072969 + 3 ^ 40 * 3535444 * 2
def baseEnd_3535444 : Nat := 605127366351456930930265

theorem tailTrace_3535444 : CollatzResearch.WordTrace tailWord_3535444 prefixEnd_3535444 605127366351456930930265 := by
  unfold tailWord_3535444
  simp only [CollatzResearch.WordTrace]
  refine ⟨64474118101848834304438693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85965490802465112405918257 64474118101848834304438693)
  ·
    refine ⟨12088897144096656432082255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64474118101848834304438693 12088897144096656432082255)
    ·
      refine ⟨18133345716144984648123383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12088897144096656432082255 18133345716144984648123383)
      ·
        refine ⟨27200018574217476972185075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18133345716144984648123383 27200018574217476972185075)
        ·
          refine ⟨40800027861326215458277613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27200018574217476972185075 40800027861326215458277613)
          ·
            refine ⟨15300010447997330796854105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40800027861326215458277613 15300010447997330796854105)
            ·
              refine ⟨11475007835997998097640579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15300010447997330796854105 11475007835997998097640579)
              ·
                refine ⟨17212511753996997146460869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11475007835997998097640579 17212511753996997146460869)
                ·
                  refine ⟨3227345953874436964961413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17212511753996997146460869 3227345953874436964961413)
                  ·
                    refine ⟨605127366351456930930265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3227345953874436964961413 605127366351456930930265)
                    ·
                      rfl

theorem cell23_3535444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_3535444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535444 prefixEnd_3535444 := by exact prefixLift 3535444
  have htrace : WordTrace (prefixWord ++ tailWord_3535444) baseStart_3535444 baseEnd_3535444 := by
    simpa [prefixWord, tailWord_3535444, baseEnd_3535444] using wordTrace_append hprefix tailTrace_3535444
  have hstable : (prefixWord ++ tailWord_3535444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535444).length < 2 ^ (prefixWord ++ tailWord_3535444).sum := by decide
  have hdescent : baseEnd_3535444 < baseStart_3535444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535457 : List Nat := [1, 2, 3, 1, 1, 5, 2, 8]
def baseStart_3535457 : Nat := 118140960795 + 3535457 * 2 ^ 59
def prefixEnd_3535457 : Nat := 4983230072969 + 3 ^ 40 * 3535457 * 2
def baseEnd_3535457 : Nat := 67236621270477008960305

theorem tailTrace_3535457 : CollatzResearch.WordTrace tailWord_3535457 prefixEnd_3535457 67236621270477008960305 := by
  unfold tailWord_3535457
  simp only [CollatzResearch.WordTrace]
  refine ⟨128948710352650571829100625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85965806901767047886067083 128948710352650571829100625)
  ·
    refine ⟨96711532764487928871825469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128948710352650571829100625 96711532764487928871825469)
    ·
      refine ⟨36266824786682973326934551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96711532764487928871825469 36266824786682973326934551)
      ·
        refine ⟨54400237180024459990401827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36266824786682973326934551 54400237180024459990401827)
        ·
          refine ⟨81600355770036689985602741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54400237180024459990401827 81600355770036689985602741)
          ·
            refine ⟨7650033353440939686150257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81600355770036689985602741 7650033353440939686150257)
            ·
              refine ⟨5737525015080704764612693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7650033353440939686150257 5737525015080704764612693)
              ·
                refine ⟨67236621270477008960305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5737525015080704764612693 67236621270477008960305)
                ·
                  rfl

theorem cell23_3535457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 8].length) (baseStart_3535457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535457 prefixEnd_3535457 := by exact prefixLift 3535457
  have htrace : WordTrace (prefixWord ++ tailWord_3535457) baseStart_3535457 baseEnd_3535457 := by
    simpa [prefixWord, tailWord_3535457, baseEnd_3535457] using wordTrace_append hprefix tailTrace_3535457
  have hstable : (prefixWord ++ tailWord_3535457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535457).length < 2 ^ (prefixWord ++ tailWord_3535457).sum := by decide
  have hdescent : baseEnd_3535457 < baseStart_3535457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535461 : List Nat := [1, 3, 1, 3, 4, 1, 1, 3, 2, 4]
def baseStart_3535461 : Nat := 118140960795 + 3535461 * 2 ^ 59
def prefixEnd_3535461 : Nat := 4983230072969 + 3 ^ 40 * 3535461 * 2
def baseEnd_3535461 : Nat := 605130276075165742092739

theorem tailTrace_3535461 : CollatzResearch.WordTrace tailWord_3535461 prefixEnd_3535461 605130276075165742092739 := by
  unfold tailWord_3535461
  simp only [CollatzResearch.WordTrace]
  refine ⟨128948856244636080512246237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85965904163090720341497491 128948856244636080512246237)
  ·
    refine ⟨48355821091738530192092339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128948856244636080512246237 48355821091738530192092339)
    ·
      refine ⟨72533731637607795288138509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48355821091738530192092339 72533731637607795288138509)
      ·
        refine ⟨27200149364102923233051941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72533731637607795288138509 27200149364102923233051941)
        ·
          refine ⟨5100028005769298106197239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27200149364102923233051941 5100028005769298106197239)
          ·
            refine ⟨7650042008653947159295859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5100028005769298106197239 7650042008653947159295859)
            ·
              refine ⟨11475063012980920738943789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7650042008653947159295859 11475063012980920738943789)
              ·
                refine ⟨4303148629867845277103921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11475063012980920738943789 4303148629867845277103921)
                ·
                  refine ⟨3227361472400883957827941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4303148629867845277103921 3227361472400883957827941)
                  ·
                    refine ⟨605130276075165742092739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3227361472400883957827941 605130276075165742092739)
                    ·
                      rfl

theorem cell23_3535461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 2, 4].length) (baseStart_3535461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535461 prefixEnd_3535461 := by exact prefixLift 3535461
  have htrace : WordTrace (prefixWord ++ tailWord_3535461) baseStart_3535461 baseEnd_3535461 := by
    simpa [prefixWord, tailWord_3535461, baseEnd_3535461] using wordTrace_append hprefix tailTrace_3535461
  have hstable : (prefixWord ++ tailWord_3535461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535461).length < 2 ^ (prefixWord ++ tailWord_3535461).sum := by decide
  have hdescent : baseEnd_3535461 < baseStart_3535461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535484 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 6, 1, 3]
def baseStart_3535484 : Nat := 118140960795 + 3535484 * 2 ^ 59
def prefixEnd_3535484 : Nat := 4983230072969 + 3 ^ 40 * 3535484 * 2
def baseEnd_3535484 : Nat := 1815402638280550636290611

theorem tailTrace_3535484 : CollatzResearch.WordTrace tailWord_3535484 prefixEnd_3535484 1815402638280550636290611 := by
  unfold tailWord_3535484
  simp only [CollatzResearch.WordTrace]
  refine ⟨64474847561776377720166753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85966463415701836960222337 64474847561776377720166753)
  ·
    refine ⟨48356135671332283290125065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64474847561776377720166753 48356135671332283290125065)
    ·
      refine ⟨36267101753499212467593799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48356135671332283290125065 36267101753499212467593799)
      ·
        refine ⟨54400652630248818701390699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36267101753499212467593799 54400652630248818701390699)
        ·
          refine ⟨81600978945373228052086049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54400652630248818701390699 81600978945373228052086049)
          ·
            refine ⟨61200734209029921039064537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81600978945373228052086049 61200734209029921039064537)
            ·
              refine ⟨45900550656772440779298403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61200734209029921039064537 45900550656772440779298403)
              ·
                refine ⟨68850825985158661168947605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45900550656772440779298403 68850825985158661168947605)
                ·
                  refine ⟨3227382468054312242294419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 68850825985158661168947605 3227382468054312242294419)
                  ·
                    refine ⟨4841073702081468363441629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3227382468054312242294419 4841073702081468363441629)
                    ·
                      refine ⟨1815402638280550636290611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4841073702081468363441629 1815402638280550636290611)
                      ·
                        rfl

theorem cell23_3535484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_3535484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535484 prefixEnd_3535484 := by exact prefixLift 3535484
  have htrace : WordTrace (prefixWord ++ tailWord_3535484) baseStart_3535484 baseEnd_3535484 := by
    simpa [prefixWord, tailWord_3535484, baseEnd_3535484] using wordTrace_append hprefix tailTrace_3535484
  have hstable : (prefixWord ++ tailWord_3535484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535484).length < 2 ^ (prefixWord ++ tailWord_3535484).sum := by decide
  have hdescent : baseEnd_3535484 < baseStart_3535484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535517 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 1, 8]
def baseStart_3535517 : Nat := 118140960795 + 3535517 * 2 ^ 59
def prefixEnd_3535517 : Nat := 4983230072969 + 3 ^ 40 * 3535517 * 2
def baseEnd_3535517 : Nat := 605139861047383002392653

theorem tailTrace_3535517 : CollatzResearch.WordTrace tailWord_3535517 prefixEnd_3535517 605139861047383002392653 := by
  unfold tailWord_3535517
  simp only [CollatzResearch.WordTrace]
  refine ⟨128950898732433202076284805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85967265821622134717523203 128950898732433202076284805)
  ·
    refine ⟨24178293512331225389303401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128950898732433202076284805 24178293512331225389303401)
    ·
      refine ⟨18133720134248419041977551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24178293512331225389303401 18133720134248419041977551)
      ·
        refine ⟨27200580201372628562966327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18133720134248419041977551 27200580201372628562966327)
        ·
          refine ⟨40800870302058942844449491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27200580201372628562966327 40800870302058942844449491)
          ·
            refine ⟨61201305453088414266674237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40800870302058942844449491 61201305453088414266674237)
            ·
              refine ⟨22950489544908155350002839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61201305453088414266674237 22950489544908155350002839)
              ·
                refine ⟨34425734317362233025004259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22950489544908155350002839 34425734317362233025004259)
                ·
                  refine ⟨51638601476043349537506389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34425734317362233025004259 51638601476043349537506389)
                  ·
                    refine ⟨605139861047383002392653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51638601476043349537506389 605139861047383002392653)
                    ·
                      rfl

theorem cell23_3535517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_3535517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535517 prefixEnd_3535517 := by exact prefixLift 3535517
  have htrace : WordTrace (prefixWord ++ tailWord_3535517) baseStart_3535517 baseEnd_3535517 := by
    simpa [prefixWord, tailWord_3535517, baseEnd_3535517] using wordTrace_append hprefix tailTrace_3535517
  have hstable : (prefixWord ++ tailWord_3535517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535517).length < 2 ^ (prefixWord ++ tailWord_3535517).sum := by decide
  have hdescent : baseEnd_3535517 < baseStart_3535517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535518 : List Nat := [4, 3, 1, 1, 1, 1, 1, 5, 2, 1, 3]
def baseStart_3535518 : Nat := 118140960795 + 3535518 * 2 ^ 59
def prefixEnd_3535518 : Nat := 4983230072969 + 3 ^ 40 * 3535518 * 2
def baseEnd_3535518 : Nat := 1815420096622803503265455

theorem tailTrace_3535518 : CollatzResearch.WordTrace tailWord_3535518 prefixEnd_3535518 1815420096622803503265455 := by
  unfold tailWord_3535518
  simp only [CollatzResearch.WordTrace]
  refine ⟨16118866900678697405883901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85967290136953052831380805 16118866900678697405883901)
  ·
    refine ⟨6044575087754511527206463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16118866900678697405883901 6044575087754511527206463)
    ·
      refine ⟨9066862631631767290809695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6044575087754511527206463 9066862631631767290809695)
      ·
        refine ⟨13600293947447650936214543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9066862631631767290809695 13600293947447650936214543)
        ·
          refine ⟨20400440921171476404321815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13600293947447650936214543 20400440921171476404321815)
          ·
            refine ⟨30600661381757214606482723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20400440921171476404321815 30600661381757214606482723)
            ·
              refine ⟨45900992072635821909724085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30600661381757214606482723 45900992072635821909724085)
              ·
                refine ⟨4303218006809608304036633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45900992072635821909724085 4303218006809608304036633)
                ·
                  refine ⟨3227413505107206228027475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4303218006809608304036633 3227413505107206228027475)
                  ·
                    refine ⟨4841120257660809342041213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3227413505107206228027475 4841120257660809342041213)
                    ·
                      refine ⟨1815420096622803503265455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4841120257660809342041213 1815420096622803503265455)
                      ·
                        rfl

theorem cell23_3535518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_3535518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535518 prefixEnd_3535518 := by exact prefixLift 3535518
  have htrace : WordTrace (prefixWord ++ tailWord_3535518) baseStart_3535518 baseEnd_3535518 := by
    simpa [prefixWord, tailWord_3535518, baseEnd_3535518] using wordTrace_append hprefix tailTrace_3535518
  have hstable : (prefixWord ++ tailWord_3535518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535518).length < 2 ^ (prefixWord ++ tailWord_3535518).sum := by decide
  have hdescent : baseEnd_3535518 < baseStart_3535518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535564 : List Nat := [2, 2, 1, 5, 1, 1, 1, 3, 7]
def baseStart_3535564 : Nat := 118140960795 + 3535564 * 2 ^ 59
def prefixEnd_3535564 : Nat := 4983230072969 + 3 ^ 40 * 3535564 * 2
def baseEnd_3535564 : Nat := 201715968525878924810027

theorem tailTrace_3535564 : CollatzResearch.WordTrace tailWord_3535564 prefixEnd_3535564 201715968525878924810027 := by
  unfold tailWord_3535564
  simp only [CollatzResearch.WordTrace]
  refine ⟨64476306481631464551622873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85968408642175286068830497 64476306481631464551622873)
  ·
    refine ⟨48357229861223598413717155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64476306481631464551622873 48357229861223598413717155)
    ·
      refine ⟨72535844791835397620575733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48357229861223598413717155 72535844791835397620575733)
      ·
        refine ⟨6800235449234568526928975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72535844791835397620575733 6800235449234568526928975)
        ·
          refine ⟨10200353173851852790393463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6800235449234568526928975 10200353173851852790393463)
          ·
            refine ⟨15300529760777779185590195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10200353173851852790393463 15300529760777779185590195)
            ·
              refine ⟨22950794641166668778385293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15300529760777779185590195 22950794641166668778385293)
              ·
                refine ⟨8606547990437500791894485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22950794641166668778385293 8606547990437500791894485)
                ·
                  refine ⟨201715968525878924810027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8606547990437500791894485 201715968525878924810027)
                  ·
                    rfl

theorem cell23_3535564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 7].length) (baseStart_3535564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535564 prefixEnd_3535564 := by exact prefixLift 3535564
  have htrace : WordTrace (prefixWord ++ tailWord_3535564) baseStart_3535564 baseEnd_3535564 := by
    simpa [prefixWord, tailWord_3535564, baseEnd_3535564] using wordTrace_append hprefix tailTrace_3535564
  have hstable : (prefixWord ++ tailWord_3535564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535564).length < 2 ^ (prefixWord ++ tailWord_3535564).sum := by decide
  have hdescent : baseEnd_3535564 < baseStart_3535564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535575 : List Nat := [1, 1, 3, 2, 1, 5, 3, 1, 2, 2, 2]
def baseStart_3535575 : Nat := 118140960795 + 3535575 * 2 ^ 59
def prefixEnd_3535575 : Nat := 4983230072969 + 3 ^ 40 * 3535575 * 2
def baseEnd_3535575 : Nat := 1815449365020109780252693

theorem tailTrace_3535575 : CollatzResearch.WordTrace tailWord_3535575 prefixEnd_3535575 1815449365020109780252693 := by
  unfold tailWord_3535575
  simp only [CollatzResearch.WordTrace]
  refine ⟨128953014166223077981896179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85968676110815385321264119 128953014166223077981896179)
  ·
    refine ⟨193429521249334616972844269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128953014166223077981896179 193429521249334616972844269)
    ·
      refine ⟨72536070468500481364816601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193429521249334616972844269 72536070468500481364816601)
      ·
        refine ⟨54402052851375361023612451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72536070468500481364816601 54402052851375361023612451)
        ·
          refine ⟨81603079277063041535418677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54402052851375361023612451 81603079277063041535418677)
          ·
            refine ⟨7650288682224660143945501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81603079277063041535418677 7650288682224660143945501)
            ·
              refine ⟨2868858255834247553979563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7650288682224660143945501 2868858255834247553979563)
              ·
                refine ⟨4303287383751371330969345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2868858255834247553979563 4303287383751371330969345)
                ·
                  refine ⟨3227465537813528498227009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4303287383751371330969345 3227465537813528498227009)
                  ·
                    refine ⟨2420599153360146373670257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3227465537813528498227009 2420599153360146373670257)
                    ·
                      refine ⟨1815449365020109780252693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2420599153360146373670257 1815449365020109780252693)
                      ·
                        rfl

theorem cell23_3535575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 2, 2, 2].length) (baseStart_3535575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535575 prefixEnd_3535575 := by exact prefixLift 3535575
  have htrace : WordTrace (prefixWord ++ tailWord_3535575) baseStart_3535575 baseEnd_3535575 := by
    simpa [prefixWord, tailWord_3535575, baseEnd_3535575] using wordTrace_append hprefix tailTrace_3535575
  have hstable : (prefixWord ++ tailWord_3535575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535575).length < 2 ^ (prefixWord ++ tailWord_3535575).sum := by decide
  have hdescent : baseEnd_3535575 < baseStart_3535575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535577 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 3, 7]
def baseStart_3535577 : Nat := 118140960795 + 3535577 * 2 ^ 59
def prefixEnd_3535577 : Nat := 4983230072969 + 3 ^ 40 * 3535577 * 2
def baseEnd_3535577 : Nat := 605150130660472924142561

theorem tailTrace_3535577 : CollatzResearch.WordTrace tailWord_3535577 prefixEnd_3535577 605150130660472924142561 := by
  unfold tailWord_3535577
  simp only [CollatzResearch.WordTrace]
  refine ⟨128953087112215832323468985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85968724741477221548979323 128953087112215832323468985)
  ·
    refine ⟨96714815334161874242601739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128953087112215832323468985 96714815334161874242601739)
    ·
      refine ⟨145072223001242811363902609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96714815334161874242601739 145072223001242811363902609)
      ·
        refine ⟨108804167250932108522926957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145072223001242811363902609 108804167250932108522926957)
        ·
          refine ⟨40801562719099540696097609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108804167250932108522926957 40801562719099540696097609)
          ·
            refine ⟨30601172039324655522073207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40801562719099540696097609 30601172039324655522073207)
            ·
              refine ⟨45901758058986983283109811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30601172039324655522073207 45901758058986983283109811)
              ·
                refine ⟨68852637088480474924664717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45901758058986983283109811 68852637088480474924664717)
                ·
                  refine ⟨25819738908180178096749269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68852637088480474924664717 25819738908180178096749269)
                  ·
                    refine ⟨605150130660472924142561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25819738908180178096749269 605150130660472924142561)
                    ·
                      rfl

theorem cell23_3535577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 7].length) (baseStart_3535577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535577 prefixEnd_3535577 := by exact prefixLift 3535577
  have htrace : WordTrace (prefixWord ++ tailWord_3535577) baseStart_3535577 baseEnd_3535577 := by
    simpa [prefixWord, tailWord_3535577, baseEnd_3535577] using wordTrace_append hprefix tailTrace_3535577
  have hstable : (prefixWord ++ tailWord_3535577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535577).length < 2 ^ (prefixWord ++ tailWord_3535577).sum := by decide
  have hdescent : baseEnd_3535577 < baseStart_3535577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535594 : List Nat := [3, 1, 3, 1, 1, 1, 1, 5, 2, 5]
def baseStart_3535594 : Nat := 118140960795 + 3535594 * 2 ^ 59
def prefixEnd_3535594 : Nat := 4983230072969 + 3 ^ 40 * 3535594 * 2
def baseEnd_3535594 : Nat := 605153040384181735305035

theorem tailTrace_3535594 : CollatzResearch.WordTrace tailWord_3535594 prefixEnd_3535594 605153040384181735305035 := by
  unfold tailWord_3535594
  simp only [CollatzResearch.WordTrace]
  refine ⟨32238426788288561056709459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85969138102102829484558557 32238426788288561056709459)
  ·
    refine ⟨48357640182432841585064189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32238426788288561056709459 48357640182432841585064189)
    ·
      refine ⟨18134115068412315594399071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48357640182432841585064189 18134115068412315594399071)
      ·
        refine ⟨27201172602618473391598607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18134115068412315594399071 27201172602618473391598607)
        ·
          refine ⟨40801758903927710087397911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27201172602618473391598607 40801758903927710087397911)
          ·
            refine ⟨61202638355891565131096867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40801758903927710087397911 61202638355891565131096867)
            ·
              refine ⟨91803957533837347696645301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61202638355891565131096867 91803957533837347696645301)
              ·
                refine ⟨8606621018797251346560497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91803957533837347696645301 8606621018797251346560497)
                ·
                  refine ⟨6454965764097938509920373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8606621018797251346560497 6454965764097938509920373)
                  ·
                    refine ⟨605153040384181735305035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6454965764097938509920373 605153040384181735305035)
                    ·
                      rfl

theorem cell23_3535594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_3535594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535594 prefixEnd_3535594 := by exact prefixLift 3535594
  have htrace : WordTrace (prefixWord ++ tailWord_3535594) baseStart_3535594 baseEnd_3535594 := by
    simpa [prefixWord, tailWord_3535594, baseEnd_3535594] using wordTrace_append hprefix tailTrace_3535594
  have hstable : (prefixWord ++ tailWord_3535594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535594).length < 2 ^ (prefixWord ++ tailWord_3535594).sum := by decide
  have hdescent : baseEnd_3535594 < baseStart_3535594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535598 : List Nat := [4, 1, 2, 1, 1, 5, 1, 3, 5]
def baseStart_3535598 : Nat := 118140960795 + 3535598 * 2 ^ 59
def prefixEnd_3535598 : Nat := 4983230072969 + 3 ^ 40 * 3535598 * 2
def baseEnd_3535598 : Nat := 201717908341684798918343

theorem tailTrace_3535598 : CollatzResearch.WordTrace tailWord_3535598 prefixEnd_3535598 201717908341684798918343 := by
  unfold tailWord_3535598
  simp only [CollatzResearch.WordTrace]
  refine ⟨16119231630642469113747931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85969235363426501939988965 16119231630642469113747931)
  ·
    refine ⟨24178847445963703670621897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16119231630642469113747931 24178847445963703670621897)
    ·
      refine ⟨18134135584472777752966423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24178847445963703670621897 18134135584472777752966423)
      ·
        refine ⟨27201203376709166629449635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18134135584472777752966423 27201203376709166629449635)
        ·
          refine ⟨40801805065063749944174453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27201203376709166629449635 40801805065063749944174453)
          ·
            refine ⟨3825169224849726557266355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40801805065063749944174453 3825169224849726557266355)
            ·
              refine ⟨5737753837274589835899533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3825169224849726557266355 5737753837274589835899533)
              ·
                refine ⟨2151657688977971188462325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5737753837274589835899533 2151657688977971188462325)
                ·
                  refine ⟨201717908341684798918343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2151657688977971188462325 201717908341684798918343)
                  ·
                    rfl

theorem cell23_3535598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 3, 5].length) (baseStart_3535598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535598 prefixEnd_3535598 := by exact prefixLift 3535598
  have htrace : WordTrace (prefixWord ++ tailWord_3535598) baseStart_3535598 baseEnd_3535598 := by
    simpa [prefixWord, tailWord_3535598, baseEnd_3535598] using wordTrace_append hprefix tailTrace_3535598
  have hstable : (prefixWord ++ tailWord_3535598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535598).length < 2 ^ (prefixWord ++ tailWord_3535598).sum := by decide
  have hdescent : baseEnd_3535598 < baseStart_3535598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535698 : List Nat := [3, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3]
def baseStart_3535698 : Nat := 118140960795 + 3535698 * 2 ^ 59
def prefixEnd_3535698 : Nat := 4983230072969 + 3 ^ 40 * 3535698 * 2
def baseEnd_3535698 : Nat := 1815512523140612799014627

theorem tailTrace_3535698 : CollatzResearch.WordTrace tailWord_3535698 prefixEnd_3535698 1815512523140612799014627 := by
  unfold tailWord_3535698
  simp only [CollatzResearch.WordTrace]
  refine ⟨32239375086194367497155937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85971666896518313325749165 32239375086194367497155937)
  ·
    refine ⟨24179531314645775622866953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32239375086194367497155937 24179531314645775622866953)
    ·
      refine ⟨18134648485984331717150215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24179531314645775622866953 18134648485984331717150215)
      ·
        refine ⟨27201972728976497575725323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18134648485984331717150215 27201972728976497575725323)
        ·
          refine ⟨40802959093464746363587985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27201972728976497575725323 40802959093464746363587985)
          ·
            refine ⟨30602219320098559772690989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40802959093464746363587985 30602219320098559772690989)
            ·
              refine ⟨11475832245036959914759121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30602219320098559772690989 11475832245036959914759121)
              ·
                refine ⟨8606874183777719936069341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11475832245036959914759121 8606874183777719936069341)
                ·
                  refine ⟨3227577818916644976026003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8606874183777719936069341 3227577818916644976026003)
                  ·
                    refine ⟨4841366728374967464039005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3227577818916644976026003 4841366728374967464039005)
                    ·
                      refine ⟨1815512523140612799014627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4841366728374967464039005 1815512523140612799014627)
                      ·
                        rfl

theorem cell23_3535698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_3535698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535698 prefixEnd_3535698 := by exact prefixLift 3535698
  have htrace : WordTrace (prefixWord ++ tailWord_3535698) baseStart_3535698 baseEnd_3535698 := by
    simpa [prefixWord, tailWord_3535698, baseEnd_3535698] using wordTrace_append hprefix tailTrace_3535698
  have hstable : (prefixWord ++ tailWord_3535698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535698).length < 2 ^ (prefixWord ++ tailWord_3535698).sum := by decide
  have hdescent : baseEnd_3535698 < baseStart_3535698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535701 : List Nat := [1, 3, 2, 2, 2, 1, 2, 4, 1, 5]
def baseStart_3535701 : Nat := 118140960795 + 3535701 * 2 ^ 59
def prefixEnd_3535701 : Nat := 4983230072969 + 3 ^ 40 * 3535701 * 2
def baseEnd_3535701 : Nat := 605171354527525429092371

theorem tailTrace_3535701 : CollatzResearch.WordTrace tailWord_3535701 prefixEnd_3535701 605171354527525429092371 := by
  unfold tailWord_3535701
  simp only [CollatzResearch.WordTrace]
  refine ⟨128957609763766601500982957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85971739842511067667321971 128957609763766601500982957)
  ·
    refine ⟨48359103661412475562868609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128957609763766601500982957 48359103661412475562868609)
    ·
      refine ⟨36269327746059356672151457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48359103661412475562868609 36269327746059356672151457)
      ·
        refine ⟨27201995809544517504113593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36269327746059356672151457 27201995809544517504113593)
        ·
          refine ⟨20401496857158388128085195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27201995809544517504113593 20401496857158388128085195)
          ·
            refine ⟨30602245285737582192127793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20401496857158388128085195 30602245285737582192127793)
            ·
              refine ⟨22951683964303186644095845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30602245285737582192127793 22951683964303186644095845)
              ·
                refine ⟨4303440743306847495767971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22951683964303186644095845 4303440743306847495767971)
                ·
                  refine ⟨6455161114960271243651957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4303440743306847495767971 6455161114960271243651957)
                  ·
                    refine ⟨605171354527525429092371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6455161114960271243651957 605171354527525429092371)
                    ·
                      rfl

theorem cell23_3535701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_3535701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535701 prefixEnd_3535701 := by exact prefixLift 3535701
  have htrace : WordTrace (prefixWord ++ tailWord_3535701) baseStart_3535701 baseEnd_3535701 := by
    simpa [prefixWord, tailWord_3535701, baseEnd_3535701] using wordTrace_append hprefix tailTrace_3535701
  have hstable : (prefixWord ++ tailWord_3535701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535701).length < 2 ^ (prefixWord ++ tailWord_3535701).sum := by decide
  have hdescent : baseEnd_3535701 < baseStart_3535701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535715 : List Nat := [1, 1, 1, 5, 3, 1, 1, 5, 1, 1, 3]
def baseStart_3535715 : Nat := 118140960795 + 3535715 * 2 ^ 59
def prefixEnd_3535715 : Nat := 4983230072969 + 3 ^ 40 * 3535715 * 2
def baseEnd_3535715 : Nat := 1815521252311739232502049

theorem tailTrace_3535715 : CollatzResearch.WordTrace tailWord_3535715 prefixEnd_3535715 1815521252311739232502049 := by
  unfold tailWord_3535715
  simp only [CollatzResearch.WordTrace]
  refine ⟨128958120385715881891992599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85972080257143921261328399 128958120385715881891992599)
  ·
    refine ⟨193437180578573822837988899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128958120385715881891992599 193437180578573822837988899)
    ·
      refine ⟨290155770867860734256983349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193437180578573822837988899 290155770867860734256983349)
      ·
        refine ⟨27202103518861943836592189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 290155770867860734256983349 27202103518861943836592189)
        ·
          refine ⟨10200788819573228938722071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27202103518861943836592189 10200788819573228938722071)
          ·
            refine ⟨15301183229359843408083107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10200788819573228938722071 15301183229359843408083107)
            ·
              refine ⟨22951774844039765112124661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15301183229359843408083107 22951774844039765112124661)
              ·
                refine ⟨2151728891628727979261687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22951774844039765112124661 2151728891628727979261687)
                ·
                  refine ⟨3227593337443091968892531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2151728891628727979261687 3227593337443091968892531)
                  ·
                    refine ⟨4841390006164637953338797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3227593337443091968892531 4841390006164637953338797)
                    ·
                      refine ⟨1815521252311739232502049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4841390006164637953338797 1815521252311739232502049)
                      ·
                        rfl

theorem cell23_3535715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_3535715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535715 prefixEnd_3535715 := by exact prefixLift 3535715
  have htrace : WordTrace (prefixWord ++ tailWord_3535715) baseStart_3535715 baseEnd_3535715 := by
    simpa [prefixWord, tailWord_3535715, baseEnd_3535715] using wordTrace_append hprefix tailTrace_3535715
  have hstable : (prefixWord ++ tailWord_3535715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535715).length < 2 ^ (prefixWord ++ tailWord_3535715).sum := by decide
  have hdescent : baseEnd_3535715 < baseStart_3535715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535741 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 5, 2, 3]
def baseStart_3535741 : Nat := 118140960795 + 3535741 * 2 ^ 59
def prefixEnd_3535741 : Nat := 4983230072969 + 3 ^ 40 * 3535741 * 2
def baseEnd_3535741 : Nat := 1815534602808756130776929

theorem tailTrace_3535741 : CollatzResearch.WordTrace tailWord_3535741 prefixEnd_3535741 1815534602808756130776929 := by
  unfold tailWord_3535741
  simp only [CollatzResearch.WordTrace]
  refine ⟨128959068683621688332439077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85972712455747792221626051 128959068683621688332439077)
  ·
    refine ⟨24179825378179066562332327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128959068683621688332439077 24179825378179066562332327)
    ·
      refine ⟨36269738067268599843498491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24179825378179066562332327 36269738067268599843498491)
      ·
        refine ⟨54404607100902899765247737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36269738067268599843498491 54404607100902899765247737)
        ·
          refine ⟨40803455325677174823935803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54404607100902899765247737 40803455325677174823935803)
          ·
            refine ⟨61205182988515762235903705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40803455325677174823935803 61205182988515762235903705)
            ·
              refine ⟨45903887241386821676927779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61205182988515762235903705 45903887241386821676927779)
              ·
                refine ⟨68855830862080232515391669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45903887241386821676927779 68855830862080232515391669)
                ·
                  refine ⟨6455234143320021798317969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68855830862080232515391669 6455234143320021798317969)
                  ·
                    refine ⟨4841425607490016348738477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6455234143320021798317969 4841425607490016348738477)
                    ·
                      refine ⟨1815534602808756130776929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4841425607490016348738477 1815534602808756130776929)
                      ·
                        rfl

theorem cell23_3535741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_3535741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535741 prefixEnd_3535741 := by exact prefixLift 3535741
  have htrace : WordTrace (prefixWord ++ tailWord_3535741) baseStart_3535741 baseEnd_3535741 := by
    simpa [prefixWord, tailWord_3535741, baseEnd_3535741] using wordTrace_append hprefix tailTrace_3535741
  have hstable : (prefixWord ++ tailWord_3535741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535741).length < 2 ^ (prefixWord ++ tailWord_3535741).sum := by decide
  have hdescent : baseEnd_3535741 < baseStart_3535741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535751 : List Nat := [1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 6]
def baseStart_3535751 : Nat := 118140960795 + 3535751 * 2 ^ 59
def prefixEnd_3535751 : Nat := 4983230072969 + 3 ^ 40 * 3535751 * 2
def baseEnd_3535751 : Nat := 1815539737615301091651883

theorem tailTrace_3535751 : CollatzResearch.WordTrace tailWord_3535751 prefixEnd_3535751 1815539737615301091651883 := by
  unfold tailWord_3535751
  simp only [CollatzResearch.WordTrace]
  refine ⟨128959433413585460040303107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85972955609056973360202071 128959433413585460040303107)
  ·
    refine ⟨193439150120378190060454661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128959433413585460040303107 193439150120378190060454661)
    ·
      refine ⟨36269840647570910636335249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193439150120378190060454661 36269840647570910636335249)
      ·
        refine ⟨27202380485678182977251437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36269840647570910636335249 27202380485678182977251437)
        ·
          refine ⟨10200892682129318616469289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27202380485678182977251437 10200892682129318616469289)
          ·
            refine ⟨7650669511596988962351967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10200892682129318616469289 7650669511596988962351967)
            ·
              refine ⟨11476004267395483443527951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7650669511596988962351967 11476004267395483443527951)
              ·
                refine ⟨17214006401093225165291927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11476004267395483443527951 17214006401093225165291927)
                ·
                  refine ⟨25821009601639837747937891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17214006401093225165291927 25821009601639837747937891)
                  ·
                    refine ⟨38731514402459756621906837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25821009601639837747937891 38731514402459756621906837)
                    ·
                      refine ⟨1815539737615301091651883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38731514402459756621906837 1815539737615301091651883)
                      ·
                        rfl

theorem cell23_3535751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_3535751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535751 prefixEnd_3535751 := by exact prefixLift 3535751
  have htrace : WordTrace (prefixWord ++ tailWord_3535751) baseStart_3535751 baseEnd_3535751 := by
    simpa [prefixWord, tailWord_3535751, baseEnd_3535751] using wordTrace_append hprefix tailTrace_3535751
  have hstable : (prefixWord ++ tailWord_3535751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535751).length < 2 ^ (prefixWord ++ tailWord_3535751).sum := by decide
  have hdescent : baseEnd_3535751 < baseStart_3535751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535766 : List Nat := [5, 3, 1, 1, 1, 1, 3, 3, 1, 1, 3]
def baseStart_3535766 : Nat := 118140960795 + 3535766 * 2 ^ 59
def prefixEnd_3535766 : Nat := 4983230072969 + 3 ^ 40 * 3535766 * 2
def baseEnd_3535766 : Nat := 1815547439825118532964315

theorem tailTrace_3535766 : CollatzResearch.WordTrace tailWord_3535766 prefixEnd_3535766 1815547439825118532964315 := by
  unfold tailWord_3535766
  simp only [CollatzResearch.WordTrace]
  refine ⟨8059998781783194850131197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85973320339020745068066101 8059998781783194850131197)
  ·
    refine ⟨3022499543168698068799199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8059998781783194850131197 3022499543168698068799199)
    ·
      refine ⟨4533749314753047103198799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3022499543168698068799199 4533749314753047103198799)
      ·
        refine ⟨6800623972129570654798199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4533749314753047103198799 6800623972129570654798199)
        ·
          refine ⟨10200935958194355982197299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6800623972129570654798199 10200935958194355982197299)
          ·
            refine ⟨15301403937291533973295949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10200935958194355982197299 15301403937291533973295949)
            ·
              refine ⟨5738026476484325239985981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15301403937291533973295949 5738026476484325239985981)
              ·
                refine ⟨2151759928681621964994743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5738026476484325239985981 2151759928681621964994743)
                ·
                  refine ⟨3227639893022432947492115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2151759928681621964994743 3227639893022432947492115)
                  ·
                    refine ⟨4841459839533649421238173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3227639893022432947492115 4841459839533649421238173)
                    ·
                      refine ⟨1815547439825118532964315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4841459839533649421238173 1815547439825118532964315)
                      ·
                        rfl

theorem cell23_3535766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_3535766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535766 prefixEnd_3535766 := by exact prefixLift 3535766
  have htrace : WordTrace (prefixWord ++ tailWord_3535766) baseStart_3535766 baseEnd_3535766 := by
    simpa [prefixWord, tailWord_3535766, baseEnd_3535766] using wordTrace_append hprefix tailTrace_3535766
  have hstable : (prefixWord ++ tailWord_3535766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535766).length < 2 ^ (prefixWord ++ tailWord_3535766).sum := by decide
  have hdescent : baseEnd_3535766 < baseStart_3535766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535815 : List Nat := [1, 1, 4, 1, 1, 2, 5, 2, 1, 3, 2]
def baseStart_3535815 : Nat := 118140960795 + 3535815 * 2 ^ 59
def prefixEnd_3535815 : Nat := 4983230072969 + 3 ^ 40 * 3535815 * 2
def baseEnd_3535815 : Nat := 1815572600377188841251589

theorem tailTrace_3535815 : CollatzResearch.WordTrace tailWord_3535815 prefixEnd_3535815 1815572600377188841251589 := by
  unfold tailWord_3535815
  simp only [CollatzResearch.WordTrace]
  refine ⟨128961767685353598970632899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85974511790235732647088599 128961767685353598970632899)
  ·
    refine ⟨193442651528030398455949349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128961767685353598970632899 193442651528030398455949349)
    ·
      refine ⟨36270497161505699710490503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193442651528030398455949349 36270497161505699710490503)
      ·
        refine ⟨54405745742258549565735755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36270497161505699710490503 54405745742258549565735755)
        ·
          refine ⟨81608618613387824348603633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54405745742258549565735755 81608618613387824348603633)
          ·
            refine ⟨61206463960040868261452725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81608618613387824348603633 61206463960040868261452725)
            ·
              refine ⟨5738105996253831399511193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61206463960040868261452725 5738105996253831399511193)
              ·
                refine ⟨4303579497190373549633395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5738105996253831399511193 4303579497190373549633395)
                ·
                  refine ⟨6455369245785560324450093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4303579497190373549633395 6455369245785560324450093)
                  ·
                    refine ⟨2420763467169585121668785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6455369245785560324450093 2420763467169585121668785)
                    ·
                      refine ⟨1815572600377188841251589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2420763467169585121668785 1815572600377188841251589)
                      ·
                        rfl

theorem cell23_3535815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 3, 2].length) (baseStart_3535815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535815 prefixEnd_3535815 := by exact prefixLift 3535815
  have htrace : WordTrace (prefixWord ++ tailWord_3535815) baseStart_3535815 baseEnd_3535815 := by
    simpa [prefixWord, tailWord_3535815, baseEnd_3535815] using wordTrace_append hprefix tailTrace_3535815
  have hstable : (prefixWord ++ tailWord_3535815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535815).length < 2 ^ (prefixWord ++ tailWord_3535815).sum := by decide
  have hdescent : baseEnd_3535815 < baseStart_3535815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535832 : List Nat := [2, 1, 2, 2, 2, 4, 3, 1, 1, 3, 2]
def baseStart_3535832 : Nat := 118140960795 + 3535832 * 2 ^ 59
def prefixEnd_3535832 : Nat := 4983230072969 + 3 ^ 40 * 3535832 * 2
def baseEnd_3535832 : Nat := 1815581329548315274739011

theorem tailTrace_3535832 : CollatzResearch.WordTrace tailWord_3535832 prefixEnd_3535832 1815581329548315274739011 := by
  unfold tailWord_3535832
  simp only [CollatzResearch.WordTrace]
  refine ⟨64481193863146005437000875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85974925150861340582667833 64481193863146005437000875)
  ·
    refine ⟨96721790794719008155501313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64481193863146005437000875 96721790794719008155501313)
    ·
      refine ⟨72541343096039256116625985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96721790794719008155501313 72541343096039256116625985)
      ·
        refine ⟨54406007322029442087469489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72541343096039256116625985 54406007322029442087469489)
        ·
          refine ⟨40804505491522081565602117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54406007322029442087469489 40804505491522081565602117)
          ·
            refine ⟨7650844779660390293550397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40804505491522081565602117 7650844779660390293550397)
            ·
              refine ⟨2869066792372646360081399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7650844779660390293550397 2869066792372646360081399)
              ·
                refine ⟨4303600188558969540122099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2869066792372646360081399 4303600188558969540122099)
                ·
                  refine ⟨6455400282838454310183149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4303600188558969540122099 6455400282838454310183149)
                  ·
                    refine ⟨2420775106064420366318681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6455400282838454310183149 2420775106064420366318681)
                    ·
                      refine ⟨1815581329548315274739011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2420775106064420366318681 1815581329548315274739011)
                      ·
                        rfl

theorem cell23_3535832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 1, 3, 2].length) (baseStart_3535832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535832 prefixEnd_3535832 := by exact prefixLift 3535832
  have htrace : WordTrace (prefixWord ++ tailWord_3535832) baseStart_3535832 baseEnd_3535832 := by
    simpa [prefixWord, tailWord_3535832, baseEnd_3535832] using wordTrace_append hprefix tailTrace_3535832
  have hstable : (prefixWord ++ tailWord_3535832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535832).length < 2 ^ (prefixWord ++ tailWord_3535832).sum := by decide
  have hdescent : baseEnd_3535832 < baseStart_3535832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535841 : List Nat := [1, 2, 3, 1, 2, 1, 1, 4, 2, 2, 4]
def baseStart_3535841 : Nat := 118140960795 + 3535841 * 2 ^ 59
def prefixEnd_3535841 : Nat := 4983230072969 + 3 ^ 40 * 3535841 * 2
def baseEnd_3535841 : Nat := 1815585950874205739526469

theorem tailTrace_3535841 : CollatzResearch.WordTrace tailWord_3535841 prefixEnd_3535841 1815585950874205739526469 := by
  unfold tailWord_3535841
  simp only [CollatzResearch.WordTrace]
  refine ⟨128962715983259405411079377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85975143988839603607386251 128962715983259405411079377)
  ·
    refine ⟨96722036987444554058309533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128962715983259405411079377 96722036987444554058309533)
    ·
      refine ⟨36270763870291707771866075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96722036987444554058309533 36270763870291707771866075)
      ·
        refine ⟨54406145805437561657799113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36270763870291707771866075 54406145805437561657799113)
        ·
          refine ⟨40804609354078171243349335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54406145805437561657799113 40804609354078171243349335)
          ·
            refine ⟨61206914031117256865024003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40804609354078171243349335 61206914031117256865024003)
            ·
              refine ⟨91810371046675885297536005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61206914031117256865024003 91810371046675885297536005)
              ·
                refine ⟨17214444571251728493288001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91810371046675885297536005 17214444571251728493288001)
                ·
                  refine ⟨12910833428438796369966001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17214444571251728493288001 12910833428438796369966001)
                  ·
                    refine ⟨9683125071329097277474501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12910833428438796369966001 9683125071329097277474501)
                    ·
                      refine ⟨1815585950874205739526469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9683125071329097277474501 1815585950874205739526469)
                      ·
                        rfl

theorem cell23_3535841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_3535841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535841 prefixEnd_3535841 := by exact prefixLift 3535841
  have htrace : WordTrace (prefixWord ++ tailWord_3535841) baseStart_3535841 baseEnd_3535841 := by
    simpa [prefixWord, tailWord_3535841, baseEnd_3535841] using wordTrace_append hprefix tailTrace_3535841
  have hstable : (prefixWord ++ tailWord_3535841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535841).length < 2 ^ (prefixWord ++ tailWord_3535841).sum := by decide
  have hdescent : baseEnd_3535841 < baseStart_3535841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535862 : List Nat := [5, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2]
def baseStart_3535862 : Nat := 118140960795 + 3535862 * 2 ^ 59
def prefixEnd_3535862 : Nat := 4983230072969 + 3 ^ 40 * 3535862 * 2
def baseEnd_3535862 : Nat := 1815596733967950157363873

theorem tailTrace_3535862 : CollatzResearch.WordTrace tailWord_3535862 prefixEnd_3535862 1815596733967950157363873 := by
  unfold tailWord_3535862
  simp only [CollatzResearch.WordTrace]
  refine ⟨8060217619761457874849615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85975654610788883998395893 8060217619761457874849615)
  ·
    refine ⟨12090326429642186812274423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8060217619761457874849615 12090326429642186812274423)
    ·
      refine ⟨18135489644463280218411635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12090326429642186812274423 18135489644463280218411635)
      ·
        refine ⟨27203234466694920327617453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18135489644463280218411635 27203234466694920327617453)
        ·
          refine ⟨10201212925010595122856545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27203234466694920327617453 10201212925010595122856545)
          ·
            refine ⟨7650909693757946342142409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10201212925010595122856545 7650909693757946342142409)
            ·
              refine ⟨5738182270318459756606807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7650909693757946342142409 5738182270318459756606807)
              ·
                refine ⟨8607273405477689634910211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5738182270318459756606807 8607273405477689634910211)
                ·
                  refine ⟨12910910108216534452365317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8607273405477689634910211 12910910108216534452365317)
                  ·
                    refine ⟨2420795645290600209818497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12910910108216534452365317 2420795645290600209818497)
                    ·
                      refine ⟨1815596733967950157363873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2420795645290600209818497 1815596733967950157363873)
                      ·
                        rfl

theorem cell23_3535862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_3535862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535862 prefixEnd_3535862 := by exact prefixLift 3535862
  have htrace : WordTrace (prefixWord ++ tailWord_3535862) baseStart_3535862 baseEnd_3535862 := by
    simpa [prefixWord, tailWord_3535862, baseEnd_3535862] using wordTrace_append hprefix tailTrace_3535862
  have hstable : (prefixWord ++ tailWord_3535862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535862).length < 2 ^ (prefixWord ++ tailWord_3535862).sum := by decide
  have hdescent : baseEnd_3535862 < baseStart_3535862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535918 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_3535918 : Nat := 118140960795 + 3535918 * 2 ^ 59
def prefixEnd_3535918 : Nat := 4983230072969 + 3 ^ 40 * 3535918 * 2
def baseEnd_3535918 : Nat := 1815625488884601938263615

theorem tailTrace_3535918 : CollatzResearch.WordTrace tailWord_3535918 prefixEnd_3535918 1815625488884601938263615 := by
  unfold tailWord_3535918
  simp only [CollatzResearch.WordTrace]
  refine ⟨16120690550497555945204051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85977016269320298374421605 16120690550497555945204051)
  ·
    refine ⟨24181035825746333917806077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16120690550497555945204051 24181035825746333917806077)
    ·
      refine ⟨9067888434654875219177279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24181035825746333917806077 9067888434654875219177279)
      ·
        refine ⟨13601832651982312828765919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9067888434654875219177279 13601832651982312828765919)
        ·
          refine ⟨20402748977973469243148879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13601832651982312828765919 20402748977973469243148879)
          ·
            refine ⟨30604123466960203864723319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20402748977973469243148879 30604123466960203864723319)
            ·
              refine ⟨45906185200440305797084979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30604123466960203864723319 45906185200440305797084979)
              ·
                refine ⟨68859277800660458695627469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45906185200440305797084979 68859277800660458695627469)
                ·
                  refine ⟨25822229175247672010860301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68859277800660458695627469 25822229175247672010860301)
                  ·
                    refine ⟨9683335940717877004072613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25822229175247672010860301 9683335940717877004072613)
                    ·
                      refine ⟨1815625488884601938263615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9683335940717877004072613 1815625488884601938263615)
                      ·
                        rfl

theorem cell23_3535918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_3535918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535918 prefixEnd_3535918 := by exact prefixLift 3535918
  have htrace : WordTrace (prefixWord ++ tailWord_3535918) baseStart_3535918 baseEnd_3535918 := by
    simpa [prefixWord, tailWord_3535918, baseEnd_3535918] using wordTrace_append hprefix tailTrace_3535918
  have hstable : (prefixWord ++ tailWord_3535918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535918).length < 2 ^ (prefixWord ++ tailWord_3535918).sum := by decide
  have hdescent : baseEnd_3535918 < baseStart_3535918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535941 : List Nat := [1, 3, 1, 1, 1, 3, 3, 2, 8]
def baseStart_3535941 : Nat := 118140960795 + 3535941 * 2 ^ 59
def prefixEnd_3535941 : Nat := 4983230072969 + 3 ^ 40 * 3535941 * 2
def baseEnd_3535941 : Nat := 201737477659961705364001

theorem tailTrace_3535941 : CollatzResearch.WordTrace tailWord_3535941 prefixEnd_3535941 201737477659961705364001 := by
  unfold tailWord_3535941
  simp only [CollatzResearch.WordTrace]
  refine ⟨128966363282897122489719677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85977575521931414993146451 128966363282897122489719677)
  ·
    refine ⟨48362386231086420933644879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128966363282897122489719677 48362386231086420933644879)
    ·
      refine ⟨72543579346629631400467319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48362386231086420933644879 72543579346629631400467319)
      ·
        refine ⟨108815369019944447100700979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72543579346629631400467319 108815369019944447100700979)
        ·
          refine ⟨163223053529916670651051469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108815369019944447100700979 163223053529916670651051469)
          ·
            refine ⟨61208645073718751494144301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163223053529916670651051469 61208645073718751494144301)
            ·
              refine ⟨22953241902644531810304113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61208645073718751494144301 22953241902644531810304113)
              ·
                refine ⟨17214931426983398857728085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22953241902644531810304113 17214931426983398857728085)
                ·
                  refine ⟨201737477659961705364001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17214931426983398857728085 201737477659961705364001)
                  ·
                    rfl

theorem cell23_3535941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 8].length) (baseStart_3535941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535941 prefixEnd_3535941 := by exact prefixLift 3535941
  have htrace : WordTrace (prefixWord ++ tailWord_3535941) baseStart_3535941 baseEnd_3535941 := by
    simpa [prefixWord, tailWord_3535941, baseEnd_3535941] using wordTrace_append hprefix tailTrace_3535941
  have hstable : (prefixWord ++ tailWord_3535941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535941).length < 2 ^ (prefixWord ++ tailWord_3535941).sum := by decide
  have hdescent : baseEnd_3535941 < baseStart_3535941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535945 : List Nat := [1, 2, 1, 1, 2, 2, 2, 7, 1, 4]
def baseStart_3535945 : Nat := 118140960795 + 3535945 * 2 ^ 59
def prefixEnd_3535945 : Nat := 4983230072969 + 3 ^ 40 * 3535945 * 2
def baseEnd_3535945 : Nat := 605213117620757777541997

theorem tailTrace_3535945 : CollatzResearch.WordTrace tailWord_3535945 prefixEnd_3535945 605213117620757777541997 := by
  unfold tailWord_3535945
  simp only [CollatzResearch.WordTrace]
  refine ⟨128966509174882631172865289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85977672783255087448576859 128966509174882631172865289)
  ·
    refine ⟨96724881881161973379648967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128966509174882631172865289 96724881881161973379648967)
    ·
      refine ⟨145087322821742960069473451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96724881881161973379648967 145087322821742960069473451)
      ·
        refine ⟨217630984232614440104210177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145087322821742960069473451 217630984232614440104210177)
        ·
          refine ⟨163223238174460830078157633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217630984232614440104210177 163223238174460830078157633)
          ·
            refine ⟨122417428630845622558618225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163223238174460830078157633 122417428630845622558618225)
            ·
              refine ⟨91813071473134216918963669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122417428630845622558618225 91813071473134216918963669)
              ·
                refine ⟨2151868862651583209038211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 91813071473134216918963669 2151868862651583209038211)
                ·
                  refine ⟨3227803293977374813557317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2151868862651583209038211 3227803293977374813557317)
                  ·
                    refine ⟨605213117620757777541997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3227803293977374813557317 605213117620757777541997)
                    ·
                      rfl

theorem cell23_3535945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 7, 1, 4].length) (baseStart_3535945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535945 prefixEnd_3535945 := by exact prefixLift 3535945
  have htrace : WordTrace (prefixWord ++ tailWord_3535945) baseStart_3535945 baseEnd_3535945 := by
    simpa [prefixWord, tailWord_3535945, baseEnd_3535945] using wordTrace_append hprefix tailTrace_3535945
  have hstable : (prefixWord ++ tailWord_3535945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535945).length < 2 ^ (prefixWord ++ tailWord_3535945).sum := by decide
  have hdescent : baseEnd_3535945 < baseStart_3535945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535961 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 1, 2, 6]
def baseStart_3535961 : Nat := 118140960795 + 3535961 * 2 ^ 59
def prefixEnd_3535961 : Nat := 4983230072969 + 3 ^ 40 * 3535961 * 2
def baseEnd_3535961 : Nat := 1815647568552745270025917

theorem tailTrace_3535961 : CollatzResearch.WordTrace tailWord_3535961 prefixEnd_3535961 1815647568552745270025917 := by
  unfold tailWord_3535961
  simp only [CollatzResearch.WordTrace]
  refine ⟨128967092742824665905447737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85978061828549777270298491 128967092742824665905447737)
  ·
    refine ⟨96725319557118499429085803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128967092742824665905447737 96725319557118499429085803)
    ·
      refine ⟨145087979335677749143628705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96725319557118499429085803 145087979335677749143628705)
      ·
        refine ⟨108815984501758311857721529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145087979335677749143628705 108815984501758311857721529)
        ·
          refine ⟨81611988376318733893291147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108815984501758311857721529 81611988376318733893291147)
          ·
            refine ⟨122417982564478100839936721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81611988376318733893291147 122417982564478100839936721)
            ·
              refine ⟨91813486923358575629952541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122417982564478100839936721 91813486923358575629952541)
              ·
                refine ⟨34430057596259465861232203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91813486923358575629952541 34430057596259465861232203)
                ·
                  refine ⟨51645086394389198791848305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34430057596259465861232203 51645086394389198791848305)
                  ·
                    refine ⟨38733814795791899093886229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51645086394389198791848305 38733814795791899093886229)
                    ·
                      refine ⟨1815647568552745270025917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38733814795791899093886229 1815647568552745270025917)
                      ·
                        rfl

theorem cell23_3535961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_3535961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535961 prefixEnd_3535961 := by exact prefixLift 3535961
  have htrace : WordTrace (prefixWord ++ tailWord_3535961) baseStart_3535961 baseEnd_3535961 := by
    simpa [prefixWord, tailWord_3535961, baseEnd_3535961] using wordTrace_append hprefix tailTrace_3535961
  have hstable : (prefixWord ++ tailWord_3535961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535961).length < 2 ^ (prefixWord ++ tailWord_3535961).sum := by decide
  have hdescent : baseEnd_3535961 < baseStart_3535961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535971 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 2, 9]
def baseStart_3535971 : Nat := 118140960795 + 3535971 * 2 ^ 59
def prefixEnd_3535971 : Nat := 4983230072969 + 3 ^ 40 * 3535971 * 2
def baseEnd_3535971 : Nat := 605217567786430076966957

theorem tailTrace_3535971 : CollatzResearch.WordTrace tailWord_3535971 prefixEnd_3535971 605217567786430076966957 := by
  unfold tailWord_3535971
  simp only [CollatzResearch.WordTrace]
  refine ⟨128967457472788437613311767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85978304981858958408874511 128967457472788437613311767)
  ·
    refine ⟨193451186209182656419967651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128967457472788437613311767 193451186209182656419967651)
    ·
      refine ⟨290176779313773984629951477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193451186209182656419967651 290176779313773984629951477)
      ·
        refine ⟨27204073060666311059057951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 290176779313773984629951477 27204073060666311059057951)
        ·
          refine ⟨40806109590999466588586927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27204073060666311059057951 40806109590999466588586927)
          ·
            refine ⟨61209164386499199882880391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40806109590999466588586927 61209164386499199882880391)
            ·
              refine ⟨91813746579748799824320587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61209164386499199882880391 91813746579748799824320587)
              ·
                refine ⟨137720619869623199736480881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91813746579748799824320587 137720619869623199736480881)
                ·
                  refine ⟨103290464902217399802360661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137720619869623199736480881 103290464902217399802360661)
                  ·
                    refine ⟨605217567786430076966957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 103290464902217399802360661 605217567786430076966957)
                    ·
                      rfl

theorem cell23_3535971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 9].length) (baseStart_3535971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535971 prefixEnd_3535971 := by exact prefixLift 3535971
  have htrace : WordTrace (prefixWord ++ tailWord_3535971) baseStart_3535971 baseEnd_3535971 := by
    simpa [prefixWord, tailWord_3535971, baseEnd_3535971] using wordTrace_append hprefix tailTrace_3535971
  have hstable : (prefixWord ++ tailWord_3535971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535971).length < 2 ^ (prefixWord ++ tailWord_3535971).sum := by decide
  have hdescent : baseEnd_3535971 < baseStart_3535971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535975 : List Nat := [1, 1, 5, 1, 1, 3, 4, 1, 6]
def baseStart_3535975 : Nat := 118140960795 + 3535975 * 2 ^ 59
def prefixEnd_3535975 : Nat := 4983230072969 + 3 ^ 40 * 3535975 * 2
def baseEnd_3535975 : Nat := 201739417475767579472317

theorem tailTrace_3535975 : CollatzResearch.WordTrace tailWord_3535975 prefixEnd_3535975 201739417475767579472317 := by
  unfold tailWord_3535975
  simp only [CollatzResearch.WordTrace]
  refine ⟨128967603364773946296457379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85978402243182630864304919 128967603364773946296457379)
  ·
    refine ⟨193451405047160919444686069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128967603364773946296457379 193451405047160919444686069)
    ·
      refine ⟨18136069223171336197939319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 193451405047160919444686069 18136069223171336197939319)
      ·
        refine ⟨27204103834757004296908979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18136069223171336197939319 27204103834757004296908979)
        ·
          refine ⟨40806155752135506445363469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27204103834757004296908979 40806155752135506445363469)
          ·
            refine ⟨15302308407050814917011301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40806155752135506445363469 15302308407050814917011301)
            ·
              refine ⟨2869182826322027796939619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15302308407050814917011301 2869182826322027796939619)
              ·
                refine ⟨4303774239483041695409429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2869182826322027796939619 4303774239483041695409429)
                ·
                  refine ⟨201739417475767579472317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4303774239483041695409429 201739417475767579472317)
                  ·
                    rfl

theorem cell23_3535975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 6].length) (baseStart_3535975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535975 prefixEnd_3535975 := by exact prefixLift 3535975
  have htrace : WordTrace (prefixWord ++ tailWord_3535975) baseStart_3535975 baseEnd_3535975 := by
    simpa [prefixWord, tailWord_3535975, baseEnd_3535975] using wordTrace_append hprefix tailTrace_3535975
  have hstable : (prefixWord ++ tailWord_3535975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535975).length < 2 ^ (prefixWord ++ tailWord_3535975).sum := by decide
  have hdescent : baseEnd_3535975 < baseStart_3535975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535989 : List Nat := [1, 3, 4, 3, 1, 1, 2, 1, 2, 2, 3]
def baseStart_3535989 : Nat := 118140960795 + 3535989 * 2 ^ 59
def prefixEnd_3535989 : Nat := 4983230072969 + 3 ^ 40 * 3535989 * 2
def baseEnd_3535989 : Nat := 1815661946011071160475789

theorem tailTrace_3535989 : CollatzResearch.WordTrace tailWord_3535989 prefixEnd_3535989 1815661946011071160475789 := by
  unfold tailWord_3535989
  simp only [CollatzResearch.WordTrace]
  refine ⟨128968113986723226687467021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85978742657815484458311347 128968113986723226687467021)
  ·
    refine ⟨48363042745021210007800133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128968113986723226687467021 48363042745021210007800133)
    ·
      refine ⟨9068070514691476876462525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48363042745021210007800133 9068070514691476876462525)
      ·
        refine ⟨3400526443009303828673447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9068070514691476876462525 3400526443009303828673447)
        ·
          refine ⟨5100789664513955743010171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3400526443009303828673447 5100789664513955743010171)
          ·
            refine ⟨7651184496770933614515257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5100789664513955743010171 7651184496770933614515257)
            ·
              refine ⟨5738388372578200210886443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7651184496770933614515257 5738388372578200210886443)
              ·
                refine ⟨8607582558867300316329665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5738388372578200210886443 8607582558867300316329665)
                ·
                  refine ⟨6455686919150475237247249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8607582558867300316329665 6455686919150475237247249)
                  ·
                    refine ⟨4841765189362856427935437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6455686919150475237247249 4841765189362856427935437)
                    ·
                      refine ⟨1815661946011071160475789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4841765189362856427935437 1815661946011071160475789)
                      ·
                        rfl

theorem cell23_3535989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_3535989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535989 prefixEnd_3535989 := by exact prefixLift 3535989
  have htrace : WordTrace (prefixWord ++ tailWord_3535989) baseStart_3535989 baseEnd_3535989 := by
    simpa [prefixWord, tailWord_3535989, baseEnd_3535989] using wordTrace_append hprefix tailTrace_3535989
  have hstable : (prefixWord ++ tailWord_3535989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535989).length < 2 ^ (prefixWord ++ tailWord_3535989).sum := by decide
  have hdescent : baseEnd_3535989 < baseStart_3535989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536019 : List Nat := [1, 1, 1, 2, 1, 2, 8, 2, 1, 1, 3]
def baseStart_3536019 : Nat := 118140960795 + 3536019 * 2 ^ 59
def prefixEnd_3536019 : Nat := 4983230072969 + 3 ^ 40 * 3536019 * 2
def baseEnd_3536019 : Nat := 1815677350430706043100651

theorem tailTrace_3536019 : CollatzResearch.WordTrace tailWord_3536019 prefixEnd_3536019 1815677350430706043100651 := by
  unfold tailWord_3536019
  simp only [CollatzResearch.WordTrace]
  refine ⟨128969208176614541811059111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85979472117743027874039407 128969208176614541811059111)
  ·
    refine ⟨193453812264921812716588667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128969208176614541811059111 193453812264921812716588667)
    ·
      refine ⟨290180718397382719074883001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193453812264921812716588667 290180718397382719074883001)
      ·
        refine ⟨217635538798037039306162251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290180718397382719074883001 217635538798037039306162251)
        ·
          refine ⟨326453308197055558959243377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217635538798037039306162251 326453308197055558959243377)
          ·
            refine ⟨244839981147791669219432533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326453308197055558959243377 244839981147791669219432533)
            ·
              refine ⟨2869218529075683623665225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 244839981147791669219432533 2869218529075683623665225)
              ·
                refine ⟨2151913896806762717748919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2869218529075683623665225 2151913896806762717748919)
                ·
                  refine ⟨3227870845210144076623379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2151913896806762717748919 3227870845210144076623379)
                  ·
                    refine ⟨4841806267815216114935069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3227870845210144076623379 4841806267815216114935069)
                    ·
                      refine ⟨1815677350430706043100651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4841806267815216114935069 1815677350430706043100651)
                      ·
                        rfl

theorem cell23_3536019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 2, 1, 1, 3].length) (baseStart_3536019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536019 prefixEnd_3536019 := by exact prefixLift 3536019
  have htrace : WordTrace (prefixWord ++ tailWord_3536019) baseStart_3536019 baseEnd_3536019 := by
    simpa [prefixWord, tailWord_3536019, baseEnd_3536019] using wordTrace_append hprefix tailTrace_3536019
  have hstable : (prefixWord ++ tailWord_3536019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536019).length < 2 ^ (prefixWord ++ tailWord_3536019).sum := by decide
  have hdescent : baseEnd_3536019 < baseStart_3536019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536042 : List Nat := [3, 1, 5, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_3536042 : Nat := 118140960795 + 3536042 * 2 ^ 59
def prefixEnd_3536042 : Nat := 4983230072969 + 3 ^ 40 * 3536042 * 2
def baseEnd_3536042 : Nat := 1815689160485759453113045

theorem tailTrace_3536042 : CollatzResearch.WordTrace tailWord_3536042 prefixEnd_3536042 1815689160485759453113045 := by
  unfold tailWord_3536042
  simp only [CollatzResearch.WordTrace]
  refine ⟨32242511763882804184786595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85980031370354144492764253 32242511763882804184786595)
  ·
    refine ⟨48363767645824206277179893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32242511763882804184786595 48363767645824206277179893)
    ·
      refine ⟨4534103216796019338485615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48363767645824206277179893 4534103216796019338485615)
      ·
        refine ⟨6801154825194029007728423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4534103216796019338485615 6801154825194029007728423)
        ·
          refine ⟨10201732237791043511592635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6801154825194029007728423 10201732237791043511592635)
          ·
            refine ⟨15302598356686565267388953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10201732237791043511592635 15302598356686565267388953)
            ·
              refine ⟨11476948767514923950541715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15302598356686565267388953 11476948767514923950541715)
              ·
                refine ⟨17215423151272385925812573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11476948767514923950541715 17215423151272385925812573)
                ·
                  refine ⟨6455783681727144722179715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17215423151272385925812573 6455783681727144722179715)
                  ·
                    refine ⟨9683675522590717083269573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6455783681727144722179715 9683675522590717083269573)
                    ·
                      refine ⟨1815689160485759453113045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9683675522590717083269573 1815689160485759453113045)
                      ·
                        rfl

theorem cell23_3536042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_3536042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536042 prefixEnd_3536042 := by exact prefixLift 3536042
  have htrace : WordTrace (prefixWord ++ tailWord_3536042) baseStart_3536042 baseEnd_3536042 := by
    simpa [prefixWord, tailWord_3536042, baseEnd_3536042] using wordTrace_append hprefix tailTrace_3536042
  have hstable : (prefixWord ++ tailWord_3536042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536042).length < 2 ^ (prefixWord ++ tailWord_3536042).sum := by decide
  have hdescent : baseEnd_3536042 < baseStart_3536042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536065 : List Nat := [1, 2, 6, 1, 1, 2, 10]
def baseStart_3536065 : Nat := 118140960795 + 3536065 * 2 ^ 59
def prefixEnd_3536065 : Nat := 4983230072969 + 3 ^ 40 * 3536065 * 2
def baseEnd_3536065 : Nat := 22416061364701393371919

theorem tailTrace_3536065 : CollatzResearch.WordTrace tailWord_3536065 prefixEnd_3536065 22416061364701393371919 := by
  unfold tailWord_3536065
  simp only [CollatzResearch.WordTrace]
  refine ⟨128970885934447891667233649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85980590622965261111489099 128970885934447891667233649)
  ·
    refine ⟨96728164450835918750425237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128970885934447891667233649 96728164450835918750425237)
    ·
      refine ⟨4534132708632933691426183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 96728164450835918750425237 4534132708632933691426183)
      ·
        refine ⟨6801199062949400537139275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4534132708632933691426183 6801199062949400537139275)
        ·
          refine ⟨10201798594424100805708913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6801199062949400537139275 10201798594424100805708913)
          ·
            refine ⟨7651348945818075604281685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10201798594424100805708913 7651348945818075604281685)
            ·
              refine ⟨22416061364701393371919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7651348945818075604281685 22416061364701393371919)
              ·
                rfl

theorem cell23_3536065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 10].length) (baseStart_3536065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536065 prefixEnd_3536065 := by exact prefixLift 3536065
  have htrace : WordTrace (prefixWord ++ tailWord_3536065) baseStart_3536065 baseEnd_3536065 := by
    simpa [prefixWord, tailWord_3536065, baseEnd_3536065] using wordTrace_append hprefix tailTrace_3536065
  have hstable : (prefixWord ++ tailWord_3536065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536065).length < 2 ^ (prefixWord ++ tailWord_3536065).sum := by decide
  have hdescent : baseEnd_3536065 < baseStart_3536065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536086 : List Nat := [5, 2, 1, 2, 3, 1, 1, 1, 1, 6]
def baseStart_3536086 : Nat := 118140960795 + 3536086 * 2 ^ 59
def prefixEnd_3536086 : Nat := 4983230072969 + 3 ^ 40 * 3536086 * 2
def baseEnd_3536086 : Nat := 605237251211519093654281

theorem tailTrace_3536086 : CollatzResearch.WordTrace tailWord_3536086 prefixEnd_3536086 605237251211519093654281 := by
  unfold tailWord_3536086
  simp only [CollatzResearch.WordTrace]
  refine ⟨8060728241710738265859257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85981101244914541502498741 8060728241710738265859257)
  ·
    refine ⟨6045546181283053699394443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8060728241710738265859257 6045546181283053699394443)
    ·
      refine ⟨9068319271924580549091665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6045546181283053699394443 9068319271924580549091665)
      ·
        refine ⟨6801239453943435411818749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9068319271924580549091665 6801239453943435411818749)
        ·
          refine ⟨2550464795228788279432031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6801239453943435411818749 2550464795228788279432031)
          ·
            refine ⟨3825697192843182419148047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2550464795228788279432031 3825697192843182419148047)
            ·
              refine ⟨5738545789264773628722071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3825697192843182419148047 5738545789264773628722071)
              ·
                refine ⟨8607818683897160443083107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5738545789264773628722071 8607818683897160443083107)
                ·
                  refine ⟨12911728025845740664624661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8607818683897160443083107 12911728025845740664624661)
                  ·
                    refine ⟨605237251211519093654281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12911728025845740664624661 605237251211519093654281)
                    ·
                      rfl

theorem cell23_3536086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_3536086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536086 prefixEnd_3536086 := by exact prefixLift 3536086
  have htrace : WordTrace (prefixWord ++ tailWord_3536086) baseStart_3536086 baseEnd_3536086 := by
    simpa [prefixWord, tailWord_3536086, baseEnd_3536086] using wordTrace_append hprefix tailTrace_3536086
  have hstable : (prefixWord ++ tailWord_3536086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536086).length < 2 ^ (prefixWord ++ tailWord_3536086).sum := by decide
  have hdescent : baseEnd_3536086 < baseStart_3536086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536116 : List Nat := [2, 6, 1, 2, 2, 1, 9]
def baseStart_3536116 : Nat := 118140960795 + 3536116 * 2 ^ 59
def prefixEnd_3536116 : Nat := 4983230072969 + 3 ^ 40 * 3536116 * 2
def baseEnd_3536116 : Nat := 22416384667335705723305

theorem tailTrace_3536116 : CollatzResearch.WordTrace tailWord_3536116 prefixEnd_3536116 22416384667335705723305 := by
  unfold tailWord_3536116
  simp only [CollatzResearch.WordTrace]
  refine ⟨64486373028631563688670101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85981830704842084918226801 64486373028631563688670101)
  ·
    refine ⟨3022798735717104547906411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 64486373028631563688670101 3022798735717104547906411)
    ·
      refine ⟨4534198103575656821859617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3022798735717104547906411 4534198103575656821859617)
      ·
        refine ⟨3400648577681742616394713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4534198103575656821859617 3400648577681742616394713)
        ·
          refine ⟨2550486433261306962296035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3400648577681742616394713 2550486433261306962296035)
          ·
            refine ⟨3825729649891960443444053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2550486433261306962296035 3825729649891960443444053)
            ·
              refine ⟨22416384667335705723305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3825729649891960443444053 22416384667335705723305)
              ·
                rfl

theorem cell23_3536116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 9].length) (baseStart_3536116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536116 prefixEnd_3536116 := by exact prefixLift 3536116
  have htrace : WordTrace (prefixWord ++ tailWord_3536116) baseStart_3536116 baseEnd_3536116 := by
    simpa [prefixWord, tailWord_3536116, baseEnd_3536116] using wordTrace_append hprefix tailTrace_3536116
  have hstable : (prefixWord ++ tailWord_3536116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536116).length < 2 ^ (prefixWord ++ tailWord_3536116).sum := by decide
  have hdescent : baseEnd_3536116 < baseStart_3536116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536242 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 4, 2, 3]
def baseStart_3536242 : Nat := 118140960795 + 3536242 * 2 ^ 59
def prefixEnd_3536242 : Nat := 4983230072969 + 3 ^ 40 * 3536242 * 2
def baseEnd_3536242 : Nat := 1815791856616658670612125

theorem tailTrace_3536242 : CollatzResearch.WordTrace tailWord_3536242 prefixEnd_3536242 1815791856616658670612125 := by
  unfold tailWord_3536242
  simp only [CollatzResearch.WordTrace]
  refine ⟨32244335413701662724106745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85984894436537767264284653 32244335413701662724106745)
  ·
    refine ⟨24183251560276247043080059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32244335413701662724106745 24183251560276247043080059)
    ·
      refine ⟨36274877340414370564620089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24183251560276247043080059 36274877340414370564620089)
      ·
        refine ⟨27206158005310777923465067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36274877340414370564620089 27206158005310777923465067)
        ·
          refine ⟨40809237007966166885197601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27206158005310777923465067 40809237007966166885197601)
          ·
            refine ⟨30606927755974625163898201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40809237007966166885197601 30606927755974625163898201)
            ·
              refine ⟨22955195816980968872923651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30606927755974625163898201 22955195816980968872923651)
              ·
                refine ⟨34432793725471453309385477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22955195816980968872923651 34432793725471453309385477)
                ·
                  refine ⟨6456148823525897495509777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34432793725471453309385477 6456148823525897495509777)
                  ·
                    refine ⟨4842111617644423121632333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6456148823525897495509777 4842111617644423121632333)
                    ·
                      refine ⟨1815791856616658670612125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4842111617644423121632333 1815791856616658670612125)
                      ·
                        rfl

theorem cell23_3536242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_3536242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536242 prefixEnd_3536242 := by exact prefixLift 3536242
  have htrace : WordTrace (prefixWord ++ tailWord_3536242) baseStart_3536242 baseEnd_3536242 := by
    simpa [prefixWord, tailWord_3536242, baseEnd_3536242] using wordTrace_append hprefix tailTrace_3536242
  have hstable : (prefixWord ++ tailWord_3536242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536242).length < 2 ^ (prefixWord ++ tailWord_3536242).sum := by decide
  have hdescent : baseEnd_3536242 < baseStart_3536242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536249 : List Nat := [1, 2, 1, 3, 2, 1, 4, 4, 1, 4]
def baseStart_3536249 : Nat := 118140960795 + 3536249 * 2 ^ 59
def prefixEnd_3536249 : Nat := 4983230072969 + 3 ^ 40 * 3536249 * 2
def baseEnd_3536249 : Nat := 605265150327080047741531

theorem tailTrace_3536249 : CollatzResearch.WordTrace tailWord_3536249 prefixEnd_3536249 605265150327080047741531 := by
  unfold tailWord_3536249
  simp only [CollatzResearch.WordTrace]
  refine ⟨128977596965781291091931801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85985064643854194061287867 128977596965781291091931801)
  ·
    refine ⟨96733197724335968318948851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128977596965781291091931801 96733197724335968318948851)
    ·
      refine ⟨145099796586503952478423277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96733197724335968318948851 145099796586503952478423277)
      ·
        refine ⟨54412423719938982179408729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145099796586503952478423277 54412423719938982179408729)
        ·
          refine ⟨40809317789954236634556547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54412423719938982179408729 40809317789954236634556547)
          ·
            refine ⟨61213976684931354951834821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40809317789954236634556547 61213976684931354951834821)
            ·
              refine ⟨11477620628424629053469029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61213976684931354951834821 11477620628424629053469029)
              ·
                refine ⟨2152053867829617947525443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11477620628424629053469029 2152053867829617947525443)
                ·
                  refine ⟨3228080801744426921288165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2152053867829617947525443 3228080801744426921288165)
                  ·
                    refine ⟨605265150327080047741531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3228080801744426921288165 605265150327080047741531)
                    ·
                      rfl

theorem cell23_3536249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 4, 1, 4].length) (baseStart_3536249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536249 prefixEnd_3536249 := by exact prefixLift 3536249
  have htrace : WordTrace (prefixWord ++ tailWord_3536249) baseStart_3536249 baseEnd_3536249 := by
    simpa [prefixWord, tailWord_3536249, baseEnd_3536249] using wordTrace_append hprefix tailTrace_3536249
  have hstable : (prefixWord ++ tailWord_3536249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536249).length < 2 ^ (prefixWord ++ tailWord_3536249).sum := by decide
  have hdescent : baseEnd_3536249 < baseStart_3536249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536255 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 4, 5, 3]
def baseStart_3536255 : Nat := 118140960795 + 3536255 * 2 ^ 59
def prefixEnd_3536255 : Nat := 4983230072969 + 3 ^ 40 * 3536255 * 2
def baseEnd_3536255 : Nat := 1815798531865167119749565

theorem tailTrace_3536255 : CollatzResearch.WordTrace tailWord_3536255 prefixEnd_3536255 1815798531865167119749565 := by
  unfold tailWord_3536255
  simp only [CollatzResearch.WordTrace]
  refine ⟨128977815803759554116650219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85985210535839702744433479 128977815803759554116650219)
  ·
    refine ⟨193466723705639331174975329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128977815803759554116650219 193466723705639331174975329)
    ·
      refine ⟨145100042779229498381231497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193466723705639331174975329 145100042779229498381231497)
      ·
        refine ⟨108825032084422123785923623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145100042779229498381231497 108825032084422123785923623)
        ·
          refine ⟨163237548126633185678885435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108825032084422123785923623 163237548126633185678885435)
          ·
            refine ⟨244856322189949778518328153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163237548126633185678885435 244856322189949778518328153)
            ·
              refine ⟨183642241642462333888746115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244856322189949778518328153 183642241642462333888746115)
              ·
                refine ⟨275463362463693500833119173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183642241642462333888746115 275463362463693500833119173)
                ·
                  refine ⟨51649380461942531406209845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 275463362463693500833119173 51649380461942531406209845)
                  ·
                    refine ⟨4842129418307112319332173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51649380461942531406209845 4842129418307112319332173)
                    ·
                      refine ⟨1815798531865167119749565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4842129418307112319332173 1815798531865167119749565)
                      ·
                        rfl

theorem cell23_3536255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5, 3].length) (baseStart_3536255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536255 prefixEnd_3536255 := by exact prefixLift 3536255
  have htrace : WordTrace (prefixWord ++ tailWord_3536255) baseStart_3536255 baseEnd_3536255 := by
    simpa [prefixWord, tailWord_3536255, baseEnd_3536255] using wordTrace_append hprefix tailTrace_3536255
  have hstable : (prefixWord ++ tailWord_3536255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536255).length < 2 ^ (prefixWord ++ tailWord_3536255).sum := by decide
  have hdescent : baseEnd_3536255 < baseStart_3536255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536329 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 5, 2, 2]
def baseStart_3536329 : Nat := 118140960795 + 3536329 * 2 ^ 59
def prefixEnd_3536329 : Nat := 4983230072969 + 3 ^ 40 * 3536329 * 2
def baseEnd_3536329 : Nat := 1815836529433599830224225

theorem tailTrace_3536329 : CollatzResearch.WordTrace tailWord_3536329 prefixEnd_3536329 1815836529433599830224225 := by
  unfold tailWord_3536329
  simp only [CollatzResearch.WordTrace]
  refine ⟨128980514805491464754844041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85987009870327643169896027 128980514805491464754844041)
  ·
    refine ⟨96735386104118598566133031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128980514805491464754844041 96735386104118598566133031)
    ·
      refine ⟨145103079156177897849199547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96735386104118598566133031 145103079156177897849199547)
      ·
        refine ⟨217654618734266846773799321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145103079156177897849199547 217654618734266846773799321)
        ·
          refine ⟨163240964050700135080349491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217654618734266846773799321 163240964050700135080349491)
          ·
            refine ⟨244861446076050202620524237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163240964050700135080349491 244861446076050202620524237)
            ·
              refine ⟨91823042278518825982696589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244861446076050202620524237 91823042278518825982696589)
              ·
                refine ⟨34433640854444559743511221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91823042278518825982696589 34433640854444559743511221)
                ·
                  refine ⟨3228153830104177475954177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34433640854444559743511221 3228153830104177475954177)
                  ·
                    refine ⟨2421115372578133106965633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3228153830104177475954177 2421115372578133106965633)
                    ·
                      refine ⟨1815836529433599830224225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2421115372578133106965633 1815836529433599830224225)
                      ·
                        rfl

theorem cell23_3536329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 5, 2, 2].length) (baseStart_3536329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536329 prefixEnd_3536329 := by exact prefixLift 3536329
  have htrace : WordTrace (prefixWord ++ tailWord_3536329) baseStart_3536329 baseEnd_3536329 := by
    simpa [prefixWord, tailWord_3536329, baseEnd_3536329] using wordTrace_append hprefix tailTrace_3536329
  have hstable : (prefixWord ++ tailWord_3536329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536329).length < 2 ^ (prefixWord ++ tailWord_3536329).sum := by decide
  have hdescent : baseEnd_3536329 < baseStart_3536329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536335 : List Nat := [1, 1, 2, 1, 1, 4, 4, 9]
def baseStart_3536335 : Nat := 118140960795 + 3536335 * 2 ^ 59
def prefixEnd_3536335 : Nat := 4983230072969 + 3 ^ 40 * 3536335 * 2
def baseEnd_3536335 : Nat := 67253318900649140990711

theorem tailTrace_3536335 : CollatzResearch.WordTrace tailWord_3536335 prefixEnd_3536335 67253318900649140990711 := by
  unfold tailWord_3536335
  simp only [CollatzResearch.WordTrace]
  refine ⟨128980733643469727779562459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85987155762313151853041639 128980733643469727779562459)
  ·
    refine ⟨193471100465204591669343689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128980733643469727779562459 193471100465204591669343689)
    ·
      refine ⟨145103325348903443752007767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193471100465204591669343689 145103325348903443752007767)
      ·
        refine ⟨217654988023355165628011651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145103325348903443752007767 217654988023355165628011651)
        ·
          refine ⟨326482482035032748442017477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217654988023355165628011651 326482482035032748442017477)
          ·
            refine ⟨61215465381568640332878277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 326482482035032748442017477 61215465381568640332878277)
            ·
              refine ⟨11477899759044120062414677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61215465381568640332878277 11477899759044120062414677)
              ·
                refine ⟨67253318900649140990711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11477899759044120062414677 67253318900649140990711)
                ·
                  rfl

theorem cell23_3536335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 9].length) (baseStart_3536335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536335 prefixEnd_3536335 := by exact prefixLift 3536335
  have htrace : WordTrace (prefixWord ++ tailWord_3536335) baseStart_3536335 baseEnd_3536335 := by
    simpa [prefixWord, tailWord_3536335, baseEnd_3536335] using wordTrace_append hprefix tailTrace_3536335
  have hstable : (prefixWord ++ tailWord_3536335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536335).length < 2 ^ (prefixWord ++ tailWord_3536335).sum := by decide
  have hdescent : baseEnd_3536335 < baseStart_3536335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536346 : List Nat := [3, 1, 1, 2, 3, 3, 3, 1, 1, 1, 4]
def baseStart_3536346 : Nat := 118140960795 + 3536346 * 2 ^ 59
def prefixEnd_3536346 : Nat := 4983230072969 + 3 ^ 40 * 3536346 * 2
def baseEnd_3536346 : Nat := 1815845258604726263711647

theorem tailTrace_3536346 : CollatzResearch.WordTrace tailWord_3536346 prefixEnd_3536346 1815845258604726263711647 := by
  unfold tailWord_3536346
  simp only [CollatzResearch.WordTrace]
  refine ⟨32245283711607469164553223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85987423230953251105475261 32245283711607469164553223)
  ·
    refine ⟨48367925567411203746829835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32245283711607469164553223 48367925567411203746829835)
    ·
      refine ⟨72551888351116805620244753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48367925567411203746829835 72551888351116805620244753)
      ·
        refine ⟨54413916263337604215183565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72551888351116805620244753 54413916263337604215183565)
        ·
          refine ⟨20405218598751601580693837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54413916263337604215183565 20405218598751601580693837)
          ·
            refine ⟨7651956974531850592760189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20405218598751601580693837 7651956974531850592760189)
            ·
              refine ⟨2869483865449443972285071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7651956974531850592760189 2869483865449443972285071)
              ·
                refine ⟨4304225798174165958427607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2869483865449443972285071 4304225798174165958427607)
                ·
                  refine ⟨6456338697261248937641411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4304225798174165958427607 6456338697261248937641411)
                  ·
                    refine ⟨9684508045891873406462117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6456338697261248937641411 9684508045891873406462117)
                    ·
                      refine ⟨1815845258604726263711647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9684508045891873406462117 1815845258604726263711647)
                      ·
                        rfl

theorem cell23_3536346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 1, 1, 4].length) (baseStart_3536346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536346 prefixEnd_3536346 := by exact prefixLift 3536346
  have htrace : WordTrace (prefixWord ++ tailWord_3536346) baseStart_3536346 baseEnd_3536346 := by
    simpa [prefixWord, tailWord_3536346, baseEnd_3536346] using wordTrace_append hprefix tailTrace_3536346
  have hstable : (prefixWord ++ tailWord_3536346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536346).length < 2 ^ (prefixWord ++ tailWord_3536346).sum := by decide
  have hdescent : baseEnd_3536346 < baseStart_3536346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536349 : List Nat := [1, 4, 3, 1, 1, 2, 3, 1, 1, 1, 5]
def baseStart_3536349 : Nat := 118140960795 + 3536349 * 2 ^ 59
def prefixEnd_3536349 : Nat := 4983230072969 + 3 ^ 40 * 3536349 * 2
def baseEnd_3536349 : Nat := 1815846799046689751974133

theorem tailTrace_3536349 : CollatzResearch.WordTrace tailWord_3536349 prefixEnd_3536349 1815846799046689751974133 := by
  unfold tailWord_3536349
  simp only [CollatzResearch.WordTrace]
  refine ⟨128981244265419008170572101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85987496176946005447048067 128981244265419008170572101)
  ·
    refine ⟨24183983299766064031982269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128981244265419008170572101 24183983299766064031982269)
    ·
      refine ⟨9068993737412274011993351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24183983299766064031982269 9068993737412274011993351)
      ·
        refine ⟨13603490606118411017990027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9068993737412274011993351 13603490606118411017990027)
        ·
          refine ⟨20405235909177616526985041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13603490606118411017990027 20405235909177616526985041)
          ·
            refine ⟨15303926931883212395238781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20405235909177616526985041 15303926931883212395238781)
            ·
              refine ⟨5738972599456204648214543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15303926931883212395238781 5738972599456204648214543)
              ·
                refine ⟨8608458899184306972321815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5738972599456204648214543 8608458899184306972321815)
                ·
                  refine ⟨12912688348776460458482723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8608458899184306972321815 12912688348776460458482723)
                  ·
                    refine ⟨19369032523164690687724085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12912688348776460458482723 19369032523164690687724085)
                    ·
                      refine ⟨1815846799046689751974133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19369032523164690687724085 1815846799046689751974133)
                      ·
                        rfl

theorem cell23_3536349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_3536349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536349 prefixEnd_3536349 := by exact prefixLift 3536349
  have htrace : WordTrace (prefixWord ++ tailWord_3536349) baseStart_3536349 baseEnd_3536349 := by
    simpa [prefixWord, tailWord_3536349, baseEnd_3536349] using wordTrace_append hprefix tailTrace_3536349
  have hstable : (prefixWord ++ tailWord_3536349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536349).length < 2 ^ (prefixWord ++ tailWord_3536349).sum := by decide
  have hdescent : baseEnd_3536349 < baseStart_3536349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536386 : List Nat := [3, 4, 1, 2, 1, 2, 3, 7]
def baseStart_3536386 : Nat := 118140960795 + 3536386 * 2 ^ 59
def prefixEnd_3536386 : Nat := 4983230072969 + 3 ^ 40 * 3536386 * 2
def baseEnd_3536386 : Nat := 67254288808552078044869

theorem tailTrace_3536386 : CollatzResearch.WordTrace tailWord_3536386 prefixEnd_3536386 67254288808552078044869 := by
  unfold tailWord_3536386
  simp only [CollatzResearch.WordTrace]
  refine ⟨32245648441571240872417253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85988395844189975659779341 32245648441571240872417253)
  ·
    refine ⟨6046059082794607663578235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32245648441571240872417253 6046059082794607663578235)
    ·
      refine ⟨9069088624191911495367353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6046059082794607663578235 9069088624191911495367353)
      ·
        refine ⟨6801816468143933621525515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9069088624191911495367353 6801816468143933621525515)
        ·
          refine ⟨10202724702215900432288273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6801816468143933621525515 10202724702215900432288273)
          ·
            refine ⟨7652043526661925324216205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10202724702215900432288273 7652043526661925324216205)
            ·
              refine ⟨2869516322498221996581077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7652043526661925324216205 2869516322498221996581077)
              ·
                refine ⟨67254288808552078044869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2869516322498221996581077 67254288808552078044869)
                ·
                  rfl

theorem cell23_3536386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 7].length) (baseStart_3536386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536386 prefixEnd_3536386 := by exact prefixLift 3536386
  have htrace : WordTrace (prefixWord ++ tailWord_3536386) baseStart_3536386 baseEnd_3536386 := by
    simpa [prefixWord, tailWord_3536386, baseEnd_3536386] using wordTrace_append hprefix tailTrace_3536386
  have hstable : (prefixWord ++ tailWord_3536386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536386).length < 2 ^ (prefixWord ++ tailWord_3536386).sum := by decide
  have hdescent : baseEnd_3536386 < baseStart_3536386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536397 : List Nat := [1, 7, 1, 1, 2, 2, 2, 1, 1, 1, 4]
def baseStart_3536397 : Nat := 118140960795 + 3536397 * 2 ^ 59
def prefixEnd_3536397 : Nat := 4983230072969 + 3 ^ 40 * 3536397 * 2
def baseEnd_3536397 : Nat := 1815871446118105564173913

theorem tailTrace_3536397 : CollatzResearch.WordTrace tailWord_3536397 prefixEnd_3536397 1815871446118105564173913 := by
  unfold tailWord_3536397
  simp only [CollatzResearch.WordTrace]
  refine ⟨128982994969245112368319445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85988663312830074912212963 128982994969245112368319445)
  ·
    refine ⟨3023038944591682321132487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 128982994969245112368319445 3023038944591682321132487)
    ·
      refine ⟨4534558416887523481698731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3023038944591682321132487 4534558416887523481698731)
      ·
        refine ⟨6801837625331285222548097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4534558416887523481698731 6801837625331285222548097)
        ·
          refine ⟨5101378218998463916911073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6801837625331285222548097 5101378218998463916911073)
          ·
            refine ⟨3826033664248847937683305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5101378218998463916911073 3826033664248847937683305)
            ·
              refine ⟨2869525248186635953262479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3826033664248847937683305 2869525248186635953262479)
              ·
                refine ⟨4304287872279953929893719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2869525248186635953262479 4304287872279953929893719)
                ·
                  refine ⟨6456431808419930894840579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4304287872279953929893719 6456431808419930894840579)
                  ·
                    refine ⟨9684647712629896342260869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6456431808419930894840579 9684647712629896342260869)
                    ·
                      refine ⟨1815871446118105564173913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9684647712629896342260869 1815871446118105564173913)
                      ·
                        rfl

theorem cell23_3536397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_3536397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536397 prefixEnd_3536397 := by exact prefixLift 3536397
  have htrace : WordTrace (prefixWord ++ tailWord_3536397) baseStart_3536397 baseEnd_3536397 := by
    simpa [prefixWord, tailWord_3536397, baseEnd_3536397] using wordTrace_append hprefix tailTrace_3536397
  have hstable : (prefixWord ++ tailWord_3536397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536397).length < 2 ^ (prefixWord ++ tailWord_3536397).sum := by decide
  have hdescent : baseEnd_3536397 < baseStart_3536397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536412 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 4, 6]
def baseStart_3536412 : Nat := 118140960795 + 3536412 * 2 ^ 59
def prefixEnd_3536412 : Nat := 4983230072969 + 3 ^ 40 * 3536412 * 2
def baseEnd_3536412 : Nat := 605293049442641001828781

theorem tailTrace_3536412 : CollatzResearch.WordTrace tailWord_3536412 prefixEnd_3536412 605293049442641001828781 := by
  unfold tailWord_3536412
  simp only [CollatzResearch.WordTrace]
  refine ⟨64491771032095384965057745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85989028042793846620076993 64491771032095384965057745)
  ·
    refine ⟨48368828274071538723793309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64491771032095384965057745 48368828274071538723793309)
    ·
      refine ⟨18138310602776827021422491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48368828274071538723793309 18138310602776827021422491)
      ·
        refine ⟨27207465904165240532133737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18138310602776827021422491 27207465904165240532133737)
        ·
          refine ⟨20405599428123930399100303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27207465904165240532133737 20405599428123930399100303)
          ·
            refine ⟨30608399142185895598650455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20405599428123930399100303 30608399142185895598650455)
            ·
              refine ⟨45912598713278843397975683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30608399142185895598650455 45912598713278843397975683)
              ·
                refine ⟨68868898069918265096963525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45912598713278843397975683 68868898069918265096963525)
                ·
                  refine ⟨12912918388109674705680661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68868898069918265096963525 12912918388109674705680661)
                  ·
                    refine ⟨605293049442641001828781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12912918388109674705680661 605293049442641001828781)
                    ·
                      rfl

theorem cell23_3536412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_3536412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536412 prefixEnd_3536412 := by exact prefixLift 3536412
  have htrace : WordTrace (prefixWord ++ tailWord_3536412) baseStart_3536412 baseEnd_3536412 := by
    simpa [prefixWord, tailWord_3536412, baseEnd_3536412] using wordTrace_append hprefix tailTrace_3536412
  have hstable : (prefixWord ++ tailWord_3536412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536412).length < 2 ^ (prefixWord ++ tailWord_3536412).sum := by decide
  have hdescent : baseEnd_3536412 < baseStart_3536412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536414 : List Nat := [4, 3, 3, 1, 1, 1, 2, 1, 3, 2, 2]
def baseStart_3536414 : Nat := 118140960795 + 3536414 * 2 ^ 59
def prefixEnd_3536414 : Nat := 4983230072969 + 3 ^ 40 * 3536414 * 2
def baseEnd_3536414 : Nat := 1815880175289231997661335

theorem tailTrace_3536414 : CollatzResearch.WordTrace tailWord_3536414 prefixEnd_3536414 1815880175289231997661335 := by
  unfold tailWord_3536414
  simp only [CollatzResearch.WordTrace]
  refine ⟨16122951876272940533961037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85989076673455682847792197 16122951876272940533961037)
  ·
    refine ⟨6046106953602352700235389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16122951876272940533961037 6046106953602352700235389)
    ·
      refine ⟨2267290107600882262588271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6046106953602352700235389 2267290107600882262588271)
      ·
        refine ⟨3400935161401323393882407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2267290107600882262588271 3400935161401323393882407)
        ·
          refine ⟨5101402742101985090823611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3400935161401323393882407 5101402742101985090823611)
          ·
            refine ⟨7652104113152977636235417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5101402742101985090823611 7652104113152977636235417)
            ·
              refine ⟨5739078084864733227176563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7652104113152977636235417 5739078084864733227176563)
              ·
                refine ⟨8608617127297099840764845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5739078084864733227176563 8608617127297099840764845)
                ·
                  refine ⟨3228231422736412440286817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8608617127297099840764845 3228231422736412440286817)
                  ·
                    refine ⟨2421173567052309330215113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3228231422736412440286817 2421173567052309330215113)
                    ·
                      refine ⟨1815880175289231997661335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2421173567052309330215113 1815880175289231997661335)
                      ·
                        rfl

theorem cell23_3536414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_3536414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536414 prefixEnd_3536414 := by exact prefixLift 3536414
  have htrace : WordTrace (prefixWord ++ tailWord_3536414) baseStart_3536414 baseEnd_3536414 := by
    simpa [prefixWord, tailWord_3536414, baseEnd_3536414] using wordTrace_append hprefix tailTrace_3536414
  have hstable : (prefixWord ++ tailWord_3536414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536414).length < 2 ^ (prefixWord ++ tailWord_3536414).sum := by decide
  have hdescent : baseEnd_3536414 < baseStart_3536414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536430 : List Nat := [4, 1, 3, 1, 2, 2, 3, 1, 2, 1, 3]
def baseStart_3536430 : Nat := 118140960795 + 3536430 * 2 ^ 59
def prefixEnd_3536430 : Nat := 4983230072969 + 3 ^ 40 * 3536430 * 2
def baseEnd_3536430 : Nat := 1815888390979703935061261

theorem tailTrace_3536430 : CollatzResearch.WordTrace tailWord_3536430 prefixEnd_3536430 1815888390979703935061261 := by
  unfold tailWord_3536430
  simp only [CollatzResearch.WordTrace]
  refine ⟨16123024822265694875533843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85989465718750372669513829 16123024822265694875533843)
  ·
    refine ⟨24184537233398542313300765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16123024822265694875533843 24184537233398542313300765)
    ·
      refine ⟨9069201462524453367487787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24184537233398542313300765 9069201462524453367487787)
      ·
        refine ⟨13603802193786680051231681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9069201462524453367487787 13603802193786680051231681)
        ·
          refine ⟨10202851645340010038423761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13603802193786680051231681 10202851645340010038423761)
          ·
            refine ⟨7652138734005007528817821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10202851645340010038423761 7652138734005007528817821)
            ·
              refine ⟨2869552025251877823306683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7652138734005007528817821 2869552025251877823306683)
              ·
                refine ⟨4304328037877816734960025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2869552025251877823306683 4304328037877816734960025)
                ·
                  refine ⟨3228246028408362551220019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4304328037877816734960025 3228246028408362551220019)
                  ·
                    refine ⟨4842369042612543826830029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3228246028408362551220019 4842369042612543826830029)
                    ·
                      refine ⟨1815888390979703935061261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4842369042612543826830029 1815888390979703935061261)
                      ·
                        rfl

theorem cell23_3536430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_3536430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536430 prefixEnd_3536430 := by exact prefixLift 3536430
  have htrace : WordTrace (prefixWord ++ tailWord_3536430) baseStart_3536430 baseEnd_3536430 := by
    simpa [prefixWord, tailWord_3536430, baseEnd_3536430] using wordTrace_append hprefix tailTrace_3536430
  have hstable : (prefixWord ++ tailWord_3536430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536430).length < 2 ^ (prefixWord ++ tailWord_3536430).sum := by decide
  have hdescent : baseEnd_3536430 < baseStart_3536430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536442 : List Nat := [3, 1, 1, 1, 3, 2, 1, 4, 7]
def baseStart_3536442 : Nat := 118140960795 + 3536442 * 2 ^ 59
def prefixEnd_3536442 : Nat := 4983230072969 + 3 ^ 40 * 3536442 * 2
def baseEnd_3536442 : Nat := 201766061416395320901245

theorem tailTrace_3536442 : CollatzResearch.WordTrace tailWord_3536442 prefixEnd_3536442 201766061416395320901245 := by
  unfold tailWord_3536442
  simp only [CollatzResearch.WordTrace]
  refine ⟨32246159063520521263426895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85989757502721390035805053 32246159063520521263426895)
  ·
    refine ⟨48369238595280781895140343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32246159063520521263426895 48369238595280781895140343)
    ·
      refine ⟨72553857892921172842710515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48369238595280781895140343 72553857892921172842710515)
      ·
        refine ⟨108830786839381759264065773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72553857892921172842710515 108830786839381759264065773)
        ·
          refine ⟨40811545064768159724024665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108830786839381759264065773 40811545064768159724024665)
          ·
            refine ⟨30608658798576119793018499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40811545064768159724024665 30608658798576119793018499)
            ·
              refine ⟨45912988197864179689527749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30608658798576119793018499 45912988197864179689527749)
              ·
                refine ⟨8608685287099533691786453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45912988197864179689527749 8608685287099533691786453)
                ·
                  refine ⟨201766061416395320901245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8608685287099533691786453 201766061416395320901245)
                  ·
                    rfl

theorem cell23_3536442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 7].length) (baseStart_3536442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536442 prefixEnd_3536442 := by exact prefixLift 3536442
  have htrace : WordTrace (prefixWord ++ tailWord_3536442) baseStart_3536442 baseEnd_3536442 := by
    simpa [prefixWord, tailWord_3536442, baseEnd_3536442] using wordTrace_append hprefix tailTrace_3536442
  have hstable : (prefixWord ++ tailWord_3536442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536442).length < 2 ^ (prefixWord ++ tailWord_3536442).sum := by decide
  have hdescent : baseEnd_3536442 < baseStart_3536442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536476 : List Nat := [2, 2, 4, 1, 2, 3, 1, 1, 7]
def baseStart_3536476 : Nat := 118140960795 + 3536476 * 2 ^ 59
def prefixEnd_3536476 : Nat := 4983230072969 + 3 ^ 40 * 3536476 * 2
def baseEnd_3536476 : Nat := 201768001232201195009561

theorem tailTrace_3536476 : CollatzResearch.WordTrace tailWord_3536476 prefixEnd_3536476 201768001232201195009561 := by
  unfold tailWord_3536476
  simp only [CollatzResearch.WordTrace]
  refine ⟨64492938167979454430222641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85990584223972605906963521 64492938167979454430222641)
  ·
    refine ⟨48369703625984590822666981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64492938167979454430222641 48369703625984590822666981)
    ·
      refine ⟨9069319429872110779250059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48369703625984590822666981 9069319429872110779250059)
      ·
        refine ⟨13603979144808166168875089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9069319429872110779250059 13603979144808166168875089)
        ·
          refine ⟨10202984358606124626656317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13603979144808166168875089 10202984358606124626656317)
          ·
            refine ⟨3826119134477296734996119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10202984358606124626656317 3826119134477296734996119)
            ·
              refine ⟨5739178701715945102494179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3826119134477296734996119 5739178701715945102494179)
              ·
                refine ⟨8608768052573917653741269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5739178701715945102494179 8608768052573917653741269)
                ·
                  refine ⟨201768001232201195009561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8608768052573917653741269 201768001232201195009561)
                  ·
                    rfl

theorem cell23_3536476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 7].length) (baseStart_3536476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536476 prefixEnd_3536476 := by exact prefixLift 3536476
  have htrace : WordTrace (prefixWord ++ tailWord_3536476) baseStart_3536476 baseEnd_3536476 := by
    simpa [prefixWord, tailWord_3536476, baseEnd_3536476] using wordTrace_append hprefix tailTrace_3536476
  have hstable : (prefixWord ++ tailWord_3536476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536476).length < 2 ^ (prefixWord ++ tailWord_3536476).sum := by decide
  have hdescent : baseEnd_3536476 < baseStart_3536476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536526 : List Nat := [4, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4]
def baseStart_3536526 : Nat := 118140960795 + 3536526 * 2 ^ 59
def prefixEnd_3536526 : Nat := 4983230072969 + 3 ^ 40 * 3536526 * 2
def baseEnd_3536526 : Nat := 1815937685122535559460819

theorem tailTrace_3536526 : CollatzResearch.WordTrace tailWord_3536526 prefixEnd_3536526 1815937685122535559460819 := by
  unfold tailWord_3536526
  simp only [CollatzResearch.WordTrace]
  refine ⟨16123462498222220924970679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85991799990518511599843621 16123462498222220924970679)
  ·
    refine ⟨24185193747333331387456019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16123462498222220924970679 24185193747333331387456019)
    ·
      refine ⟨36277790620999997081184029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24185193747333331387456019 36277790620999997081184029)
      ·
        refine ⟨13604171482874998905444011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36277790620999997081184029 13604171482874998905444011)
        ·
          refine ⟨20406257224312498358166017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13604171482874998905444011 20406257224312498358166017)
          ·
            refine ⟨15304692918234373768624513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20406257224312498358166017 15304692918234373768624513)
            ·
              refine ⟨11478519688675780326468385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15304692918234373768624513 11478519688675780326468385)
              ·
                refine ⟨8608889766506835244851289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11478519688675780326468385 8608889766506835244851289)
                ·
                  refine ⟨6456667324880126433638467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8608889766506835244851289 6456667324880126433638467)
                  ·
                    refine ⟨9685000987320189650457701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6456667324880126433638467 9685000987320189650457701)
                    ·
                      refine ⟨1815937685122535559460819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9685000987320189650457701 1815937685122535559460819)
                      ·
                        rfl

theorem cell23_3536526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_3536526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536526 prefixEnd_3536526 := by exact prefixLift 3536526
  have htrace : WordTrace (prefixWord ++ tailWord_3536526) baseStart_3536526 baseEnd_3536526 := by
    simpa [prefixWord, tailWord_3536526, baseEnd_3536526] using wordTrace_append hprefix tailTrace_3536526
  have hstable : (prefixWord ++ tailWord_3536526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536526).length < 2 ^ (prefixWord ++ tailWord_3536526).sum := by decide
  have hdescent : baseEnd_3536526 < baseStart_3536526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536529 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 3]
def baseStart_3536529 : Nat := 118140960795 + 3536529 * 2 ^ 59
def prefixEnd_3536529 : Nat := 4983230072969 + 3 ^ 40 * 3536529 * 2
def baseEnd_3536529 : Nat := 1815939225564499047723305

theorem tailTrace_3536529 : CollatzResearch.WordTrace tailWord_3536529 prefixEnd_3536529 1815939225564499047723305 := by
  unfold tailWord_3536529
  simp only [CollatzResearch.WordTrace]
  refine ⟨128987809404766898912124641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85991872936511265941416427 128987809404766898912124641)
  ·
    refine ⟨96740857053575174184093481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128987809404766898912124641 96740857053575174184093481)
    ·
      refine ⟨72555642790181380638070111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96740857053575174184093481 72555642790181380638070111)
      ·
        refine ⟨108833464185272070957105167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72555642790181380638070111 108833464185272070957105167)
        ·
          refine ⟨163250196277908106435657751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108833464185272070957105167 163250196277908106435657751)
          ·
            refine ⟨244875294416862159653486627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163250196277908106435657751 244875294416862159653486627)
            ·
              refine ⟨367312941625293239480229941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244875294416862159653486627 367312941625293239480229941)
              ·
                refine ⟨34435588277371241201271557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 367312941625293239480229941 34435588277371241201271557)
                ·
                  refine ⟨6456672802007107725238417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34435588277371241201271557 6456672802007107725238417)
                  ·
                    refine ⟨4842504601505330793928813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6456672802007107725238417 4842504601505330793928813)
                    ·
                      refine ⟨1815939225564499047723305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4842504601505330793928813 1815939225564499047723305)
                      ·
                        rfl

theorem cell23_3536529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 3].length) (baseStart_3536529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536529 prefixEnd_3536529 := by exact prefixLift 3536529
  have htrace : WordTrace (prefixWord ++ tailWord_3536529) baseStart_3536529 baseEnd_3536529 := by
    simpa [prefixWord, tailWord_3536529, baseEnd_3536529] using wordTrace_append hprefix tailTrace_3536529
  have hstable : (prefixWord ++ tailWord_3536529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536529).length < 2 ^ (prefixWord ++ tailWord_3536529).sum := by decide
  have hdescent : baseEnd_3536529 < baseStart_3536529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536549 : List Nat := [1, 3, 1, 2, 1, 2, 4, 3, 6]
def baseStart_3536549 : Nat := 118140960795 + 3536549 * 2 ^ 59
def prefixEnd_3536549 : Nat := 4983230072969 + 3 ^ 40 * 3536549 * 2
def baseEnd_3536549 : Nat := 201772166130843218830357

theorem tailTrace_3536549 : CollatzResearch.WordTrace tailWord_3536549 prefixEnd_3536549 201772166130843218830357 := by
  unfold tailWord_3536549
  simp only [CollatzResearch.WordTrace]
  refine ⟨128988538864694442327852701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85992359243129628218568467 128988538864694442327852701)
  ·
    refine ⟨48370702074260415872944763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128988538864694442327852701 48370702074260415872944763)
    ·
      refine ⟨72556053111390623809417145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48370702074260415872944763 72556053111390623809417145)
      ·
        refine ⟨54417039833542967857062859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72556053111390623809417145 54417039833542967857062859)
        ·
          refine ⟨81625559750314451785594289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54417039833542967857062859 81625559750314451785594289)
          ·
            refine ⟨61219169812735838839195717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81625559750314451785594289 61219169812735838839195717)
            ·
              refine ⟨11478594339887969782349197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61219169812735838839195717 11478594339887969782349197)
              ·
                refine ⟨4304472877457988668380949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11478594339887969782349197 4304472877457988668380949)
                ·
                  refine ⟨201772166130843218830357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4304472877457988668380949 201772166130843218830357)
                  ·
                    rfl

theorem cell23_3536549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 6].length) (baseStart_3536549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536549 prefixEnd_3536549 := by exact prefixLift 3536549
  have htrace : WordTrace (prefixWord ++ tailWord_3536549) baseStart_3536549 baseEnd_3536549 := by
    simpa [prefixWord, tailWord_3536549, baseEnd_3536549] using wordTrace_append hprefix tailTrace_3536549
  have hstable : (prefixWord ++ tailWord_3536549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536549).length < 2 ^ (prefixWord ++ tailWord_3536549).sum := by decide
  have hdescent : baseEnd_3536549 < baseStart_3536549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536576 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 5, 1, 3]
def baseStart_3536576 : Nat := 118140960795 + 3536576 * 2 ^ 59
def prefixEnd_3536576 : Nat := 4983230072969 + 3 ^ 40 * 3536576 * 2
def baseEnd_3536576 : Nat := 1815963359155260363835589

theorem tailTrace_3536576 : CollatzResearch.WordTrace tailWord_3536576 prefixEnd_3536576 1815963359155260363835589 := by
  unfold tailWord_3536576
  simp only [CollatzResearch.WordTrace]
  refine ⟨64494761817798312969542791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85993015757064417292723721 64494761817798312969542791)
  ·
    refine ⟨96742142726697469454314187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64494761817798312969542791 96742142726697469454314187)
    ·
      refine ⟨145113214090046204181471281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96742142726697469454314187 145113214090046204181471281)
      ·
        refine ⟨108834910567534653136103461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145113214090046204181471281 108834910567534653136103461)
        ·
          refine ⟨20406545731412747463019399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108834910567534653136103461 20406545731412747463019399)
          ·
            refine ⟨30609818597119121194529099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20406545731412747463019399 30609818597119121194529099)
            ·
              refine ⟨45914727895678681791793649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30609818597119121194529099 45914727895678681791793649)
              ·
                refine ⟨34436045921759011343845237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45914727895678681791793649 34436045921759011343845237)
                ·
                  refine ⟨3228379305164907313485491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34436045921759011343845237 3228379305164907313485491)
                  ·
                    refine ⟨4842568957747360970228237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3228379305164907313485491 4842568957747360970228237)
                    ·
                      refine ⟨1815963359155260363835589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4842568957747360970228237 1815963359155260363835589)
                      ·
                        rfl

theorem cell23_3536576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 5, 1, 3].length) (baseStart_3536576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536576 prefixEnd_3536576 := by exact prefixLift 3536576
  have htrace : WordTrace (prefixWord ++ tailWord_3536576) baseStart_3536576 baseEnd_3536576 := by
    simpa [prefixWord, tailWord_3536576, baseEnd_3536576] using wordTrace_append hprefix tailTrace_3536576
  have hstable : (prefixWord ++ tailWord_3536576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536576).length < 2 ^ (prefixWord ++ tailWord_3536576).sum := by decide
  have hdescent : baseEnd_3536576 < baseStart_3536576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536593 : List Nat := [1, 2, 2, 1, 2, 5, 2, 1, 3, 1, 3]
def baseStart_3536593 : Nat := 118140960795 + 3536593 * 2 ^ 59
def prefixEnd_3536593 : Nat := 4983230072969 + 3 ^ 40 * 3536593 * 2
def baseEnd_3536593 : Nat := 1815972088326386797323011

theorem tailTrace_3536593 : CollatzResearch.WordTrace tailWord_3536593 prefixEnd_3536593 1815972088326386797323011 := by
  unfold tailWord_3536593
  simp only [CollatzResearch.WordTrace]
  refine ⟨128990143676535037842454433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85993429117690025228302955 128990143676535037842454433)
  ·
    refine ⟨96742607757401278381840825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128990143676535037842454433 96742607757401278381840825)
    ·
      refine ⟨72556955818050958786380619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96742607757401278381840825 72556955818050958786380619)
      ·
        refine ⟨108835433727076438179570929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72556955818050958786380619 108835433727076438179570929)
        ·
          refine ⟨81626575295307328634678197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108835433727076438179570929 81626575295307328634678197)
          ·
            refine ⟨7652491433935062059501081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81626575295307328634678197 7652491433935062059501081)
            ·
              refine ⟨5739368575451296544625811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7652491433935062059501081 5739368575451296544625811)
              ·
                refine ⟨8609052863176944816938717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5739368575451296544625811 8609052863176944816938717)
                ·
                  refine ⟨3228394823691354306352019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8609052863176944816938717 3228394823691354306352019)
                  ·
                    refine ⟨4842592235537031459528029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3228394823691354306352019 4842592235537031459528029)
                    ·
                      refine ⟨1815972088326386797323011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4842592235537031459528029 1815972088326386797323011)
                      ·
                        rfl

theorem cell23_3536593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 3, 1, 3].length) (baseStart_3536593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536593 prefixEnd_3536593 := by exact prefixLift 3536593
  have htrace : WordTrace (prefixWord ++ tailWord_3536593) baseStart_3536593 baseEnd_3536593 := by
    simpa [prefixWord, tailWord_3536593, baseEnd_3536593] using wordTrace_append hprefix tailTrace_3536593
  have hstable : (prefixWord ++ tailWord_3536593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536593).length < 2 ^ (prefixWord ++ tailWord_3536593).sum := by decide
  have hdescent : baseEnd_3536593 < baseStart_3536593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536626 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 6, 4]
def baseStart_3536626 : Nat := 118140960795 + 3536626 * 2 ^ 59
def prefixEnd_3536626 : Nat := 4983230072969 + 3 ^ 40 * 3536626 * 2
def baseEnd_3536626 : Nat := 605329677729328389403453

theorem tailTrace_3536626 : CollatzResearch.WordTrace tailWord_3536626 prefixEnd_3536626 605329677729328389403453 := by
  unfold tailWord_3536626
  simp only [CollatzResearch.WordTrace]
  refine ⟨32247836821353871119601433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85994231523610322985603821 32247836821353871119601433)
  ·
    refine ⟨24185877616015403339701075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32247836821353871119601433 24185877616015403339701075)
    ·
      refine ⟨36278816424023105009551613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24185877616015403339701075 36278816424023105009551613)
      ·
        refine ⟨13604556159008664378581855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36278816424023105009551613 13604556159008664378581855)
        ·
          refine ⟨20406834238512996567872783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13604556159008664378581855 20406834238512996567872783)
          ·
            refine ⟨30610251357769494851809175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20406834238512996567872783 30610251357769494851809175)
            ·
              refine ⟨45915377036654242277713763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30610251357769494851809175 45915377036654242277713763)
              ·
                refine ⟨68873065554981363416570645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45915377036654242277713763 68873065554981363416570645)
                ·
                  refine ⟨3228424947889751410151749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 68873065554981363416570645 3228424947889751410151749)
                  ·
                    refine ⟨605329677729328389403453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3228424947889751410151749 605329677729328389403453)
                    ·
                      rfl

theorem cell23_3536626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_3536626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536626 prefixEnd_3536626 := by exact prefixLift 3536626
  have htrace : WordTrace (prefixWord ++ tailWord_3536626) baseStart_3536626 baseEnd_3536626 := by
    simpa [prefixWord, tailWord_3536626, baseEnd_3536626] using wordTrace_append hprefix tailTrace_3536626
  have hstable : (prefixWord ++ tailWord_3536626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536626).length < 2 ^ (prefixWord ++ tailWord_3536626).sum := by decide
  have hdescent : baseEnd_3536626 < baseStart_3536626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536636 : List Nat := [2, 2, 2, 1, 3, 1, 4, 1, 1, 1, 5]
def baseStart_3536636 : Nat := 118140960795 + 3536636 * 2 ^ 59
def prefixEnd_3536636 : Nat := 4983230072969 + 3 ^ 40 * 3536636 * 2
def baseEnd_3536636 : Nat := 1815994167994530129085313

theorem tailTrace_3536636 : CollatzResearch.WordTrace tailWord_3536636 prefixEnd_3536636 1815994167994530129085313 := by
  unfold tailWord_3536636
  simp only [CollatzResearch.WordTrace]
  refine ⟨64495856007689628093134881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85994474676919504124179841 64495856007689628093134881)
  ·
    refine ⟨48371892005767221069851161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64495856007689628093134881 48371892005767221069851161)
    ·
      refine ⟨36278919004325415802388371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48371892005767221069851161 36278919004325415802388371)
      ·
        refine ⟨54418378506488123703582557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36278919004325415802388371 54418378506488123703582557)
        ·
          refine ⟨20406891939933046388843459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54418378506488123703582557 20406891939933046388843459)
          ·
            refine ⟨30610337909899569583265189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20406891939933046388843459 30610337909899569583265189)
            ·
              refine ⟨5739438358106169296862223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30610337909899569583265189 5739438358106169296862223)
              ·
                refine ⟨8609157537159253945293335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5739438358106169296862223 8609157537159253945293335)
                ·
                  refine ⟨12913736305738880917940003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8609157537159253945293335 12913736305738880917940003)
                  ·
                    refine ⟨19370604458608321376910005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12913736305738880917940003 19370604458608321376910005)
                    ·
                      refine ⟨1815994167994530129085313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19370604458608321376910005 1815994167994530129085313)
                      ·
                        rfl

theorem cell23_3536636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_3536636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536636 prefixEnd_3536636 := by exact prefixLift 3536636
  have htrace : WordTrace (prefixWord ++ tailWord_3536636) baseStart_3536636 baseEnd_3536636 := by
    simpa [prefixWord, tailWord_3536636, baseEnd_3536636] using wordTrace_append hprefix tailTrace_3536636
  have hstable : (prefixWord ++ tailWord_3536636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536636).length < 2 ^ (prefixWord ++ tailWord_3536636).sum := by decide
  have hdescent : baseEnd_3536636 < baseStart_3536636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536650 : List Nat := [3, 1, 2, 2, 1, 3, 3, 1, 3, 2, 2]
def baseStart_3536650 : Nat := 118140960795 + 3536650 * 2 ^ 59
def prefixEnd_3536650 : Nat := 4983230072969 + 3 ^ 40 * 3536650 * 2
def baseEnd_3536650 : Nat := 1816001356723693074310249

theorem tailTrace_3536650 : CollatzResearch.WordTrace tailWord_3536650 prefixEnd_3536650 1816001356723693074310249 := by
  unfold tailWord_3536650
  simp only [CollatzResearch.WordTrace]
  refine ⟨32248055659332134144319851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85994815091552357718186269 32248055659332134144319851)
  ·
    refine ⟨48372083488998201216479777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32248055659332134144319851 48372083488998201216479777)
    ·
      refine ⟨36279062616748650912359833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48372083488998201216479777 36279062616748650912359833)
      ·
        refine ⟨27209296962561488184269875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36279062616748650912359833 27209296962561488184269875)
        ·
          refine ⟨40813945443842232276404813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27209296962561488184269875 40813945443842232276404813)
          ·
            refine ⟨15305229541440837103651805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40813945443842232276404813 15305229541440837103651805)
            ·
              refine ⟨5739461078040313913869427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15305229541440837103651805 5739461078040313913869427)
              ·
                refine ⟨8609191617060470870804141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5739461078040313913869427 8609191617060470870804141)
                ·
                  refine ⟨3228446856397676576551553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8609191617060470870804141 3228446856397676576551553)
                  ·
                    refine ⟨2421335142298257432413665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3228446856397676576551553 2421335142298257432413665)
                    ·
                      refine ⟨1816001356723693074310249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2421335142298257432413665 1816001356723693074310249)
                      ·
                        rfl

theorem cell23_3536650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_3536650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536650 prefixEnd_3536650 := by exact prefixLift 3536650
  have htrace : WordTrace (prefixWord ++ tailWord_3536650) baseStart_3536650 baseEnd_3536650 := by
    simpa [prefixWord, tailWord_3536650, baseEnd_3536650] using wordTrace_append hprefix tailTrace_3536650
  have hstable : (prefixWord ++ tailWord_3536650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536650).length < 2 ^ (prefixWord ++ tailWord_3536650).sum := by decide
  have hdescent : baseEnd_3536650 < baseStart_3536650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536701 : List Nat := [1, 4, 1, 4, 1, 3, 2, 2, 1, 2, 2]
def baseStart_3536701 : Nat := 118140960795 + 3536701 * 2 ^ 59
def prefixEnd_3536701 : Nat := 4983230072969 + 3 ^ 40 * 3536701 * 2
def baseEnd_3536701 : Nat := 1816027544237072374772515

theorem tailTrace_3536701 : CollatzResearch.WordTrace tailWord_3536701 prefixEnd_3536701 1816027544237072374772515 := by
  unfold tailWord_3536701
  simp only [CollatzResearch.WordTrace]
  refine ⟨128994082760143772287385957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85996055173429181524923971 128994082760143772287385957)
  ·
    refine ⟨24186390517526957303884867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128994082760143772287385957 24186390517526957303884867)
    ·
      refine ⟨36279585776290435955827301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24186390517526957303884867 36279585776290435955827301)
      ·
        refine ⟨6802422333054456741717619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36279585776290435955827301 6802422333054456741717619)
        ·
          refine ⟨10203633499581685112576429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6802422333054456741717619 10203633499581685112576429)
          ·
            refine ⟨3826362562343131917216161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10203633499581685112576429 3826362562343131917216161)
            ·
              refine ⟨2869771921757348937912121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3826362562343131917216161 2869771921757348937912121)
              ·
                refine ⟨2152328941318011703434091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2869771921757348937912121 2152328941318011703434091)
                ·
                  refine ⟨3228493411977017555151137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2152328941318011703434091 3228493411977017555151137)
                  ·
                    refine ⟨2421370058982763166363353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3228493411977017555151137 2421370058982763166363353)
                    ·
                      refine ⟨1816027544237072374772515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2421370058982763166363353 1816027544237072374772515)
                      ·
                        rfl

theorem cell23_3536701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_3536701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536701 prefixEnd_3536701 := by exact prefixLift 3536701
  have htrace : WordTrace (prefixWord ++ tailWord_3536701) baseStart_3536701 baseEnd_3536701 := by
    simpa [prefixWord, tailWord_3536701, baseEnd_3536701] using wordTrace_append hprefix tailTrace_3536701
  have hstable : (prefixWord ++ tailWord_3536701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536701).length < 2 ^ (prefixWord ++ tailWord_3536701).sum := by decide
  have hdescent : baseEnd_3536701 < baseStart_3536701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536717 : List Nat := [1, 6, 1, 2, 1, 1, 2, 3, 2, 1, 3]
def baseStart_3536717 : Nat := 118140960795 + 3536717 * 2 ^ 59
def prefixEnd_3536717 : Nat := 4983230072969 + 3 ^ 40 * 3536717 * 2
def baseEnd_3536717 : Nat := 1816035759927544312172441

theorem tailTrace_3536717 : CollatzResearch.WordTrace tailWord_3536717 prefixEnd_3536717 1816035759927544312172441 := by
  unfold tailWord_3536717
  simp only [CollatzResearch.WordTrace]
  refine ⟨128994666328085807019968405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85996444218723871346645603 128994666328085807019968405)
  ·
    refine ⟨6046624984129022204061019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 128994666328085807019968405 6046624984129022204061019)
    ·
      refine ⟨9069937476193533306091529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6046624984129022204061019 9069937476193533306091529)
      ·
        refine ⟨6802453107145149979568647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9069937476193533306091529 6802453107145149979568647)
        ·
          refine ⟨10203679660717724969352971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6802453107145149979568647 10203679660717724969352971)
          ·
            refine ⟨15305519491076587454029457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10203679660717724969352971 15305519491076587454029457)
            ·
              refine ⟨11479139618307440590522093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15305519491076587454029457 11479139618307440590522093)
              ·
                refine ⟨4304677356865290221445785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11479139618307440590522093 4304677356865290221445785)
                ·
                  refine ⟨3228508017648967666084339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4304677356865290221445785 3228508017648967666084339)
                  ·
                    refine ⟨4842762026473451499126509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3228508017648967666084339 4842762026473451499126509)
                    ·
                      refine ⟨1816035759927544312172441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4842762026473451499126509 1816035759927544312172441)
                      ·
                        rfl

theorem cell23_3536717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_3536717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536717 prefixEnd_3536717 := by exact prefixLift 3536717
  have htrace : WordTrace (prefixWord ++ tailWord_3536717) baseStart_3536717 baseEnd_3536717 := by
    simpa [prefixWord, tailWord_3536717, baseEnd_3536717] using wordTrace_append hprefix tailTrace_3536717
  have hstable : (prefixWord ++ tailWord_3536717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536717).length < 2 ^ (prefixWord ++ tailWord_3536717).sum := by decide
  have hdescent : baseEnd_3536717 < baseStart_3536717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536723 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 8, 2, 2]
def baseStart_3536723 : Nat := 118140960795 + 3536723 * 2 ^ 59
def prefixEnd_3536723 : Nat := 4983230072969 + 3 ^ 40 * 3536723 * 2
def baseEnd_3536723 : Nat := 1816038840811471288697413

theorem tailTrace_3536723 : CollatzResearch.WordTrace tailWord_3536723 prefixEnd_3536723 1816038840811471288697413 := by
  unfold tailWord_3536723
  simp only [CollatzResearch.WordTrace]
  refine ⟨128994885166064070044686823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85996590110709380029791215 128994885166064070044686823)
  ·
    refine ⟨193492327749096105067030235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128994885166064070044686823 193492327749096105067030235)
    ·
      refine ⟨290238491623644157600545353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193492327749096105067030235 290238491623644157600545353)
      ·
        refine ⟨217678868717733118200409015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290238491623644157600545353 217678868717733118200409015)
        ·
          refine ⟨326518303076599677300613523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217678868717733118200409015 326518303076599677300613523)
          ·
            refine ⟨489777454614899515950920285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326518303076599677300613523 489777454614899515950920285)
            ·
              refine ⟨183666545480587318481595107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 489777454614899515950920285 183666545480587318481595107)
              ·
                refine ⟨275499818220880977722392661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183666545480587318481595107 275499818220880977722392661)
                ·
                  refine ⟨3228513494775948957684289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 275499818220880977722392661 3228513494775948957684289)
                  ·
                    refine ⟨2421385121081961718263217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3228513494775948957684289 2421385121081961718263217)
                    ·
                      refine ⟨1816038840811471288697413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2421385121081961718263217 1816038840811471288697413)
                      ·
                        rfl

theorem cell23_3536723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 8, 2, 2].length) (baseStart_3536723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536723 prefixEnd_3536723 := by exact prefixLift 3536723
  have htrace : WordTrace (prefixWord ++ tailWord_3536723) baseStart_3536723 baseEnd_3536723 := by
    simpa [prefixWord, tailWord_3536723, baseEnd_3536723] using wordTrace_append hprefix tailTrace_3536723
  have hstable : (prefixWord ++ tailWord_3536723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536723).length < 2 ^ (prefixWord ++ tailWord_3536723).sum := by decide
  have hdescent : baseEnd_3536723 < baseStart_3536723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536814 : List Nat := [4, 1, 5, 1, 1, 2, 1, 1, 7]
def baseStart_3536814 : Nat := 118140960795 + 3536814 * 2 ^ 59
def prefixEnd_3536814 : Nat := 4983230072969 + 3 ^ 40 * 3536814 * 2
def baseEnd_3536814 : Nat := 201787285283447825851055

theorem tailTrace_3536814 : CollatzResearch.WordTrace tailWord_3536814 prefixEnd_3536814 201787285283447825851055 := by
  unfold tailWord_3536814
  simp only [CollatzResearch.WordTrace]
  refine ⟨16124775526091799073281187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85998802805822928390832997 16124775526091799073281187)
  ·
    refine ⟨24187163289137698609921781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16124775526091799073281187 24187163289137698609921781)
    ·
      refine ⟨2267546558356659244680167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24187163289137698609921781 2267546558356659244680167)
      ·
        refine ⟨3401319837534988867020251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2267546558356659244680167 3401319837534988867020251)
        ·
          refine ⟨5101979756302483300530377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3401319837534988867020251 5101979756302483300530377)
          ·
            refine ⟨3826484817226862475397783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5101979756302483300530377 3826484817226862475397783)
            ·
              refine ⟨5739727225840293713096675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3826484817226862475397783 5739727225840293713096675)
              ·
                refine ⟨8609590838760440569645013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5739727225840293713096675 8609590838760440569645013)
                ·
                  refine ⟨201787285283447825851055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8609590838760440569645013 201787285283447825851055)
                  ·
                    rfl

theorem cell23_3536814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 7].length) (baseStart_3536814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536814 prefixEnd_3536814 := by exact prefixLift 3536814
  have htrace : WordTrace (prefixWord ++ tailWord_3536814) baseStart_3536814 baseEnd_3536814 := by
    simpa [prefixWord, tailWord_3536814, baseEnd_3536814] using wordTrace_append hprefix tailTrace_3536814
  have hstable : (prefixWord ++ tailWord_3536814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536814).length < 2 ^ (prefixWord ++ tailWord_3536814).sum := by decide
  have hdescent : baseEnd_3536814 < baseStart_3536814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536816 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 3]
def baseStart_3536816 : Nat := 118140960795 + 3536816 * 2 ^ 59
def prefixEnd_3536816 : Nat := 4983230072969 + 3 ^ 40 * 3536816 * 2
def baseEnd_3536816 : Nat := 1816086594512339424834485

theorem tailTrace_3536816 : CollatzResearch.WordTrace tailWord_3536816 prefixEnd_3536816 1816086594512339424834485 := by
  unfold tailWord_3536816
  simp only [CollatzResearch.WordTrace]
  refine ⟨64499138577363573463911151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85998851436484764618548201 64499138577363573463911151)
  ·
    refine ⟨96748707866045360195866727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64499138577363573463911151 96748707866045360195866727)
    ·
      refine ⟨145123061799068040293800091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96748707866045360195866727 145123061799068040293800091)
      ·
        refine ⟨217684592698602060440700137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145123061799068040293800091 217684592698602060440700137)
        ·
          refine ⟨163263444523951545330525103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217684592698602060440700137 163263444523951545330525103)
          ·
            refine ⟨244895166785927317995787655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163263444523951545330525103 244895166785927317995787655)
            ·
              refine ⟨367342750178890976993681483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244895166785927317995787655 367342750178890976993681483)
              ·
                refine ⟨551014125268336465490522225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367342750178890976993681483 551014125268336465490522225)
                ·
                  refine ⟨413260593951252349117891669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 551014125268336465490522225 413260593951252349117891669)
                  ·
                    refine ⟨4842897585366238466225293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 413260593951252349117891669 4842897585366238466225293)
                    ·
                      refine ⟨1816086594512339424834485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4842897585366238466225293 1816086594512339424834485)
                      ·
                        rfl

theorem cell23_3536816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 3].length) (baseStart_3536816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536816 prefixEnd_3536816 := by exact prefixLift 3536816
  have htrace : WordTrace (prefixWord ++ tailWord_3536816) baseStart_3536816 baseEnd_3536816 := by
    simpa [prefixWord, tailWord_3536816, baseEnd_3536816] using wordTrace_append hprefix tailTrace_3536816
  have hstable : (prefixWord ++ tailWord_3536816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536816).length < 2 ^ (prefixWord ++ tailWord_3536816).sum := by decide
  have hdescent : baseEnd_3536816 < baseStart_3536816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536826 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 2, 4, 4]
def baseStart_3536826 : Nat := 118140960795 + 3536826 * 2 ^ 59
def prefixEnd_3536826 : Nat := 4983230072969 + 3 ^ 40 * 3536826 * 2
def baseEnd_3536826 : Nat := 1816091729318884385709439

theorem tailTrace_3536826 : CollatzResearch.WordTrace tailWord_3536826 prefixEnd_3536826 1816091729318884385709439 := by
  unfold tailWord_3536826
  simp only [CollatzResearch.WordTrace]
  refine ⟨32249660471172729658921583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85999094589793945757124221 32249660471172729658921583)
  ·
    refine ⟨48374490706759094488382375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32249660471172729658921583 48374490706759094488382375)
    ·
      refine ⟨72561736060138641732573563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48374490706759094488382375 72561736060138641732573563)
      ·
        refine ⟨108842604090207962598860345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72561736060138641732573563 108842604090207962598860345)
        ·
          refine ⟨81631953067655971949145259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108842604090207962598860345 81631953067655971949145259)
          ·
            refine ⟨122447929601483957923717889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81631953067655971949145259 122447929601483957923717889)
            ·
              refine ⟨91835947201112968442788417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122447929601483957923717889 91835947201112968442788417)
              ·
                refine ⟨68876960400834726332091313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91835947201112968442788417 68876960400834726332091313)
                ·
                  refine ⟨51657720300626044749068485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68876960400834726332091313 51657720300626044749068485)
                  ·
                    refine ⟨9685822556367383390450341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51657720300626044749068485 9685822556367383390450341)
                    ·
                      refine ⟨1816091729318884385709439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9685822556367383390450341 1816091729318884385709439)
                      ·
                        rfl

theorem cell23_3536826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_3536826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536826 prefixEnd_3536826 := by exact prefixLift 3536826
  have htrace : WordTrace (prefixWord ++ tailWord_3536826) baseStart_3536826 baseEnd_3536826 := by
    simpa [prefixWord, tailWord_3536826, baseEnd_3536826] using wordTrace_append hprefix tailTrace_3536826
  have hstable : (prefixWord ++ tailWord_3536826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536826).length < 2 ^ (prefixWord ++ tailWord_3536826).sum := by decide
  have hdescent : baseEnd_3536826 < baseStart_3536826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536876 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 5]
def baseStart_3536876 : Nat := 118140960795 + 3536876 * 2 ^ 59
def prefixEnd_3536876 : Nat := 4983230072969 + 3 ^ 40 * 3536876 * 2
def baseEnd_3536876 : Nat := 1816117403351609190084209

theorem tailTrace_3536876 : CollatzResearch.WordTrace tailWord_3536876 prefixEnd_3536876 1816117403351609190084209 := by
  unfold tailWord_3536876
  simp only [CollatzResearch.WordTrace]
  refine ⟨64500232767254888587503241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86000310356339851450004321 64500232767254888587503241)
  ·
    refine ⟨48375174575441166440627431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64500232767254888587503241 48375174575441166440627431)
    ·
      refine ⟨72562761863161749660941147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48375174575441166440627431 72562761863161749660941147)
      ·
        refine ⟨108844142794742624491411721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72562761863161749660941147 108844142794742624491411721)
        ·
          refine ⟨81633107096056968368558791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108844142794742624491411721 81633107096056968368558791)
          ·
            refine ⟨122449660644085452552838187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81633107096056968368558791 122449660644085452552838187)
            ·
              refine ⟨183674490966128178829257281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122449660644085452552838187 183674490966128178829257281)
              ·
                refine ⟨137755868224596134121942961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183674490966128178829257281 137755868224596134121942961)
                ·
                  refine ⟨103316901168447100591457221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137755868224596134121942961 103316901168447100591457221)
                  ·
                    refine ⟨19371918969083831360898229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103316901168447100591457221 19371918969083831360898229)
                    ·
                      refine ⟨1816117403351609190084209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19371918969083831360898229 1816117403351609190084209)
                      ·
                        rfl

theorem cell23_3536876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_3536876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536876 prefixEnd_3536876 := by exact prefixLift 3536876
  have htrace : WordTrace (prefixWord ++ tailWord_3536876) baseStart_3536876 baseEnd_3536876 := by
    simpa [prefixWord, tailWord_3536876, baseEnd_3536876] using wordTrace_append hprefix tailTrace_3536876
  have hstable : (prefixWord ++ tailWord_3536876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536876).length < 2 ^ (prefixWord ++ tailWord_3536876).sum := by decide
  have hdescent : baseEnd_3536876 < baseStart_3536876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536920 : List Nat := [2, 1, 2, 3, 2, 1, 3, 3, 1, 1, 4]
def baseStart_3536920 : Nat := 118140960795 + 3536920 * 2 ^ 59
def prefixEnd_3536920 : Nat := 4983230072969 + 3 ^ 40 * 3536920 * 2
def baseEnd_3536920 : Nat := 1816139996500407017934007

theorem tailTrace_3536920 : CollatzResearch.WordTrace tailWord_3536920 prefixEnd_3536920 1816139996500407017934007 := by
  unfold tailWord_3536920
  simp only [CollatzResearch.WordTrace]
  refine ⟨64501035173175186344804107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86001380230900248459738809 64501035173175186344804107)
  ·
    refine ⟨96751552759762779517206161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64501035173175186344804107 96751552759762779517206161)
    ·
      refine ⟨72563664569822084637904621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96751552759762779517206161 72563664569822084637904621)
      ·
        refine ⟨27211374213683281739214233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72563664569822084637904621 27211374213683281739214233)
        ·
          refine ⟨20408530660262461304410675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27211374213683281739214233 20408530660262461304410675)
          ·
            refine ⟨30612795990393691956616013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20408530660262461304410675 30612795990393691956616013)
            ·
              refine ⟨11479798496397634483731005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30612795990393691956616013 11479798496397634483731005)
              ·
                refine ⟨4304924436149112931399127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11479798496397634483731005 4304924436149112931399127)
                ·
                  refine ⟨6457386654223669397098691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4304924436149112931399127 6457386654223669397098691)
                  ·
                    refine ⟨9686079981335504095648037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6457386654223669397098691 9686079981335504095648037)
                    ·
                      refine ⟨1816139996500407017934007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9686079981335504095648037 1816139996500407017934007)
                      ·
                        rfl

theorem cell23_3536920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_3536920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536920 prefixEnd_3536920 := by exact prefixLift 3536920
  have htrace : WordTrace (prefixWord ++ tailWord_3536920) baseStart_3536920 baseEnd_3536920 := by
    simpa [prefixWord, tailWord_3536920, baseEnd_3536920] using wordTrace_append hprefix tailTrace_3536920
  have hstable : (prefixWord ++ tailWord_3536920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536920).length < 2 ^ (prefixWord ++ tailWord_3536920).sum := by decide
  have hdescent : baseEnd_3536920 < baseStart_3536920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536923 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 5, 2, 3]
def baseStart_3536923 : Nat := 118140960795 + 3536923 * 2 ^ 59
def prefixEnd_3536923 : Nat := 4983230072969 + 3 ^ 40 * 3536923 * 2
def baseEnd_3536923 : Nat := 1816141536942370506196493

theorem tailTrace_3536923 : CollatzResearch.WordTrace tailWord_3536923 prefixEnd_3536923 1816141536942370506196493 := by
  unfold tailWord_3536923
  simp only [CollatzResearch.WordTrace]
  refine ⟨129002179765339504201967423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86001453176893002801311615 129002179765339504201967423)
  ·
    refine ⟨193503269648009256302951135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129002179765339504201967423 193503269648009256302951135)
    ·
      refine ⟨290254904472013884454426703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193503269648009256302951135 290254904472013884454426703)
      ·
        refine ⟨435382356708020826681640055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290254904472013884454426703 435382356708020826681640055)
        ·
          refine ⟨653073535062031240022460083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435382356708020826681640055 653073535062031240022460083)
          ·
            refine ⟨979610302593046860033690125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653073535062031240022460083 979610302593046860033690125)
            ·
              refine ⟨367353863472392572512633797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 979610302593046860033690125 367353863472392572512633797)
              ·
                refine ⟨68878849401073607346118837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 367353863472392572512633797 68878849401073607346118837)
                ·
                  refine ⟨6457392131350650688698641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68878849401073607346118837 6457392131350650688698641)
                  ·
                    refine ⟨4843044098512988016523981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6457392131350650688698641 4843044098512988016523981)
                    ·
                      refine ⟨1816141536942370506196493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4843044098512988016523981 1816141536942370506196493)
                      ·
                        rfl

theorem cell23_3536923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 2, 3].length) (baseStart_3536923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536923 prefixEnd_3536923 := by exact prefixLift 3536923
  have htrace : WordTrace (prefixWord ++ tailWord_3536923) baseStart_3536923 baseEnd_3536923 := by
    simpa [prefixWord, tailWord_3536923, baseEnd_3536923] using wordTrace_append hprefix tailTrace_3536923
  have hstable : (prefixWord ++ tailWord_3536923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536923).length < 2 ^ (prefixWord ++ tailWord_3536923).sum := by decide
  have hdescent : baseEnd_3536923 < baseStart_3536923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536930 : List Nat := [3, 3, 1, 1, 1, 2, 3, 1, 4, 4]
def baseStart_3536930 : Nat := 118140960795 + 3536930 * 2 ^ 59
def prefixEnd_3536930 : Nat := 4983230072969 + 3 ^ 40 * 3536930 * 2
def baseEnd_3536930 : Nat := 605381710435650659602987

theorem tailTrace_3536930 : CollatzResearch.WordTrace tailWord_3536930 prefixEnd_3536930 605381710435650659602987 := by
  unfold tailWord_3536930
  simp only [CollatzResearch.WordTrace]
  refine ⟨32250608769078536099368061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86001623384209429598314829 32250608769078536099368061)
  ·
    refine ⟨12093978288404451037263023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32250608769078536099368061 12093978288404451037263023)
    ·
      refine ⟨18140967432606676555894535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12093978288404451037263023 18140967432606676555894535)
      ·
        refine ⟨27211451148910014833841803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18140967432606676555894535 27211451148910014833841803)
        ·
          refine ⟨40817176723365022250762705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27211451148910014833841803 40817176723365022250762705)
          ·
            refine ⟨30612882542523766688072029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40817176723365022250762705 30612882542523766688072029)
            ·
              refine ⟨11479830953446412508027011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30612882542523766688072029 11479830953446412508027011)
              ·
                refine ⟨17219746430169618762040517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11479830953446412508027011 17219746430169618762040517)
                ·
                  refine ⟨3228702455656803517882597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17219746430169618762040517 3228702455656803517882597)
                  ·
                    refine ⟨605381710435650659602987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3228702455656803517882597 605381710435650659602987)
                    ·
                      rfl

theorem cell23_3536930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_3536930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536930 prefixEnd_3536930 := by exact prefixLift 3536930
  have htrace : WordTrace (prefixWord ++ tailWord_3536930) baseStart_3536930 baseEnd_3536930 := by
    simpa [prefixWord, tailWord_3536930, baseEnd_3536930] using wordTrace_append hprefix tailTrace_3536930
  have hstable : (prefixWord ++ tailWord_3536930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536930).length < 2 ^ (prefixWord ++ tailWord_3536930).sum := by decide
  have hdescent : baseEnd_3536930 < baseStart_3536930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536950 : List Nat := [5, 1, 2, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_3536950 : Nat := 118140960795 + 3536950 * 2 ^ 59
def prefixEnd_3536950 : Nat := 4983230072969 + 3 ^ 40 * 3536950 * 2
def baseEnd_3536950 : Nat := 1816155400920041900558869

theorem tailTrace_3536950 : CollatzResearch.WordTrace tailWord_3536950 prefixEnd_3536950 1816155400920041900558869 := by
  unfold tailWord_3536950
  simp only [CollatzResearch.WordTrace]
  refine ⟨8062697783515105488325019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86002109690827791875466869 8062697783515105488325019)
  ·
    refine ⟨12094046675272658232487529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8062697783515105488325019 12094046675272658232487529)
    ·
      refine ⟨9070535006454493674365647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12094046675272658232487529 9070535006454493674365647)
      ·
        refine ⟨13605802509681740511548471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9070535006454493674365647 13605802509681740511548471)
        ·
          refine ⟨20408703764522610767322707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13605802509681740511548471 20408703764522610767322707)
          ·
            refine ⟨30613055646783916150984061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20408703764522610767322707 30613055646783916150984061)
            ·
              refine ⟨11479895867543968556619023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30613055646783916150984061 11479895867543968556619023)
              ·
                refine ⟨17219843801315952834928535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11479895867543968556619023 17219843801315952834928535)
                ·
                  refine ⟨25829765701973929252392803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17219843801315952834928535 25829765701973929252392803)
                  ·
                    refine ⟨38744648552960893878589205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25829765701973929252392803 38744648552960893878589205)
                    ·
                      refine ⟨1816155400920041900558869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38744648552960893878589205 1816155400920041900558869)
                      ·
                        rfl

theorem cell23_3536950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_3536950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536950 prefixEnd_3536950 := by exact prefixLift 3536950
  have htrace : WordTrace (prefixWord ++ tailWord_3536950) baseStart_3536950 baseEnd_3536950 := by
    simpa [prefixWord, tailWord_3536950, baseEnd_3536950] using wordTrace_append hprefix tailTrace_3536950
  have hstable : (prefixWord ++ tailWord_3536950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536950).length < 2 ^ (prefixWord ++ tailWord_3536950).sum := by decide
  have hdescent : baseEnd_3536950 < baseStart_3536950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536957 : List Nat := [1, 4, 1, 3, 1, 1, 4, 2, 1, 2, 3]
def baseStart_3536957 : Nat := 118140960795 + 3536957 * 2 ^ 59
def prefixEnd_3536957 : Nat := 4983230072969 + 3 ^ 40 * 3536957 * 2
def baseEnd_3536957 : Nat := 1816158995284623373171337

theorem tailTrace_3536957 : CollatzResearch.WordTrace tailWord_3536957 prefixEnd_3536957 1816158995284623373171337 := by
  unfold tailWord_3536957
  simp only [CollatzResearch.WordTrace]
  refine ⟨129003419847216328008705125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86002279898144218672470083 129003419847216328008705125)
  ·
    refine ⟨24188141221353061501632211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129003419847216328008705125 24188141221353061501632211)
    ·
      refine ⟨36282211832029592252448317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24188141221353061501632211 36282211832029592252448317)
      ·
        refine ⟨13605829437011097094668119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36282211832029592252448317 13605829437011097094668119)
        ·
          refine ⟨20408744155516645642002179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13605829437011097094668119 20408744155516645642002179)
          ·
            refine ⟨30613116233274968463003269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20408744155516645642002179 30613116233274968463003269)
            ·
              refine ⟨5739959293739056586813113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30613116233274968463003269 5739959293739056586813113)
              ·
                refine ⟨4304969470304292440109835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5739959293739056586813113 4304969470304292440109835)
                ·
                  refine ⟨6457454205456438660164753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4304969470304292440109835 6457454205456438660164753)
                  ·
                    refine ⟨4843090654092328995123565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6457454205456438660164753 4843090654092328995123565)
                    ·
                      refine ⟨1816158995284623373171337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4843090654092328995123565 1816158995284623373171337)
                      ·
                        rfl

theorem cell23_3536957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_3536957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536957 prefixEnd_3536957 := by exact prefixLift 3536957
  have htrace : WordTrace (prefixWord ++ tailWord_3536957) baseStart_3536957 baseEnd_3536957 := by
    simpa [prefixWord, tailWord_3536957, baseEnd_3536957] using wordTrace_append hprefix tailTrace_3536957
  have hstable : (prefixWord ++ tailWord_3536957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536957).length < 2 ^ (prefixWord ++ tailWord_3536957).sum := by decide
  have hdescent : baseEnd_3536957 < baseStart_3536957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536960 : List Nat := [2, 1, 1, 2, 2, 6, 2, 7]
def baseStart_3536960 : Nat := 118140960795 + 3536960 * 2 ^ 59
def prefixEnd_3536960 : Nat := 4983230072969 + 3 ^ 40 * 3536960 * 2
def baseEnd_3536960 : Nat := 67265205026910624497549

theorem tailTrace_3536960 : CollatzResearch.WordTrace tailWord_3536960 prefixEnd_3536960 67265205026910624497549 := by
  unfold tailWord_3536960
  simp only [CollatzResearch.WordTrace]
  refine ⟨64501764633102729760532167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86002352844136973014042889 64501764633102729760532167)
  ·
    refine ⟨96752646949654094640798251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64501764633102729760532167 96752646949654094640798251)
    ·
      refine ⟨145128970424481141961197377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96752646949654094640798251 145128970424481141961197377)
      ·
        refine ⟨108846727818360856470898033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145128970424481141961197377 108846727818360856470898033)
        ·
          refine ⟨81635045863770642353173525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108846727818360856470898033 81635045863770642353173525)
          ·
            refine ⟨3826642774864248860305009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 81635045863770642353173525 3826642774864248860305009)
            ·
              refine ⟨2869982081148186645228757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3826642774864248860305009 2869982081148186645228757)
              ·
                refine ⟨67265205026910624497549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2869982081148186645228757 67265205026910624497549)
                ·
                  rfl

theorem cell23_3536960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 7].length) (baseStart_3536960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536960 prefixEnd_3536960 := by exact prefixLift 3536960
  have htrace : WordTrace (prefixWord ++ tailWord_3536960) baseStart_3536960 baseEnd_3536960 := by
    simpa [prefixWord, tailWord_3536960, baseEnd_3536960] using wordTrace_append hprefix tailTrace_3536960
  have hstable : (prefixWord ++ tailWord_3536960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536960).length < 2 ^ (prefixWord ++ tailWord_3536960).sum := by decide
  have hdescent : baseEnd_3536960 < baseStart_3536960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536988 : List Nat := [2, 2, 4, 1, 1, 3, 3, 2, 1, 2, 2]
def baseStart_3536988 : Nat := 118140960795 + 3536988 * 2 ^ 59
def prefixEnd_3536988 : Nat := 4983230072969 + 3 ^ 40 * 3536988 * 2
def baseEnd_3536988 : Nat := 1816174913184912751883695

theorem tailTrace_3536988 : CollatzResearch.WordTrace tailWord_3536988 prefixEnd_3536988 1816174913184912751883695 := by
  unfold tailWord_3536988
  simp only [CollatzResearch.WordTrace]
  refine ⟨64502275255052010151541809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86003033673402680202055745 64502275255052010151541809)
  ·
    refine ⟨48376706441289007613656357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64502275255052010151541809 48376706441289007613656357)
    ·
      refine ⟨9070632457741688927560567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48376706441289007613656357 9070632457741688927560567)
      ·
        refine ⟨13605948686612533391340851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9070632457741688927560567 13605948686612533391340851)
        ·
          refine ⟨20408923029918800087011277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13605948686612533391340851 20408923029918800087011277)
          ·
            refine ⟨7653346136219550032629229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20408923029918800087011277 7653346136219550032629229)
            ·
              refine ⟨2870004801082331262235961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7653346136219550032629229 2870004801082331262235961)
              ·
                refine ⟨2152503600811748446676971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2870004801082331262235961 2152503600811748446676971)
                ·
                  refine ⟨3228755401217622670015457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2152503600811748446676971 3228755401217622670015457)
                  ·
                    refine ⟨2421566550913217002511593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3228755401217622670015457 2421566550913217002511593)
                    ·
                      refine ⟨1816174913184912751883695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2421566550913217002511593 1816174913184912751883695)
                      ·
                        rfl

theorem cell23_3536988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_3536988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536988 prefixEnd_3536988 := by exact prefixLift 3536988
  have htrace : WordTrace (prefixWord ++ tailWord_3536988) baseStart_3536988 baseEnd_3536988 := by
    simpa [prefixWord, tailWord_3536988, baseEnd_3536988] using wordTrace_append hprefix tailTrace_3536988
  have hstable : (prefixWord ++ tailWord_3536988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536988).length < 2 ^ (prefixWord ++ tailWord_3536988).sum := by decide
  have hdescent : baseEnd_3536988 < baseStart_3536988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536993 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 2, 3, 4]
def baseStart_3536993 : Nat := 118140960795 + 3536993 * 2 ^ 59
def prefixEnd_3536993 : Nat := 4983230072969 + 3 ^ 40 * 3536993 * 2
def baseEnd_3536993 : Nat := 1816177480588185232321171

theorem tailTrace_3536993 : CollatzResearch.WordTrace tailWord_3536993 prefixEnd_3536993 1816177480588185232321171 := by
  unfold tailWord_3536993
  simp only [CollatzResearch.WordTrace]
  refine ⟨129004732875085906157015633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86003155250057270771343755 129004732875085906157015633)
  ·
    refine ⟨96753549656314429617761725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129004732875085906157015633 96753549656314429617761725)
    ·
      refine ⟨36282581121117911106660647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96753549656314429617761725 36282581121117911106660647)
      ·
        refine ⟨54423871681676866659990971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36282581121117911106660647 54423871681676866659990971)
        ·
          refine ⟨81635807522515299989986457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54423871681676866659990971 81635807522515299989986457)
          ·
            refine ⟨61226855641886474992489843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81635807522515299989986457 61226855641886474992489843)
            ·
              refine ⟨91840283462829712488734765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61226855641886474992489843 91840283462829712488734765)
              ·
                refine ⟨34440106298561142183275537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91840283462829712488734765 34440106298561142183275537)
                ·
                  refine ⟨25830079723920856637456653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34440106298561142183275537 25830079723920856637456653)
                  ·
                    refine ⟨9686279896470321239046245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25830079723920856637456653 9686279896470321239046245)
                    ·
                      refine ⟨1816177480588185232321171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9686279896470321239046245 1816177480588185232321171)
                      ·
                        rfl

theorem cell23_3536993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_3536993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3536993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3536993 prefixEnd_3536993 := by exact prefixLift 3536993
  have htrace : WordTrace (prefixWord ++ tailWord_3536993) baseStart_3536993 baseEnd_3536993 := by
    simpa [prefixWord, tailWord_3536993, baseEnd_3536993] using wordTrace_append hprefix tailTrace_3536993
  have hstable : (prefixWord ++ tailWord_3536993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536993).length < 2 ^ (prefixWord ++ tailWord_3536993).sum := by decide
  have hdescent : baseEnd_3536993 < baseStart_3536993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537004 : List Nat := [2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 3]
def baseStart_3537004 : Nat := 118140960795 + 3537004 * 2 ^ 59
def prefixEnd_3537004 : Nat := 4983230072969 + 3 ^ 40 * 3537004 * 2
def baseEnd_3537004 : Nat := 1816183128875384689283621

theorem tailTrace_3537004 : CollatzResearch.WordTrace tailWord_3537004 prefixEnd_3537004 1816183128875384689283621 := by
  unfold tailWord_3537004
  simp only [CollatzResearch.WordTrace]
  refine ⟨64502567039023027517833033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86003422718697370023777377 64502567039023027517833033)
  ·
    refine ⟨48376925279267270638374775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64502567039023027517833033 48376925279267270638374775)
    ·
      refine ⟨72565387918900905957562163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48376925279267270638374775 72565387918900905957562163)
      ·
        refine ⟨108848081878351358936343245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72565387918900905957562163 108848081878351358936343245)
        ·
          refine ⟨40818030704381759601128717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108848081878351358936343245 40818030704381759601128717)
          ·
            refine ⟨15306761514143159850423269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40818030704381759601128717 15306761514143159850423269)
            ·
              refine ⟨2870017783901842471954363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15306761514143159850423269 2870017783901842471954363)
              ·
                refine ⟨4305026675852763707931545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2870017783901842471954363 4305026675852763707931545)
                ·
                  refine ⟨3228770006889572780948659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4305026675852763707931545 3228770006889572780948659)
                  ·
                    refine ⟨4843155010334359171422989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3228770006889572780948659 4843155010334359171422989)
                    ·
                      refine ⟨1816183128875384689283621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4843155010334359171422989 1816183128875384689283621)
                      ·
                        rfl

theorem cell23_3537004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 3].length) (baseStart_3537004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537004 prefixEnd_3537004 := by exact prefixLift 3537004
  have htrace : WordTrace (prefixWord ++ tailWord_3537004) baseStart_3537004 baseEnd_3537004 := by
    simpa [prefixWord, tailWord_3537004, baseEnd_3537004] using wordTrace_append hprefix tailTrace_3537004
  have hstable : (prefixWord ++ tailWord_3537004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537004).length < 2 ^ (prefixWord ++ tailWord_3537004).sum := by decide
  have hdescent : baseEnd_3537004 < baseStart_3537004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537014 : List Nat := [5, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2]
def baseStart_3537014 : Nat := 118140960795 + 3537014 * 2 ^ 59
def prefixEnd_3537014 : Nat := 4983230072969 + 3 ^ 40 * 3537014 * 2
def baseEnd_3537014 : Nat := 1816188263681929650158575

theorem tailTrace_3537014 : CollatzResearch.WordTrace tailWord_3537014 prefixEnd_3537014 1816188263681929650158575 := by
  unfold tailWord_3537014
  simp only [CollatzResearch.WordTrace]
  refine ⟨8062843675500614171470631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86003665872006551162353397 8062843675500614171470631)
  ·
    refine ⟨12094265513250921257205947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8062843675500614171470631 12094265513250921257205947)
    ·
      refine ⟨18141398269876381885808921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12094265513250921257205947 18141398269876381885808921)
      ·
        refine ⟨13606048702407286414356691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18141398269876381885808921 13606048702407286414356691)
        ·
          refine ⟨20409073053610929621535037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13606048702407286414356691 20409073053610929621535037)
          ·
            refine ⟨7653402395104098608075639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20409073053610929621535037 7653402395104098608075639)
            ·
              refine ⟨11480103592656147912113459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7653402395104098608075639 11480103592656147912113459)
              ·
                refine ⟨17220155388984221868170189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11480103592656147912113459 17220155388984221868170189)
                ·
                  refine ⟨6457558270869083200563821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17220155388984221868170189 6457558270869083200563821)
                  ·
                    refine ⟨2421584351575906200211433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6457558270869083200563821 2421584351575906200211433)
                    ·
                      refine ⟨1816188263681929650158575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2421584351575906200211433 1816188263681929650158575)
                      ·
                        rfl

theorem cell23_3537014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_3537014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537014 prefixEnd_3537014 := by exact prefixLift 3537014
  have htrace : WordTrace (prefixWord ++ tailWord_3537014) baseStart_3537014 baseEnd_3537014 := by
    simpa [prefixWord, tailWord_3537014, baseEnd_3537014] using wordTrace_append hprefix tailTrace_3537014
  have hstable : (prefixWord ++ tailWord_3537014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537014).length < 2 ^ (prefixWord ++ tailWord_3537014).sum := by decide
  have hdescent : baseEnd_3537014 < baseStart_3537014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537027 : List Nat := [1, 1, 1, 3, 3, 4, 1, 2, 1, 4, 2]
def baseStart_3537027 : Nat := 118140960795 + 3537027 * 2 ^ 59
def prefixEnd_3537027 : Nat := 4983230072969 + 3 ^ 40 * 3537027 * 2
def baseEnd_3537027 : Nat := 1816194938930438099296015

theorem tailTrace_3537027 : CollatzResearch.WordTrace tailWord_3537027 prefixEnd_3537027 1816194938930438099296015 := by
  unfold tailWord_3537027
  simp only [CollatzResearch.WordTrace]
  refine ⟨129005972956962729963753335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86003981971308486642502223 129005972956962729963753335)
  ·
    refine ⟨193508959435444094945630003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129005972956962729963753335 193508959435444094945630003)
    ·
      refine ⟨290263439153166142418445005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193508959435444094945630003 290263439153166142418445005)
      ·
        refine ⟨108848789682437303406916877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290263439153166142418445005 108848789682437303406916877)
        ·
          refine ⟨40818296130913988777593829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108848789682437303406916877 40818296130913988777593829)
          ·
            refine ⟨7653430524546372895798843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40818296130913988777593829 7653430524546372895798843)
            ·
              refine ⟨11480145786819559343698265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7653430524546372895798843 11480145786819559343698265)
              ·
                refine ⟨8610109340114669507773699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11480145786819559343698265 8610109340114669507773699)
                ·
                  refine ⟨12915164010172004261660549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8610109340114669507773699 12915164010172004261660549)
                  ·
                    refine ⟨2421593251907250799061353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12915164010172004261660549 2421593251907250799061353)
                    ·
                      refine ⟨1816194938930438099296015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2421593251907250799061353 1816194938930438099296015)
                      ·
                        rfl

theorem cell23_3537027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 4, 2].length) (baseStart_3537027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537027 prefixEnd_3537027 := by exact prefixLift 3537027
  have htrace : WordTrace (prefixWord ++ tailWord_3537027) baseStart_3537027 baseEnd_3537027 := by
    simpa [prefixWord, tailWord_3537027, baseEnd_3537027] using wordTrace_append hprefix tailTrace_3537027
  have hstable : (prefixWord ++ tailWord_3537027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537027).length < 2 ^ (prefixWord ++ tailWord_3537027).sum := by decide
  have hdescent : baseEnd_3537027 < baseStart_3537027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537084 : List Nat := [2, 2, 2, 3, 3, 1, 2, 3, 5]
def baseStart_3537084 : Nat := 118140960795 + 3537084 * 2 ^ 59
def prefixEnd_3537084 : Nat := 4983230072969 + 3 ^ 40 * 3537084 * 2
def baseEnd_3537084 : Nat := 201802689703082708475917

theorem tailTrace_3537084 : CollatzResearch.WordTrace tailWord_3537084 prefixEnd_3537084 201802689703082708475917 := by
  unfold tailWord_3537084
  simp only [CollatzResearch.WordTrace]
  refine ⟨64504025958878114349289153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86005367945170819132385537 64504025958878114349289153)
  ·
    refine ⟨48378019469158585761966865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64504025958878114349289153 48378019469158585761966865)
    ·
      refine ⟨36283514601868939321475149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48378019469158585761966865 36283514601868939321475149)
      ·
        refine ⟨13606317975700852245553181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36283514601868939321475149 13606317975700852245553181)
        ·
          refine ⟨5102369240887819592082443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13606317975700852245553181 5102369240887819592082443)
          ·
            refine ⟨7653553861331729388123665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5102369240887819592082443 7653553861331729388123665)
            ·
              refine ⟨5740165395998797041092749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7653553861331729388123665 5740165395998797041092749)
              ·
                refine ⟨2152562023499548890409781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5740165395998797041092749 2152562023499548890409781)
                ·
                  refine ⟨201802689703082708475917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2152562023499548890409781 201802689703082708475917)
                  ·
                    rfl

theorem cell23_3537084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 3, 5].length) (baseStart_3537084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537084 prefixEnd_3537084 := by exact prefixLift 3537084
  have htrace : WordTrace (prefixWord ++ tailWord_3537084) baseStart_3537084 baseEnd_3537084 := by
    simpa [prefixWord, tailWord_3537084, baseEnd_3537084] using wordTrace_append hprefix tailTrace_3537084
  have hstable : (prefixWord ++ tailWord_3537084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537084).length < 2 ^ (prefixWord ++ tailWord_3537084).sum := by decide
  have hdescent : baseEnd_3537084 < baseStart_3537084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537117 : List Nat := [1, 4, 3, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_3537117 : Nat := 118140960795 + 3537117 * 2 ^ 59
def prefixEnd_3537117 : Nat := 4983230072969 + 3 ^ 40 * 3537117 * 2
def baseEnd_3537117 : Nat := 1816241152189342747170601

theorem tailTrace_3537117 : CollatzResearch.WordTrace tailWord_3537117 prefixEnd_3537117 1816241152189342747170601 := by
  unfold tailWord_3537117
  simp only [CollatzResearch.WordTrace]
  refine ⟨129009255526636675334529605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86006170351091116889686403 129009255526636675334529605)
  ·
    refine ⟨24189235411244376625224301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129009255526636675334529605 24189235411244376625224301)
    ·
      refine ⟨9070963279216641234459113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24189235411244376625224301 9070963279216641234459113)
      ·
        refine ⟨6803222459412480925844335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9070963279216641234459113 6803222459412480925844335)
        ·
          refine ⟨10204833689118721388766503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6803222459412480925844335 10204833689118721388766503)
          ·
            refine ⟨15307250533678082083149755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10204833689118721388766503 15307250533678082083149755)
            ·
              refine ⟨22960875800517123124724633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15307250533678082083149755 22960875800517123124724633)
              ·
                refine ⟨17220656850387842343543475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22960875800517123124724633 17220656850387842343543475)
                ·
                  refine ⟨25830985275581763515315213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17220656850387842343543475 25830985275581763515315213)
                  ·
                    refine ⟨9686619478343161318243205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25830985275581763515315213 9686619478343161318243205)
                    ·
                      refine ⟨1816241152189342747170601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9686619478343161318243205 1816241152189342747170601)
                      ·
                        rfl

theorem cell23_3537117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_3537117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537117 prefixEnd_3537117 := by exact prefixLift 3537117
  have htrace : WordTrace (prefixWord ++ tailWord_3537117) baseStart_3537117 baseEnd_3537117 := by
    simpa [prefixWord, tailWord_3537117, baseEnd_3537117] using wordTrace_append hprefix tailTrace_3537117
  have hstable : (prefixWord ++ tailWord_3537117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537117).length < 2 ^ (prefixWord ++ tailWord_3537117).sum := by decide
  have hdescent : baseEnd_3537117 < baseStart_3537117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537120 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 3]
def baseStart_3537120 : Nat := 118140960795 + 3537120 * 2 ^ 59
def prefixEnd_3537120 : Nat := 4983230072969 + 3 ^ 40 * 3537120 * 2
def baseEnd_3537120 : Nat := 1816242692631306235433087

theorem tailTrace_3537120 : CollatzResearch.WordTrace tailWord_3537120 prefixEnd_3537120 1816242692631306235433087 := by
  unfold tailWord_3537120
  simp only [CollatzResearch.WordTrace]
  refine ⟨64504682472812903423444407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86006243297083871231259209 64504682472812903423444407)
  ·
    refine ⟨96757023709219355135166611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64504682472812903423444407 96757023709219355135166611)
    ·
      refine ⟨145135535563829032702749917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96757023709219355135166611 145135535563829032702749917)
      ·
        refine ⟨54425825836435887263531219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145135535563829032702749917 54425825836435887263531219)
        ·
          refine ⟨81638738754653830895296829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54425825836435887263531219 81638738754653830895296829)
          ·
            refine ⟨30614527032995186585736311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81638738754653830895296829 30614527032995186585736311)
            ·
              refine ⟨45921790549492779878604467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30614527032995186585736311 45921790549492779878604467)
              ·
                refine ⟨68882685824239169817906701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45921790549492779878604467 68882685824239169817906701)
                ·
                  refine ⟨25831007184089688681715013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68882685824239169817906701 25831007184089688681715013)
                  ·
                    refine ⟨4843313847016816627821565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25831007184089688681715013 4843313847016816627821565)
                    ·
                      refine ⟨1816242692631306235433087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4843313847016816627821565 1816242692631306235433087)
                      ·
                        rfl

theorem cell23_3537120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_3537120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537120 prefixEnd_3537120 := by exact prefixLift 3537120
  have htrace : WordTrace (prefixWord ++ tailWord_3537120) baseStart_3537120 baseEnd_3537120 := by
    simpa [prefixWord, tailWord_3537120, baseEnd_3537120] using wordTrace_append hprefix tailTrace_3537120
  have hstable : (prefixWord ++ tailWord_3537120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537120).length < 2 ^ (prefixWord ++ tailWord_3537120).sum := by decide
  have hdescent : baseEnd_3537120 < baseStart_3537120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537130 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 2, 4, 4]
def baseStart_3537130 : Nat := 118140960795 + 3537130 * 2 ^ 59
def prefixEnd_3537130 : Nat := 4983230072969 + 3 ^ 40 * 3537130 * 2
def baseEnd_3537130 : Nat := 1816247827437851196308041

theorem tailTrace_3537130 : CollatzResearch.WordTrace tailWord_3537130 prefixEnd_3537130 1816247827437851196308041 := by
  unfold tailWord_3537130
  simp only [CollatzResearch.WordTrace]
  refine ⟨32252432418897394638688211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86006486450393052369835229 32252432418897394638688211)
  ·
    refine ⟨48378648628346091958032317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32252432418897394638688211 48378648628346091958032317)
    ·
      refine ⟨18141993235629784484262119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48378648628346091958032317 18141993235629784484262119)
      ·
        refine ⟨27212989853444676726393179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18141993235629784484262119 27212989853444676726393179)
        ·
          refine ⟨40819484780167015089589769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27212989853444676726393179 40819484780167015089589769)
          ·
            refine ⟨30614613585125261317192327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40819484780167015089589769 30614613585125261317192327)
            ·
              refine ⟨45921920377687891975788491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30614613585125261317192327 45921920377687891975788491)
              ·
                refine ⟨68882880566531837963682737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45921920377687891975788491 68882880566531837963682737)
                ·
                  refine ⟨51662160424898878472762053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68882880566531837963682737 51662160424898878472762053)
                  ·
                    refine ⟨9686655079668539713642885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51662160424898878472762053 9686655079668539713642885)
                    ·
                      refine ⟨1816247827437851196308041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9686655079668539713642885 1816247827437851196308041)
                      ·
                        rfl

theorem cell23_3537130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_3537130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537130 prefixEnd_3537130 := by exact prefixLift 3537130
  have htrace : WordTrace (prefixWord ++ tailWord_3537130) baseStart_3537130 baseEnd_3537130 := by
    simpa [prefixWord, tailWord_3537130, baseEnd_3537130] using wordTrace_append hprefix tailTrace_3537130
  have hstable : (prefixWord ++ tailWord_3537130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537130).length < 2 ^ (prefixWord ++ tailWord_3537130).sum := by decide
  have hdescent : baseEnd_3537130 < baseStart_3537130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537154 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 4, 2, 3]
def baseStart_3537154 : Nat := 118140960795 + 3537154 * 2 ^ 59
def prefixEnd_3537154 : Nat := 4983230072969 + 3 ^ 40 * 3537154 * 2
def baseEnd_3537154 : Nat := 1816260150973559102407931

theorem tailTrace_3537154 : CollatzResearch.WordTrace tailWord_3537154 prefixEnd_3537154 1816260150973559102407931 := by
  unfold tailWord_3537154
  simp only [CollatzResearch.WordTrace]
  refine ⟨32252651256875657663406629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86007070018335087102417677 32252651256875657663406629)
  ·
    refine ⟨6047372110664185811888743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32252651256875657663406629 6047372110664185811888743)
    ·
      refine ⟨9071058165996278717833115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6047372110664185811888743 9071058165996278717833115)
      ·
        refine ⟨13606587248994418076749673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9071058165996278717833115 13606587248994418076749673)
        ·
          refine ⟨10204940436745813557562255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13606587248994418076749673 10204940436745813557562255)
          ·
            refine ⟨15307410655118720336343383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10204940436745813557562255 15307410655118720336343383)
            ·
              refine ⟨22961115982678080504515075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15307410655118720336343383 22961115982678080504515075)
              ·
                refine ⟨34441673974017120756772613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22961115982678080504515075 34441673974017120756772613)
                ·
                  refine ⟨6457813870128210141894865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34441673974017120756772613 6457813870128210141894865)
                  ·
                    refine ⟨4843360402596157606421149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6457813870128210141894865 4843360402596157606421149)
                    ·
                      refine ⟨1816260150973559102407931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4843360402596157606421149 1816260150973559102407931)
                      ·
                        rfl

theorem cell23_3537154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_3537154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537154 prefixEnd_3537154 := by exact prefixLift 3537154
  have htrace : WordTrace (prefixWord ++ tailWord_3537154) baseStart_3537154 baseEnd_3537154 := by
    simpa [prefixWord, tailWord_3537154, baseEnd_3537154] using wordTrace_append hprefix tailTrace_3537154
  have hstable : (prefixWord ++ tailWord_3537154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537154).length < 2 ^ (prefixWord ++ tailWord_3537154).sum := by decide
  have hdescent : baseEnd_3537154 < baseStart_3537154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537161 : List Nat := [1, 2, 1, 1, 3, 5, 3, 2, 1, 4]
def baseStart_3537161 : Nat := 118140960795 + 3537161 * 2 ^ 59
def prefixEnd_3537161 : Nat := 4983230072969 + 3 ^ 40 * 3537161 * 2
def baseEnd_3537161 : Nat := 605421248446046858340133

theorem tailTrace_3537161 : CollatzResearch.WordTrace tailWord_3537161 prefixEnd_3537161 605421248446046858340133 := by
  unfold tailWord_3537161
  simp only [CollatzResearch.WordTrace]
  refine ⟨129010860338477270849131337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86007240225651513899420891 129010860338477270849131337)
  ·
    refine ⟨96758145253857953136848503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129010860338477270849131337 96758145253857953136848503)
    ·
      refine ⟨145137217880786929705272755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96758145253857953136848503 145137217880786929705272755)
      ·
        refine ⟨217705826821180394557909133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145137217880786929705272755 217705826821180394557909133)
        ·
          refine ⟨81639685057942647959215925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217705826821180394557909133 81639685057942647959215925)
          ·
            refine ⟨7653720474182123246176493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81639685057942647959215925 7653720474182123246176493)
            ·
              refine ⟨2870145177818296217316185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7653720474182123246176493 2870145177818296217316185)
              ·
                refine ⟨2152608883363722162987139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2870145177818296217316185 2152608883363722162987139)
                ·
                  refine ⟨3228913325045583244480709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2152608883363722162987139 3228913325045583244480709)
                  ·
                    refine ⟨605421248446046858340133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3228913325045583244480709 605421248446046858340133)
                    ·
                      rfl

theorem cell23_3537161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 2, 1, 4].length) (baseStart_3537161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537161 prefixEnd_3537161 := by exact prefixLift 3537161
  have htrace : WordTrace (prefixWord ++ tailWord_3537161) baseStart_3537161 baseEnd_3537161 := by
    simpa [prefixWord, tailWord_3537161, baseEnd_3537161] using wordTrace_append hprefix tailTrace_3537161
  have hstable : (prefixWord ++ tailWord_3537161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537161).length < 2 ^ (prefixWord ++ tailWord_3537161).sum := by decide
  have hdescent : baseEnd_3537161 < baseStart_3537161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537207 : List Nat := [1, 1, 3, 1, 2, 1, 1, 7, 1, 1, 4]
def baseStart_3537207 : Nat := 118140960795 + 3537207 * 2 ^ 59
def prefixEnd_3537207 : Nat := 4983230072969 + 3 ^ 40 * 3537207 * 2
def baseEnd_3537207 : Nat := 1816287365448247395045187

theorem tailTrace_3537207 : CollatzResearch.WordTrace tailWord_3537207 prefixEnd_3537207 1816287365448247395045187 := by
  unfold tailWord_3537207
  simp only [CollatzResearch.WordTrace]
  refine ⟨129012538096310620705305875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86008358730873747136870583 129012538096310620705305875)
  ·
    refine ⟨193518807144465931057958813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129012538096310620705305875 193518807144465931057958813)
    ·
      refine ⟨72569552679174724146734555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193518807144465931057958813 72569552679174724146734555)
      ·
        refine ⟨108854329018762086220101833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72569552679174724146734555 108854329018762086220101833)
        ·
          refine ⟨81640746764071564665076375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108854329018762086220101833 81640746764071564665076375)
          ·
            refine ⟨122461120146107346997614563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81640746764071564665076375 122461120146107346997614563)
            ·
              refine ⟨183691680219161020496421845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122461120146107346997614563 183691680219161020496421845)
              ·
                refine ⟨4305273755136586417884887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 183691680219161020496421845 4305273755136586417884887)
                ·
                  refine ⟨6457910632704879626827331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4305273755136586417884887 6457910632704879626827331)
                  ·
                    refine ⟨9686865949057319440240997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6457910632704879626827331 9686865949057319440240997)
                    ·
                      refine ⟨1816287365448247395045187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9686865949057319440240997 1816287365448247395045187)
                      ·
                        rfl

theorem cell23_3537207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 1, 4].length) (baseStart_3537207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537207 prefixEnd_3537207 := by exact prefixLift 3537207
  have htrace : WordTrace (prefixWord ++ tailWord_3537207) baseStart_3537207 baseEnd_3537207 := by
    simpa [prefixWord, tailWord_3537207, baseEnd_3537207] using wordTrace_append hprefix tailTrace_3537207
  have hstable : (prefixWord ++ tailWord_3537207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537207).length < 2 ^ (prefixWord ++ tailWord_3537207).sum := by decide
  have hdescent : baseEnd_3537207 < baseStart_3537207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537230 : List Nat := [4, 1, 1, 1, 1, 1, 2, 12]
def baseStart_3537230 : Nat := 118140960795 + 3537230 * 2 ^ 59
def prefixEnd_3537230 : Nat := 4983230072969 + 3 ^ 40 * 3537230 * 2
def baseEnd_3537230 : Nat := 67270339833455585372503

theorem tailTrace_3537230 : CollatzResearch.WordTrace tailWord_3537230 prefixEnd_3537230 67270339833455585372503 := by
  unfold tailWord_3537230
  simp only [CollatzResearch.WordTrace]
  refine ⟨16126672121903411954174143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86008917983484863755595429 16126672121903411954174143)
  ·
    refine ⟨24190008182855117931261215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16126672121903411954174143 24190008182855117931261215)
    ·
      refine ⟨36285012274282676896891823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24190008182855117931261215 36285012274282676896891823)
      ·
        refine ⟨54427518411424015345337735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36285012274282676896891823 54427518411424015345337735)
        ·
          refine ⟨81641277617136023018006603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54427518411424015345337735 81641277617136023018006603)
          ·
            refine ⟨122461916425704034527009905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81641277617136023018006603 122461916425704034527009905)
            ·
              refine ⟨91846437319278025895257429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122461916425704034527009905 91846437319278025895257429)
              ·
                refine ⟨67270339833455585372503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 91846437319278025895257429 67270339833455585372503)
                ·
                  rfl

theorem cell23_3537230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 12].length) (baseStart_3537230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537230 prefixEnd_3537230 := by exact prefixLift 3537230
  have htrace : WordTrace (prefixWord ++ tailWord_3537230) baseStart_3537230 baseEnd_3537230 := by
    simpa [prefixWord, tailWord_3537230, baseEnd_3537230] using wordTrace_append hprefix tailTrace_3537230
  have hstable : (prefixWord ++ tailWord_3537230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537230).length < 2 ^ (prefixWord ++ tailWord_3537230).sum := by decide
  have hdescent : baseEnd_3537230 < baseStart_3537230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537234 : List Nat := [3, 2, 2, 1, 1, 1, 4, 3, 2, 4]
def baseStart_3537234 : Nat := 118140960795 + 3537234 * 2 ^ 59
def prefixEnd_3537234 : Nat := 4983230072969 + 3 ^ 40 * 3537234 * 2
def baseEnd_3537234 : Nat := 605433743141972929802521

theorem tailTrace_3537234 : CollatzResearch.WordTrace tailWord_3537234 prefixEnd_3537234 605433743141972929802521 := by
  unfold tailWord_3537234
  simp only [CollatzResearch.WordTrace]
  refine ⟨32253380716803201079134689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86009015244808536211025837 32253380716803201079134689)
  ·
    refine ⟨24190035537602400809351017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32253380716803201079134689 24190035537602400809351017)
    ·
      refine ⟨18142526653201800607013263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24190035537602400809351017 18142526653201800607013263)
      ·
        refine ⟨27213789979802700910519895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18142526653201800607013263 27213789979802700910519895)
        ·
          refine ⟨40820684969704051365779843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27213789979802700910519895 40820684969704051365779843)
          ·
            refine ⟨61231027454556077048669765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40820684969704051365779843 61231027454556077048669765)
            ·
              refine ⟨11480817647729264446625581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61231027454556077048669765 11480817647729264446625581)
              ·
                refine ⟨4305306617898474167484593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11480817647729264446625581 4305306617898474167484593)
                ·
                  refine ⟨3228979963423855625613445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4305306617898474167484593 3228979963423855625613445)
                  ·
                    refine ⟨605433743141972929802521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3228979963423855625613445 605433743141972929802521)
                    ·
                      rfl

theorem cell23_3537234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_3537234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537234 prefixEnd_3537234 := by exact prefixLift 3537234
  have htrace : WordTrace (prefixWord ++ tailWord_3537234) baseStart_3537234 baseEnd_3537234 := by
    simpa [prefixWord, tailWord_3537234, baseEnd_3537234] using wordTrace_append hprefix tailTrace_3537234
  have hstable : (prefixWord ++ tailWord_3537234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537234).length < 2 ^ (prefixWord ++ tailWord_3537234).sum := by decide
  have hdescent : baseEnd_3537234 < baseStart_3537234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537257 : List Nat := [1, 2, 1, 1, 1, 3, 3, 4, 1, 3, 3]
def baseStart_3537257 : Nat := 118140960795 + 3537257 * 2 ^ 59
def prefixEnd_3537257 : Nat := 4983230072969 + 3 ^ 40 * 3537257 * 2
def baseEnd_3537257 : Nat := 1816313039480972199419957

theorem tailTrace_3537257 : CollatzResearch.WordTrace tailWord_3537257 prefixEnd_3537257 1816313039480972199419957 := by
  unfold tailWord_3537257
  simp only [CollatzResearch.WordTrace]
  refine ⟨129014361746129479244626025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86009574497419652829750683 129014361746129479244626025)
  ·
    refine ⟨96760771309597109433469519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129014361746129479244626025 96760771309597109433469519)
    ·
      refine ⟨145141156964395664150204279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96760771309597109433469519 145141156964395664150204279)
      ·
        refine ⟨217711735446593496225306419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145141156964395664150204279 217711735446593496225306419)
        ·
          refine ⟨326567603169890244337959629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217711735446593496225306419 326567603169890244337959629)
          ·
            refine ⟨122462851188708841626734861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326567603169890244337959629 122462851188708841626734861)
            ·
              refine ⟨45923569195765815610025573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122462851188708841626734861 45923569195765815610025573)
              ·
                refine ⟨8610669224206090426879795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45923569195765815610025573 8610669224206090426879795)
                ·
                  refine ⟨12916003836309135640319693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8610669224206090426879795 12916003836309135640319693)
                  ·
                    refine ⟨4843501438615925865119885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12916003836309135640319693 4843501438615925865119885)
                    ·
                      refine ⟨1816313039480972199419957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4843501438615925865119885 1816313039480972199419957)
                      ·
                        rfl

theorem cell23_3537257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 3, 3].length) (baseStart_3537257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537257 prefixEnd_3537257 := by exact prefixLift 3537257
  have htrace : WordTrace (prefixWord ++ tailWord_3537257) baseStart_3537257 baseEnd_3537257 := by
    simpa [prefixWord, tailWord_3537257, baseEnd_3537257] using wordTrace_append hprefix tailTrace_3537257
  have hstable : (prefixWord ++ tailWord_3537257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537257).length < 2 ^ (prefixWord ++ tailWord_3537257).sum := by decide
  have hdescent : baseEnd_3537257 < baseStart_3537257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537258 : List Nat := [3, 1, 3, 3, 1, 3, 2, 1, 1, 1, 4]
def baseStart_3537258 : Nat := 118140960795 + 3537258 * 2 ^ 59
def prefixEnd_3537258 : Nat := 4983230072969 + 3 ^ 40 * 3537258 * 2
def baseEnd_3537258 : Nat := 1816313552961626695507453

theorem tailTrace_3537258 : CollatzResearch.WordTrace tailWord_3537258 prefixEnd_3537258 1816313552961626695507453 := by
  unfold tailWord_3537258
  simp only [CollatzResearch.WordTrace]
  refine ⟨32253599554781464103853107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86009598812750570943608285 32253599554781464103853107)
  ·
    refine ⟨48380399332172196155779661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32253599554781464103853107 48380399332172196155779661)
    ·
      refine ⟨18142649749564573558417373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48380399332172196155779661 18142649749564573558417373)
      ·
        refine ⟨6803493656086715084406515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18142649749564573558417373 6803493656086715084406515)
        ·
          refine ⟨10205240484130072626609773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6803493656086715084406515 10205240484130072626609773)
          ·
            refine ⟨3826965181548777234978665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10205240484130072626609773 3826965181548777234978665)
            ·
              refine ⟨2870223886161582926233999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3826965181548777234978665 2870223886161582926233999)
              ·
                refine ⟨4305335829242374389350999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2870223886161582926233999 4305335829242374389350999)
                ·
                  refine ⟨6458003743863561584026499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4305335829242374389350999 6458003743863561584026499)
                  ·
                    refine ⟨9687005615795342376039749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6458003743863561584026499 9687005615795342376039749)
                    ·
                      refine ⟨1816313552961626695507453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9687005615795342376039749 1816313552961626695507453)
                      ·
                        rfl

theorem cell23_3537258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_3537258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537258 prefixEnd_3537258 := by exact prefixLift 3537258
  have htrace : WordTrace (prefixWord ++ tailWord_3537258) baseStart_3537258 baseEnd_3537258 := by
    simpa [prefixWord, tailWord_3537258, baseEnd_3537258] using wordTrace_append hprefix tailTrace_3537258
  have hstable : (prefixWord ++ tailWord_3537258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537258).length < 2 ^ (prefixWord ++ tailWord_3537258).sum := by decide
  have hdescent : baseEnd_3537258 < baseStart_3537258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537317 : List Nat := [1, 3, 1, 2, 1, 1, 5, 1, 2, 1, 5]
def baseStart_3537317 : Nat := 118140960795 + 3537317 * 2 ^ 59
def prefixEnd_3537317 : Nat := 4983230072969 + 3 ^ 40 * 3537317 * 2
def baseEnd_3537317 : Nat := 1816343848320241964669681

theorem tailTrace_3537317 : CollatzResearch.WordTrace tailWord_3537317 prefixEnd_3537317 1816343848320241964669681 := by
  unfold tailWord_3537317
  simp only [CollatzResearch.WordTrace]
  refine ⟨129016550125912109491810205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86011033417274739661206803 129016550125912109491810205)
  ·
    refine ⟨48381206297217041059428827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129016550125912109491810205 48381206297217041059428827)
    ·
      refine ⟨72571809445825561589143241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48381206297217041059428827 72571809445825561589143241)
      ·
        refine ⟨54428857084369171191857431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72571809445825561589143241 54428857084369171191857431)
        ·
          refine ⟨81643285626553756787786147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54428857084369171191857431 81643285626553756787786147)
          ·
            refine ⟨122464928439830635181679221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81643285626553756787786147 122464928439830635181679221)
            ·
              refine ⟨11481087041234122048282427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122464928439830635181679221 11481087041234122048282427)
              ·
                refine ⟨17221630561851183072423641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11481087041234122048282427 17221630561851183072423641)
                ·
                  refine ⟨12916222921388387304317731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17221630561851183072423641 12916222921388387304317731)
                  ·
                    refine ⟨19374334382082580956476597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12916222921388387304317731 19374334382082580956476597)
                    ·
                      refine ⟨1816343848320241964669681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19374334382082580956476597 1816343848320241964669681)
                      ·
                        rfl

theorem cell23_3537317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_3537317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537317 prefixEnd_3537317 := by exact prefixLift 3537317
  have htrace : WordTrace (prefixWord ++ tailWord_3537317) baseStart_3537317 baseEnd_3537317 := by
    simpa [prefixWord, tailWord_3537317, baseEnd_3537317] using wordTrace_append hprefix tailTrace_3537317
  have hstable : (prefixWord ++ tailWord_3537317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537317).length < 2 ^ (prefixWord ++ tailWord_3537317).sum := by decide
  have hdescent : baseEnd_3537317 < baseStart_3537317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537347 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 1, 5, 3]
def baseStart_3537347 : Nat := 118140960795 + 3537347 * 2 ^ 59
def prefixEnd_3537347 : Nat := 4983230072969 + 3 ^ 40 * 3537347 * 2
def baseEnd_3537347 : Nat := 1816359252739876847294543

theorem tailTrace_3537347 : CollatzResearch.WordTrace tailWord_3537347 prefixEnd_3537347 1816359252739876847294543 := by
  unfold tailWord_3537347
  simp only [CollatzResearch.WordTrace]
  refine ⟨129017644315803424615402295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86011762877202283076934863 129017644315803424615402295)
  ·
    refine ⟨193526466473705136923103443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129017644315803424615402295 193526466473705136923103443)
    ·
      refine ⟨290289699710557705384655165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193526466473705136923103443 290289699710557705384655165)
      ·
        refine ⟨108858637391459139519245687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290289699710557705384655165 108858637391459139519245687)
        ·
          refine ⟨163287956087188709278868531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108858637391459139519245687 163287956087188709278868531)
          ·
            refine ⟨244931934130783063918302797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163287956087188709278868531 244931934130783063918302797)
            ·
              refine ⟨91849475299043648969363549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244931934130783063918302797 91849475299043648969363549)
              ·
                refine ⟨34443553237141368363511331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91849475299043648969363549 34443553237141368363511331)
                ·
                  refine ⟨51665329855712052545266997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34443553237141368363511331 51665329855712052545266997)
                  ·
                    refine ⟨4843624673973004926118781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51665329855712052545266997 4843624673973004926118781)
                    ·
                      refine ⟨1816359252739876847294543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4843624673973004926118781 1816359252739876847294543)
                      ·
                        rfl

theorem cell23_3537347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 5, 3].length) (baseStart_3537347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537347 prefixEnd_3537347 := by exact prefixLift 3537347
  have htrace : WordTrace (prefixWord ++ tailWord_3537347) baseStart_3537347 baseEnd_3537347 := by
    simpa [prefixWord, tailWord_3537347, baseEnd_3537347] using wordTrace_append hprefix tailTrace_3537347
  have hstable : (prefixWord ++ tailWord_3537347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537347).length < 2 ^ (prefixWord ++ tailWord_3537347).sum := by decide
  have hdescent : baseEnd_3537347 < baseStart_3537347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537377 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 3, 2, 5]
def baseStart_3537377 : Nat := 118140960795 + 3537377 * 2 ^ 59
def prefixEnd_3537377 : Nat := 4983230072969 + 3 ^ 40 * 3537377 * 2
def baseEnd_3537377 : Nat := 1816374657159511729919405

theorem tailTrace_3537377 : CollatzResearch.WordTrace tailWord_3537377 prefixEnd_3537377 1816374657159511729919405 := by
  unfold tailWord_3537377
  simp only [CollatzResearch.WordTrace]
  refine ⟨129018738505694739738994385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86012492337129826492662923 129018738505694739738994385)
  ·
    refine ⟨96764053879271054804245789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129018738505694739738994385 96764053879271054804245789)
    ·
      refine ⟨36286520204726645551592171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96764053879271054804245789 36286520204726645551592171)
      ·
        refine ⟨54429780307089968327388257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36286520204726645551592171 54429780307089968327388257)
        ·
          refine ⟨40822335230317476245541193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54429780307089968327388257 40822335230317476245541193)
          ·
            refine ⟨30616751422738107184155895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40822335230317476245541193 30616751422738107184155895)
            ·
              refine ⟨45925127134107160776233843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30616751422738107184155895 45925127134107160776233843)
              ·
                refine ⟨68887690701160741164350765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45925127134107160776233843 68887690701160741164350765)
                ·
                  refine ⟨25832884012935277936631537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68887690701160741164350765 25832884012935277936631537)
                  ·
                    refine ⟨19374663009701458452473653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25832884012935277936631537 19374663009701458452473653)
                    ·
                      refine ⟨1816374657159511729919405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19374663009701458452473653 1816374657159511729919405)
                      ·
                        rfl

theorem cell23_3537377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_3537377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537377 prefixEnd_3537377 := by exact prefixLift 3537377
  have htrace : WordTrace (prefixWord ++ tailWord_3537377) baseStart_3537377 baseEnd_3537377 := by
    simpa [prefixWord, tailWord_3537377, baseEnd_3537377] using wordTrace_append hprefix tailTrace_3537377
  have hstable : (prefixWord ++ tailWord_3537377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537377).length < 2 ^ (prefixWord ++ tailWord_3537377).sum := by decide
  have hdescent : baseEnd_3537377 < baseStart_3537377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537384 : List Nat := [2, 1, 4, 1, 1, 3, 2, 2, 2, 5]
def baseStart_3537384 : Nat := 118140960795 + 3537384 * 2 ^ 59
def prefixEnd_3537384 : Nat := 4983230072969 + 3 ^ 40 * 3537384 * 2
def baseEnd_3537384 : Nat := 605459417174697734177291

theorem tailTrace_3537384 : CollatzResearch.WordTrace tailWord_3537384 prefixEnd_3537384 605459417174697734177291 := by
  unfold tailWord_3537384
  simp only [CollatzResearch.WordTrace]
  refine ⟨64509496908334689967249603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86012662544446253289666137 64509496908334689967249603)
  ·
    refine ⟨96764245362502034950874405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64509496908334689967249603 96764245362502034950874405)
    ·
      refine ⟨18143296005469131553288951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96764245362502034950874405 18143296005469131553288951)
      ·
        refine ⟨27214944008203697329933427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18143296005469131553288951 27214944008203697329933427)
        ·
          refine ⟨40822416012305545994900141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27214944008203697329933427 40822416012305545994900141)
          ·
            refine ⟨15308406004614579748087553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40822416012305545994900141 15308406004614579748087553)
            ·
              refine ⟨11481304503460934811065665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15308406004614579748087553 11481304503460934811065665)
              ·
                refine ⟨8610978377595701108299249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11481304503460934811065665 8610978377595701108299249)
                ·
                  refine ⟨6458233783196775831224437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8610978377595701108299249 6458233783196775831224437)
                  ·
                    refine ⟨605459417174697734177291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6458233783196775831224437 605459417174697734177291)
                    ·
                      rfl

theorem cell23_3537384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_3537384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537384 prefixEnd_3537384 := by exact prefixLift 3537384
  have htrace : WordTrace (prefixWord ++ tailWord_3537384) baseStart_3537384 baseEnd_3537384 := by
    simpa [prefixWord, tailWord_3537384, baseEnd_3537384] using wordTrace_append hprefix tailTrace_3537384
  have hstable : (prefixWord ++ tailWord_3537384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537384).length < 2 ^ (prefixWord ++ tailWord_3537384).sum := by decide
  have hdescent : baseEnd_3537384 < baseStart_3537384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537417 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 1, 6, 4]
def baseStart_3537417 : Nat := 118140960795 + 3537417 * 2 ^ 59
def prefixEnd_3537417 : Nat := 4983230072969 + 3 ^ 40 * 3537417 * 2
def baseEnd_3537417 : Nat := 1816395196385691573419221

theorem tailTrace_3537417 : CollatzResearch.WordTrace tailWord_3537417 prefixEnd_3537417 1816395196385691573419221 := by
  unfold tailWord_3537417
  simp only [CollatzResearch.WordTrace]
  refine ⟨129020197425549826570450505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86013464950366551046967003 129020197425549826570450505)
  ·
    refine ⟨96765148069162369927837879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129020197425549826570450505 96765148069162369927837879)
    ·
      refine ⟨145147722103743554891756819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96765148069162369927837879 145147722103743554891756819)
      ·
        refine ⟨217721583155615332337635229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145147722103743554891756819 217721583155615332337635229)
        ·
          refine ⟨81645593683355749626613211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217721583155615332337635229 81645593683355749626613211)
          ·
            refine ⟨122468390525033624439919817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81645593683355749626613211 122468390525033624439919817)
            ·
              refine ⟨91851292893775218329939863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122468390525033624439919817 91851292893775218329939863)
              ·
                refine ⟨137776939340662827494909795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91851292893775218329939863 137776939340662827494909795)
                ·
                  refine ⟨206665409010994241242364693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137776939340662827494909795 206665409010994241242364693)
                  ·
                    refine ⟨9687441047390355058235845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 206665409010994241242364693 9687441047390355058235845)
                    ·
                      refine ⟨1816395196385691573419221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9687441047390355058235845 1816395196385691573419221)
                      ·
                        rfl

theorem cell23_3537417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 6, 4].length) (baseStart_3537417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537417 prefixEnd_3537417 := by exact prefixLift 3537417
  have htrace : WordTrace (prefixWord ++ tailWord_3537417) baseStart_3537417 baseEnd_3537417 := by
    simpa [prefixWord, tailWord_3537417, baseEnd_3537417] using wordTrace_append hprefix tailTrace_3537417
  have hstable : (prefixWord ++ tailWord_3537417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537417).length < 2 ^ (prefixWord ++ tailWord_3537417).sum := by decide
  have hdescent : baseEnd_3537417 < baseStart_3537417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537427 : List Nat := [1, 1, 1, 2, 1, 5, 2, 2, 8]
def baseStart_3537427 : Nat := 118140960795 + 3537427 * 2 ^ 59
def prefixEnd_3537427 : Nat := 4983230072969 + 3 ^ 40 * 3537427 * 2
def baseEnd_3537427 : Nat := 201822259021359614921575

theorem tailTrace_3537427 : CollatzResearch.WordTrace tailWord_3537427 prefixEnd_3537427 201822259021359614921575 := by
  unfold tailWord_3537427
  simp only [CollatzResearch.WordTrace]
  refine ⟨129020562155513598278314535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86013708103675732185543023 129020562155513598278314535)
  ·
    refine ⟨193530843233270397417471803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129020562155513598278314535 193530843233270397417471803)
    ·
      refine ⟨290296264849905596126207705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193530843233270397417471803 290296264849905596126207705)
      ·
        refine ⟨217722198637429197094655779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290296264849905596126207705 217722198637429197094655779)
        ·
          refine ⟨326583297956143795641983669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217722198637429197094655779 326583297956143795641983669)
          ·
            refine ⟨30617184183388480841435969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 326583297956143795641983669 30617184183388480841435969)
            ·
              refine ⟨22962888137541360631076977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30617184183388480841435969 22962888137541360631076977)
              ·
                refine ⟨17222166103156020473307733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22962888137541360631076977 17222166103156020473307733)
                ·
                  refine ⟨201822259021359614921575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17222166103156020473307733 201822259021359614921575)
                  ·
                    rfl

theorem cell23_3537427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 8].length) (baseStart_3537427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537427 prefixEnd_3537427 := by exact prefixLift 3537427
  have htrace : WordTrace (prefixWord ++ tailWord_3537427) baseStart_3537427 baseEnd_3537427 := by
    simpa [prefixWord, tailWord_3537427, baseEnd_3537427] using wordTrace_append hprefix tailTrace_3537427
  have hstable : (prefixWord ++ tailWord_3537427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537427).length < 2 ^ (prefixWord ++ tailWord_3537427).sum := by decide
  have hdescent : baseEnd_3537427 < baseStart_3537427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537448 : List Nat := [2, 1, 5, 2, 1, 2, 2, 1, 3, 4]
def baseStart_3537448 : Nat := 118140960795 + 3537448 * 2 ^ 59
def prefixEnd_3537448 : Nat := 4983230072969 + 3 ^ 40 * 3537448 * 2
def baseEnd_3537448 : Nat := 605470371428660317377193

theorem tailTrace_3537448 : CollatzResearch.WordTrace tailWord_3537448 prefixEnd_3537448 605470371428660317377193 := by
  unfold tailWord_3537448
  simp only [CollatzResearch.WordTrace]
  refine ⟨64510664044218759432414499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86014218725625012576552665 64510664044218759432414499)
  ·
    refine ⟨96765996066328139148621749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64510664044218759432414499 96765996066328139148621749)
    ·
      refine ⟨9071812131218263045183289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96765996066328139148621749 9071812131218263045183289)
      ·
        refine ⟨6803859098413697283887467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9071812131218263045183289 6803859098413697283887467)
        ·
          refine ⟨10205788647620545925831201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6803859098413697283887467 10205788647620545925831201)
          ·
            refine ⟨7654341485715409444373401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10205788647620545925831201 7654341485715409444373401)
            ·
              refine ⟨5740756114286557083280051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7654341485715409444373401 5740756114286557083280051)
              ·
                refine ⟨8611134171429835624920077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5740756114286557083280051 8611134171429835624920077)
                ·
                  refine ⟨3229175314286188359345029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8611134171429835624920077 3229175314286188359345029)
                  ·
                    refine ⟨605470371428660317377193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3229175314286188359345029 605470371428660317377193)
                    ·
                      rfl

theorem cell23_3537448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_3537448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537448 prefixEnd_3537448 := by exact prefixLift 3537448
  have htrace : WordTrace (prefixWord ++ tailWord_3537448) baseStart_3537448 baseEnd_3537448 := by
    simpa [prefixWord, tailWord_3537448, baseEnd_3537448] using wordTrace_append hprefix tailTrace_3537448
  have hstable : (prefixWord ++ tailWord_3537448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537448).length < 2 ^ (prefixWord ++ tailWord_3537448).sum := by decide
  have hdescent : baseEnd_3537448 < baseStart_3537448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537461 : List Nat := [1, 3, 3, 1, 1, 2, 5, 1, 6]
def baseStart_3537461 : Nat := 118140960795 + 3537461 * 2 ^ 59
def prefixEnd_3537461 : Nat := 4983230072969 + 3 ^ 40 * 3537461 * 2
def baseEnd_3537461 : Nat := 201824198837165489029891

theorem tailTrace_3537461 : CollatzResearch.WordTrace tailWord_3537461 prefixEnd_3537461 201824198837165489029891 := by
  unfold tailWord_3537461
  simp only [CollatzResearch.WordTrace]
  refine ⟨129021802237390422085052237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86014534824926948056701491 129021802237390422085052237)
  ·
    refine ⟨48383175839021408281894589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129021802237390422085052237 48383175839021408281894589)
    ·
      refine ⟨18143690939633028105710471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48383175839021408281894589 18143690939633028105710471)
      ·
        refine ⟨27215536409449542158565707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18143690939633028105710471 27215536409449542158565707)
        ·
          refine ⟨40823304614174313237848561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27215536409449542158565707 40823304614174313237848561)
          ·
            refine ⟨30617478460630734928386421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40823304614174313237848561 30617478460630734928386421)
            ·
              refine ⟨2870388605684131399536227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30617478460630734928386421 2870388605684131399536227)
              ·
                refine ⟨4305582908526197099304341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2870388605684131399536227 4305582908526197099304341)
                ·
                  refine ⟨201824198837165489029891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4305582908526197099304341 201824198837165489029891)
                  ·
                    rfl

theorem cell23_3537461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 6].length) (baseStart_3537461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537461 prefixEnd_3537461 := by exact prefixLift 3537461
  have htrace : WordTrace (prefixWord ++ tailWord_3537461) baseStart_3537461 baseEnd_3537461 := by
    simpa [prefixWord, tailWord_3537461, baseEnd_3537461] using wordTrace_append hprefix tailTrace_3537461
  have hstable : (prefixWord ++ tailWord_3537461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537461).length < 2 ^ (prefixWord ++ tailWord_3537461).sum := by decide
  have hdescent : baseEnd_3537461 < baseStart_3537461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537467 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 5]
def baseStart_3537467 : Nat := 118140960795 + 3537467 * 2 ^ 59
def prefixEnd_3537467 : Nat := 4983230072969 + 3 ^ 40 * 3537467 * 2
def baseEnd_3537467 : Nat := 1816420870418416377793991

theorem tailTrace_3537467 : CollatzResearch.WordTrace tailWord_3537467 prefixEnd_3537467 1816420870418416377793991 := by
  unfold tailWord_3537467
  simp only [CollatzResearch.WordTrace]
  refine ⟨129022021075368685109770655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86014680716912456739847103 129022021075368685109770655)
  ·
    refine ⟨193533031613053027664655983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129022021075368685109770655 193533031613053027664655983)
    ·
      refine ⟨290299547419579541496983975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193533031613053027664655983 290299547419579541496983975)
      ·
        refine ⟨435449321129369312245475963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290299547419579541496983975 435449321129369312245475963)
        ·
          refine ⟨653173981694053968368213945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435449321129369312245475963 653173981694053968368213945)
          ·
            refine ⟨489880486270540476276160459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 653173981694053968368213945 489880486270540476276160459)
            ·
              refine ⟨734820729405810714414240689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489880486270540476276160459 734820729405810714414240689)
              ·
                refine ⟨551115547054358035810680517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 734820729405810714414240689 551115547054358035810680517)
                ·
                  refine ⟨103334165072692131714502597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 551115547054358035810680517 103334165072692131714502597)
                  ·
                    refine ⟨19375155951129774696469237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103334165072692131714502597 19375155951129774696469237)
                    ·
                      refine ⟨1816420870418416377793991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19375155951129774696469237 1816420870418416377793991)
                      ·
                        rfl

theorem cell23_3537467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 5].length) (baseStart_3537467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537467 prefixEnd_3537467 := by exact prefixLift 3537467
  have htrace : WordTrace (prefixWord ++ tailWord_3537467) baseStart_3537467 baseEnd_3537467 := by
    simpa [prefixWord, tailWord_3537467, baseEnd_3537467] using wordTrace_append hprefix tailTrace_3537467
  have hstable : (prefixWord ++ tailWord_3537467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537467).length < 2 ^ (prefixWord ++ tailWord_3537467).sum := by decide
  have hdescent : baseEnd_3537467 < baseStart_3537467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537471 : List Nat := [1, 1, 2, 2, 3, 2, 1, 4, 3, 1, 3]
def baseStart_3537471 : Nat := 118140960795 + 3537471 * 2 ^ 59
def prefixEnd_3537471 : Nat := 4983230072969 + 3 ^ 40 * 3537471 * 2
def baseEnd_3537471 : Nat := 1816422924341034362143973

theorem tailTrace_3537471 : CollatzResearch.WordTrace tailWord_3537471 prefixEnd_3537471 1816422924341034362143973 := by
  unfold tailWord_3537471
  simp only [CollatzResearch.WordTrace]
  refine ⟨129022166967354193792916267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86014777978236129195277511 129022166967354193792916267)
  ·
    refine ⟨193533250451031290689374401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129022166967354193792916267 193533250451031290689374401)
    ·
      refine ⟨145149937838273468017030801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193533250451031290689374401 145149937838273468017030801)
      ·
        refine ⟨108862453378705101012773101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145149937838273468017030801 108862453378705101012773101)
        ·
          refine ⟨40823420017014412879789913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108862453378705101012773101 40823420017014412879789913)
          ·
            refine ⟨30617565012760809659842435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40823420017014412879789913 30617565012760809659842435)
            ·
              refine ⟨45926347519141214489763653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30617565012760809659842435 45926347519141214489763653)
              ·
                refine ⟨8611190159838977716830685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45926347519141214489763653 8611190159838977716830685)
                ·
                  refine ⟨3229196309939616643811507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8611190159838977716830685 3229196309939616643811507)
                  ·
                    refine ⟨4843794464909424965717261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3229196309939616643811507 4843794464909424965717261)
                    ·
                      refine ⟨1816422924341034362143973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4843794464909424965717261 1816422924341034362143973)
                      ·
                        rfl

theorem cell23_3537471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 3, 1, 3].length) (baseStart_3537471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537471 prefixEnd_3537471 := by exact prefixLift 3537471
  have htrace : WordTrace (prefixWord ++ tailWord_3537471) baseStart_3537471 baseEnd_3537471 := by
    simpa [prefixWord, tailWord_3537471, baseEnd_3537471] using wordTrace_append hprefix tailTrace_3537471
  have hstable : (prefixWord ++ tailWord_3537471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537471).length < 2 ^ (prefixWord ++ tailWord_3537471).sum := by decide
  have hdescent : baseEnd_3537471 < baseStart_3537471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537488 : List Nat := [2, 1, 1, 1, 1, 3, 2, 7, 1, 1, 3]
def baseStart_3537488 : Nat := 118140960795 + 3537488 * 2 ^ 59
def prefixEnd_3537488 : Nat := 4983230072969 + 3 ^ 40 * 3537488 * 2
def baseEnd_3537488 : Nat := 1816431653512160795631395

theorem tailTrace_3537488 : CollatzResearch.WordTrace tailWord_3537488 prefixEnd_3537488 1816431653512160795631395 := by
  unfold tailWord_3537488
  simp only [CollatzResearch.WordTrace]
  refine ⟨64511393504146302848142559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86015191338861737130856745 64511393504146302848142559)
  ·
    refine ⟨96767090256219454272213839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64511393504146302848142559 96767090256219454272213839)
    ·
      refine ⟨145150635384329181408320759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96767090256219454272213839 145150635384329181408320759)
      ·
        refine ⟨217725953076493772112481139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145150635384329181408320759 217725953076493772112481139)
        ·
          refine ⟨326588929614740658168721709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217725953076493772112481139 326588929614740658168721709)
          ·
            refine ⟨122470848605527746813270641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326588929614740658168721709 122470848605527746813270641)
            ·
              refine ⟨91853136454145810109952981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122470848605527746813270641 91853136454145810109952981)
              ·
                refine ⟨2152807885644042424452023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 91853136454145810109952981 2152807885644042424452023)
                ·
                  refine ⟨3229211828466063636678035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2152807885644042424452023 3229211828466063636678035)
                  ·
                    refine ⟨4843817742699095455017053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3229211828466063636678035 4843817742699095455017053)
                    ·
                      refine ⟨1816431653512160795631395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4843817742699095455017053 1816431653512160795631395)
                      ·
                        rfl

theorem cell23_3537488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 7, 1, 1, 3].length) (baseStart_3537488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537488 prefixEnd_3537488 := by exact prefixLift 3537488
  have htrace : WordTrace (prefixWord ++ tailWord_3537488) baseStart_3537488 baseEnd_3537488 := by
    simpa [prefixWord, tailWord_3537488, baseEnd_3537488] using wordTrace_append hprefix tailTrace_3537488
  have hstable : (prefixWord ++ tailWord_3537488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537488).length < 2 ^ (prefixWord ++ tailWord_3537488).sum := by decide
  have hdescent : baseEnd_3537488 < baseStart_3537488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537525 : List Nat := [1, 3, 4, 2, 2, 2, 1, 2, 1, 5]
def baseStart_3537525 : Nat := 118140960795 + 3537525 * 2 ^ 59
def prefixEnd_3537525 : Nat := 4983230072969 + 3 ^ 40 * 3537525 * 2
def baseEnd_3537525 : Nat := 605483550765459050289575

theorem tailTrace_3537525 : CollatzResearch.WordTrace tailWord_3537525 prefixEnd_3537525 605483550765459050289575 := by
  unfold tailWord_3537525
  simp only [CollatzResearch.WordTrace]
  refine ⟨129024136509158561015382029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86016091006105707343588019 129024136509158561015382029)
  ·
    refine ⟨48384051190934460380768261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129024136509158561015382029 48384051190934460380768261)
    ·
      refine ⟨9072009598300211321394049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48384051190934460380768261 9072009598300211321394049)
      ·
        refine ⟨6804007198725158491045537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9072009598300211321394049 6804007198725158491045537)
        ·
          refine ⟨5103005399043868868284153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6804007198725158491045537 5103005399043868868284153)
          ·
            refine ⟨3827254049282901651213115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5103005399043868868284153 3827254049282901651213115)
            ·
              refine ⟨5740881073924352476819673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3827254049282901651213115 5740881073924352476819673)
              ·
                refine ⟨4305660805443264357614755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5740881073924352476819673 4305660805443264357614755)
                ·
                  refine ⟨6458491208164896536422133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4305660805443264357614755 6458491208164896536422133)
                  ·
                    refine ⟨605483550765459050289575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6458491208164896536422133 605483550765459050289575)
                    ·
                      rfl

theorem cell23_3537525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_3537525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537525 prefixEnd_3537525 := by exact prefixLift 3537525
  have htrace : WordTrace (prefixWord ++ tailWord_3537525) baseStart_3537525 baseEnd_3537525 := by
    simpa [prefixWord, tailWord_3537525, baseEnd_3537525] using wordTrace_append hprefix tailTrace_3537525
  have hstable : (prefixWord ++ tailWord_3537525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537525).length < 2 ^ (prefixWord ++ tailWord_3537525).sum := by decide
  have hdescent : baseEnd_3537525 < baseStart_3537525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537531 : List Nat := [1, 1, 1, 1, 1, 4, 2, 6, 1, 2, 3]
def baseStart_3537531 : Nat := 118140960795 + 3537531 * 2 ^ 59
def prefixEnd_3537531 : Nat := 4983230072969 + 3 ^ 40 * 3537531 * 2
def baseEnd_3537531 : Nat := 1816453733180304127393697

theorem tailTrace_3537531 : CollatzResearch.WordTrace tailWord_3537531 prefixEnd_3537531 1816453733180304127393697 := by
  unfold tailWord_3537531
  simp only [CollatzResearch.WordTrace]
  refine ⟨129024355347136824040100447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86016236898091216026733631 129024355347136824040100447)
  ·
    refine ⟨193536533020705236060150671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129024355347136824040100447 193536533020705236060150671)
    ·
      refine ⟨290304799531057854090226007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193536533020705236060150671 290304799531057854090226007)
      ·
        refine ⟨435457199296586781135339011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290304799531057854090226007 435457199296586781135339011)
        ·
          refine ⟨653185798944880171703008517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435457199296586781135339011 653185798944880171703008517)
          ·
            refine ⟨122472337302165032194314097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 653185798944880171703008517 122472337302165032194314097)
            ·
              refine ⟨91854252976623774145735573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122472337302165032194314097 91854252976623774145735573)
              ·
                refine ⟨4305668108279239413081355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91854252976623774145735573 4305668108279239413081355)
                ·
                  refine ⟨6458502162418859119622033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4305668108279239413081355 6458502162418859119622033)
                  ·
                    refine ⟨4843876621814144339716525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6458502162418859119622033 4843876621814144339716525)
                    ·
                      refine ⟨1816453733180304127393697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4843876621814144339716525 1816453733180304127393697)
                      ·
                        rfl

theorem cell23_3537531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 2, 3].length) (baseStart_3537531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537531 prefixEnd_3537531 := by exact prefixLift 3537531
  have htrace : WordTrace (prefixWord ++ tailWord_3537531) baseStart_3537531 baseEnd_3537531 := by
    simpa [prefixWord, tailWord_3537531, baseEnd_3537531] using wordTrace_append hprefix tailTrace_3537531
  have hstable : (prefixWord ++ tailWord_3537531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537531).length < 2 ^ (prefixWord ++ tailWord_3537531).sum := by decide
  have hdescent : baseEnd_3537531 < baseStart_3537531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537541 : List Nat := [1, 3, 1, 1, 4, 3, 1, 2, 1, 2, 4]
def baseStart_3537541 : Nat := 118140960795 + 3537541 * 2 ^ 59
def prefixEnd_3537541 : Nat := 4983230072969 + 3 ^ 40 * 3537541 * 2
def baseEnd_3537541 : Nat := 1816458867986849088268651

theorem tailTrace_3537541 : CollatzResearch.WordTrace tailWord_3537541 prefixEnd_3537541 1816458867986849088268651 := by
  unfold tailWord_3537541
  simp only [CollatzResearch.WordTrace]
  refine ⟨129024720077100595747964477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86016480051400397165309651 129024720077100595747964477)
  ·
    refine ⟨48384270028912723405486679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129024720077100595747964477 48384270028912723405486679)
    ·
      refine ⟨72576405043369085108230019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48384270028912723405486679 72576405043369085108230019)
      ·
        refine ⟨108864607565053627662345029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72576405043369085108230019 108864607565053627662345029)
        ·
          refine ⟨20412113918447555186689693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108864607565053627662345029 20412113918447555186689693)
          ·
            refine ⟨7654542719417833195008635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20412113918447555186689693 7654542719417833195008635)
            ·
              refine ⟨11481814079126749792512953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7654542719417833195008635 11481814079126749792512953)
              ·
                refine ⟨8611360559345062344384715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11481814079126749792512953 8611360559345062344384715)
                ·
                  refine ⟨12917040839017593516577073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8611360559345062344384715 12917040839017593516577073)
                  ·
                    refine ⟨9687780629263195137432805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12917040839017593516577073 9687780629263195137432805)
                    ·
                      refine ⟨1816458867986849088268651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9687780629263195137432805 1816458867986849088268651)
                      ·
                        rfl

theorem cell23_3537541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_3537541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537541 prefixEnd_3537541 := by exact prefixLift 3537541
  have htrace : WordTrace (prefixWord ++ tailWord_3537541) baseStart_3537541 baseEnd_3537541 := by
    simpa [prefixWord, tailWord_3537541, baseEnd_3537541] using wordTrace_append hprefix tailTrace_3537541
  have hstable : (prefixWord ++ tailWord_3537541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537541).length < 2 ^ (prefixWord ++ tailWord_3537541).sum := by decide
  have hdescent : baseEnd_3537541 < baseStart_3537541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537545 : List Nat := [1, 2, 1, 1, 4, 1, 1, 7, 1, 2, 2]
def baseStart_3537545 : Nat := 118140960795 + 3537545 * 2 ^ 59
def prefixEnd_3537545 : Nat := 4983230072969 + 3 ^ 40 * 3537545 * 2
def baseEnd_3537545 : Nat := 1816460921909467072618633

theorem tailTrace_3537545 : CollatzResearch.WordTrace tailWord_3537545 prefixEnd_3537545 1816460921909467072618633 := by
  unfold tailWord_3537545
  simp only [CollatzResearch.WordTrace]
  refine ⟨129024865969086104431110089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86016577312724069620740059 129024865969086104431110089)
  ·
    refine ⟨96768649476814578323332567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129024865969086104431110089 96768649476814578323332567)
    ·
      refine ⟨145152974215221867484998851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96768649476814578323332567 145152974215221867484998851)
      ·
        refine ⟨217729461322832801227498277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145152974215221867484998851 217729461322832801227498277)
        ·
          refine ⟨40824273998031150230155927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217729461322832801227498277 40824273998031150230155927)
          ·
            refine ⟨61236410997046725345233891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40824273998031150230155927 61236410997046725345233891)
            ·
              refine ⟨91854616495570088017850837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61236410997046725345233891 91854616495570088017850837)
              ·
                refine ⟨2152842574114923937918379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 91854616495570088017850837 2152842574114923937918379)
                ·
                  refine ⟨3229263861172385906877569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2152842574114923937918379 3229263861172385906877569)
                  ·
                    refine ⟨2421947895879289430158177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3229263861172385906877569 2421947895879289430158177)
                    ·
                      refine ⟨1816460921909467072618633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2421947895879289430158177 1816460921909467072618633)
                      ·
                        rfl

theorem cell23_3537545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 7, 1, 2, 2].length) (baseStart_3537545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537545 prefixEnd_3537545 := by exact prefixLift 3537545
  have htrace : WordTrace (prefixWord ++ tailWord_3537545) baseStart_3537545 baseEnd_3537545 := by
    simpa [prefixWord, tailWord_3537545, baseEnd_3537545] using wordTrace_append hprefix tailTrace_3537545
  have hstable : (prefixWord ++ tailWord_3537545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537545).length < 2 ^ (prefixWord ++ tailWord_3537545).sum := by decide
  have hdescent : baseEnd_3537545 < baseStart_3537545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537568 : List Nat := [2, 1, 1, 4, 5, 1, 1, 8]
def baseStart_3537568 : Nat := 118140960795 + 3537568 * 2 ^ 59
def prefixEnd_3537568 : Nat := 4983230072969 + 3 ^ 40 * 3537568 * 2
def baseEnd_3537568 : Nat := 67276767850537795653001

theorem tailTrace_3537568 : CollatzResearch.WordTrace tailWord_3537568 prefixEnd_3537568 67276767850537795653001 := by
  unfold tailWord_3537568
  simp only [CollatzResearch.WordTrace]
  refine ⟨64512852424001389679598679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86017136565335186239464905 64512852424001389679598679)
  ·
    refine ⟨96769278636002084519398019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64512852424001389679598679 96769278636002084519398019)
    ·
      refine ⟨145153917954003126779097029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96769278636002084519398019 145153917954003126779097029)
      ·
        refine ⟨27216359616375586271080693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145153917954003126779097029 27216359616375586271080693)
        ·
          refine ⟨2551533714035211212913815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27216359616375586271080693 2551533714035211212913815)
          ·
            refine ⟨3827300571052816819370723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2551533714035211212913815 3827300571052816819370723)
            ·
              refine ⟨5740950856579225229056085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3827300571052816819370723 5740950856579225229056085)
              ·
                refine ⟨67276767850537795653001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5740950856579225229056085 67276767850537795653001)
                ·
                  rfl

theorem cell23_3537568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 8].length) (baseStart_3537568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537568 prefixEnd_3537568 := by exact prefixLift 3537568
  have htrace : WordTrace (prefixWord ++ tailWord_3537568) baseStart_3537568 baseEnd_3537568 := by
    simpa [prefixWord, tailWord_3537568, baseEnd_3537568] using wordTrace_append hprefix tailTrace_3537568
  have hstable : (prefixWord ++ tailWord_3537568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537568).length < 2 ^ (prefixWord ++ tailWord_3537568).sum := by decide
  have hdescent : baseEnd_3537568 < baseStart_3537568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537575 : List Nat := [1, 1, 6, 3, 1, 1, 2, 1, 1, 2, 4]
def baseStart_3537575 : Nat := 118140960795 + 3537575 * 2 ^ 59
def prefixEnd_3537575 : Nat := 4983230072969 + 3 ^ 40 * 3537575 * 2
def baseEnd_3537575 : Nat := 1816476326329101955243495

theorem tailTrace_3537575 : CollatzResearch.WordTrace tailWord_3537575 prefixEnd_3537575 1816476326329101955243495 := by
  unfold tailWord_3537575
  simp only [CollatzResearch.WordTrace]
  refine ⟨129025960158977419554702179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86017306772651613036468119 129025960158977419554702179)
  ·
    refine ⟨193538940238466129332053269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129025960158977419554702179 193538940238466129332053269)
    ·
      refine ⟨9072137823678099812439997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 193538940238466129332053269 9072137823678099812439997)
      ·
        refine ⟨3402051683879287429664999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9072137823678099812439997 3402051683879287429664999)
        ·
          refine ⟨5103077525818931144497499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3402051683879287429664999 5103077525818931144497499)
          ·
            refine ⟨7654616288728396716746249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5103077525818931144497499 7654616288728396716746249)
            ·
              refine ⟨5740962216546297537559687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7654616288728396716746249 5740962216546297537559687)
              ·
                refine ⟨8611443324819446306339531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5740962216546297537559687 8611443324819446306339531)
                ·
                  refine ⟨12917164987229169459509297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8611443324819446306339531 12917164987229169459509297)
                  ·
                    refine ⟨9687873740421877094631973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12917164987229169459509297 9687873740421877094631973)
                    ·
                      refine ⟨1816476326329101955243495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9687873740421877094631973 1816476326329101955243495)
                      ·
                        rfl

theorem cell23_3537575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_3537575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537575 prefixEnd_3537575 := by exact prefixLift 3537575
  have htrace : WordTrace (prefixWord ++ tailWord_3537575) baseStart_3537575 baseEnd_3537575 := by
    simpa [prefixWord, tailWord_3537575, baseEnd_3537575] using wordTrace_append hprefix tailTrace_3537575
  have hstable : (prefixWord ++ tailWord_3537575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537575).length < 2 ^ (prefixWord ++ tailWord_3537575).sum := by decide
  have hdescent : baseEnd_3537575 < baseStart_3537575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537584 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 4]
def baseStart_3537584 : Nat := 118140960795 + 3537584 * 2 ^ 59
def prefixEnd_3537584 : Nat := 4983230072969 + 3 ^ 40 * 3537584 * 2
def baseEnd_3537584 : Nat := 1816480947654992420030953

theorem tailTrace_3537584 : CollatzResearch.WordTrace tailWord_3537584 prefixEnd_3537584 1816480947654992420030953 := by
  unfold tailWord_3537584
  simp only [CollatzResearch.WordTrace]
  refine ⟨64513144207972407045889903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86017525610629876061186537 64513144207972407045889903)
  ·
    refine ⟨96769716311958610568834855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64513144207972407045889903 96769716311958610568834855)
    ·
      refine ⟨145154574467937915853252283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96769716311958610568834855 145154574467937915853252283)
      ·
        refine ⟨217731861701906873779878425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145154574467937915853252283 217731861701906873779878425)
        ·
          refine ⟨163298896276430155334908819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217731861701906873779878425 163298896276430155334908819)
          ·
            refine ⟨244948344414645233002363229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163298896276430155334908819 244948344414645233002363229)
            ·
              refine ⟨91855629155491962375886211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244948344414645233002363229 91855629155491962375886211)
              ·
                refine ⟨137783443733237943563829317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91855629155491962375886211 137783443733237943563829317)
                ·
                  refine ⟨25834395699982114418217997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137783443733237943563829317 25834395699982114418217997)
                  ·
                    refine ⟨9687898387493292906831749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25834395699982114418217997 9687898387493292906831749)
                    ·
                      refine ⟨1816480947654992420030953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9687898387493292906831749 1816480947654992420030953)
                      ·
                        rfl

theorem cell23_3537584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 4].length) (baseStart_3537584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537584 prefixEnd_3537584 := by exact prefixLift 3537584
  have htrace : WordTrace (prefixWord ++ tailWord_3537584) baseStart_3537584 baseEnd_3537584 := by
    simpa [prefixWord, tailWord_3537584, baseEnd_3537584] using wordTrace_append hprefix tailTrace_3537584
  have hstable : (prefixWord ++ tailWord_3537584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537584).length < 2 ^ (prefixWord ++ tailWord_3537584).sum := by decide
  have hdescent : baseEnd_3537584 < baseStart_3537584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537594 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 1, 8]
def baseStart_3537594 : Nat := 118140960795 + 3537594 * 2 ^ 59
def prefixEnd_3537594 : Nat := 4983230072969 + 3 ^ 40 * 3537594 * 2
def baseEnd_3537594 : Nat := 605495360820512460301969

theorem tailTrace_3537594 : CollatzResearch.WordTrace tailWord_3537594 prefixEnd_3537594 605495360820512460301969 := by
  unfold tailWord_3537594
  simp only [CollatzResearch.WordTrace]
  refine ⟨32256663286477146449910959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86017768763939057199762557 32256663286477146449910959)
  ·
    refine ⟨48384994929715719674866439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32256663286477146449910959 48384994929715719674866439)
    ·
      refine ⟨72577492394573579512299659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48384994929715719674866439 72577492394573579512299659)
      ·
        refine ⟨108866238591860369268449489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72577492394573579512299659 108866238591860369268449489)
        ·
          refine ⟨81649678943895276951337117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108866238591860369268449489 81649678943895276951337117)
          ·
            refine ⟨30618629603960728856751419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81649678943895276951337117 30618629603960728856751419)
            ·
              refine ⟨45927944405941093285127129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30618629603960728856751419 45927944405941093285127129)
              ·
                refine ⟨34445958304455819963845347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45927944405941093285127129 34445958304455819963845347)
                ·
                  refine ⟨51668937456683729945768021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34445958304455819963845347 51668937456683729945768021)
                  ·
                    refine ⟨605495360820512460301969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51668937456683729945768021 605495360820512460301969)
                    ·
                      rfl

theorem cell23_3537594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 1, 8].length) (baseStart_3537594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537594 prefixEnd_3537594 := by exact prefixLift 3537594
  have htrace : WordTrace (prefixWord ++ tailWord_3537594) baseStart_3537594 baseEnd_3537594 := by
    simpa [prefixWord, tailWord_3537594, baseEnd_3537594] using wordTrace_append hprefix tailTrace_3537594
  have hstable : (prefixWord ++ tailWord_3537594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537594).length < 2 ^ (prefixWord ++ tailWord_3537594).sum := by decide
  have hdescent : baseEnd_3537594 < baseStart_3537594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537606 : List Nat := [6, 1, 2, 1, 3, 1, 1, 2, 2, 4]
def baseStart_3537606 : Nat := 118140960795 + 3537606 * 2 ^ 59
def prefixEnd_3537606 : Nat := 4983230072969 + 3 ^ 40 * 3537606 * 2
def baseEnd_3537606 : Nat := 605497414743130444651951

theorem tailTrace_3537606 : CollatzResearch.WordTrace tailWord_3537606 prefixEnd_3537606 605497414743130444651951 := by
  unfold tailWord_3537606
  simp only [CollatzResearch.WordTrace]
  refine ⟨4032096588183284745283771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 86018060547910074566053781 4032096588183284745283771)
  ·
    refine ⟨6048144882274927117925657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4032096588183284745283771 6048144882274927117925657)
    ·
      refine ⟨4536108661706195338444243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6048144882274927117925657 4536108661706195338444243)
      ·
        refine ⟨6804162992559293007666365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4536108661706195338444243 6804162992559293007666365)
        ·
          refine ⟨2551561122209734877874887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6804162992559293007666365 2551561122209734877874887)
          ·
            refine ⟨3827341683314602316812331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2551561122209734877874887 3827341683314602316812331)
            ·
              refine ⟨5741012524971903475218497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3827341683314602316812331 5741012524971903475218497)
              ·
                refine ⟨4305759393728927606413873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5741012524971903475218497 4305759393728927606413873)
                ·
                  refine ⟨3229319545296695704810405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4305759393728927606413873 3229319545296695704810405)
                  ·
                    refine ⟨605497414743130444651951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3229319545296695704810405 605497414743130444651951)
                    ·
                      rfl

theorem cell23_3537606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_3537606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537606 prefixEnd_3537606 := by exact prefixLift 3537606
  have htrace : WordTrace (prefixWord ++ tailWord_3537606) baseStart_3537606 baseEnd_3537606 := by
    simpa [prefixWord, tailWord_3537606, baseEnd_3537606] using wordTrace_append hprefix tailTrace_3537606
  have hstable : (prefixWord ++ tailWord_3537606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537606).length < 2 ^ (prefixWord ++ tailWord_3537606).sum := by decide
  have hdescent : baseEnd_3537606 < baseStart_3537606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537612 : List Nat := [2, 2, 1, 5, 1, 3, 1, 2, 2, 1, 3]
def baseStart_3537612 : Nat := 118140960795 + 3537612 * 2 ^ 59
def prefixEnd_3537612 : Nat := 4983230072969 + 3 ^ 40 * 3537612 * 2
def baseEnd_3537612 : Nat := 1816495325113318310480825

theorem tailTrace_3537612 : CollatzResearch.WordTrace tailWord_3537612 prefixEnd_3537612 1816495325113318310480825 := by
  unfold tailWord_3537612
  simp only [CollatzResearch.WordTrace]
  refine ⟨64513654829921687436899545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86018206439895583249199393 64513654829921687436899545)
  ·
    refine ⟨48385241122441265577674659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64513654829921687436899545 48385241122441265577674659)
    ·
      refine ⟨72577861683661898366511989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48385241122441265577674659 72577861683661898366511989)
      ·
        refine ⟨6804174532843302971860499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72577861683661898366511989 6804174532843302971860499)
        ·
          refine ⟨10206261799264954457790749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6804174532843302971860499 10206261799264954457790749)
          ·
            refine ⟨3827348174724357921671531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10206261799264954457790749 3827348174724357921671531)
            ·
              refine ⟨5741022262086536882507297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3827348174724357921671531 5741022262086536882507297)
              ·
                refine ⟨4305766696564902661880473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5741022262086536882507297 4305766696564902661880473)
                ·
                  refine ⟨3229325022423676996410355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4305766696564902661880473 3229325022423676996410355)
                  ·
                    refine ⟨4843987533635515494615533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3229325022423676996410355 4843987533635515494615533)
                    ·
                      refine ⟨1816495325113318310480825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4843987533635515494615533 1816495325113318310480825)
                      ·
                        rfl

theorem cell23_3537612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_3537612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537612 prefixEnd_3537612 := by exact prefixLift 3537612
  have htrace : WordTrace (prefixWord ++ tailWord_3537612) baseStart_3537612 baseEnd_3537612 := by
    simpa [prefixWord, tailWord_3537612, baseEnd_3537612] using wordTrace_append hprefix tailTrace_3537612
  have hstable : (prefixWord ++ tailWord_3537612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537612).length < 2 ^ (prefixWord ++ tailWord_3537612).sum := by decide
  have hdescent : baseEnd_3537612 < baseStart_3537612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537628 : List Nat := [2, 2, 5, 1, 1, 1, 2, 1, 2, 6]
def baseStart_3537628 : Nat := 118140960795 + 3537628 * 2 ^ 59
def prefixEnd_3537628 : Nat := 4983230072969 + 3 ^ 40 * 3537628 * 2
def baseEnd_3537628 : Nat := 605501180267930082626917

theorem tailTrace_3537628 : CollatzResearch.WordTrace tailWord_3537628 prefixEnd_3537628 605501180267930082626917 := by
  unfold tailWord_3537628
  simp only [CollatzResearch.WordTrace]
  refine ⟨64513946613892704803190769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86018595485190273070921025 64513946613892704803190769)
  ·
    refine ⟨48385459960419528602393077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64513946613892704803190769 48385459960419528602393077)
    ·
      refine ⟨4536136871289330806474351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48385459960419528602393077 4536136871289330806474351)
      ·
        refine ⟨6804205306933996209711527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4536136871289330806474351 6804205306933996209711527)
        ·
          refine ⟨10206307960400994314567291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6804205306933996209711527 10206307960400994314567291)
          ·
            refine ⟨15309461940601491471850937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10206307960400994314567291 15309461940601491471850937)
            ·
              refine ⟨11482096455451118603888203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15309461940601491471850937 11482096455451118603888203)
              ·
                refine ⟨17223144683176677905832305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11482096455451118603888203 17223144683176677905832305)
                ·
                  refine ⟨12917358512382508429374229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17223144683176677905832305 12917358512382508429374229)
                  ·
                    refine ⟨605501180267930082626917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12917358512382508429374229 605501180267930082626917)
                    ·
                      rfl

theorem cell23_3537628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_3537628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537628 prefixEnd_3537628 := by exact prefixLift 3537628
  have htrace : WordTrace (prefixWord ++ tailWord_3537628) baseStart_3537628 baseEnd_3537628 := by
    simpa [prefixWord, tailWord_3537628, baseEnd_3537628] using wordTrace_append hprefix tailTrace_3537628
  have hstable : (prefixWord ++ tailWord_3537628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537628).length < 2 ^ (prefixWord ++ tailWord_3537628).sum := by decide
  have hdescent : baseEnd_3537628 < baseStart_3537628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537631 : List Nat := [1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 4]
def baseStart_3537631 : Nat := 118140960795 + 3537631 * 2 ^ 59
def prefixEnd_3537631 : Nat := 4983230072969 + 3 ^ 40 * 3537631 * 2
def baseEnd_3537631 : Nat := 1816505081245753736143237

theorem tailTrace_3537631 : CollatzResearch.WordTrace tailWord_3537631 prefixEnd_3537631 1816505081245753736143237 := by
  unfold tailWord_3537631
  simp only [CollatzResearch.WordTrace]
  refine ⟨129028002646774541118740747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86018668431183027412493831 129028002646774541118740747)
  ·
    refine ⟨193542003970161811678111121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129028002646774541118740747 193542003970161811678111121)
    ·
      refine ⟨145156502977621358758583341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193542003970161811678111121 145156502977621358758583341)
      ·
        refine ⟨54433688616608009534468753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145156502977621358758583341 54433688616608009534468753)
        ·
          refine ⟨40825266462456007150851565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54433688616608009534468753 40825266462456007150851565)
          ·
            refine ⟨15309474923421002681569337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40825266462456007150851565 15309474923421002681569337)
            ·
              refine ⟨11482106192565752011177003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15309474923421002681569337 11482106192565752011177003)
              ·
                refine ⟨17223159288848628016765505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11482106192565752011177003 17223159288848628016765505)
                ·
                  refine ⟨12917369466636471012574129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17223159288848628016765505 12917369466636471012574129)
                  ·
                    refine ⟨9688027099977353259430597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12917369466636471012574129 9688027099977353259430597)
                    ·
                      refine ⟨1816505081245753736143237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9688027099977353259430597 1816505081245753736143237)
                      ·
                        rfl

theorem cell23_3537631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_3537631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537631 prefixEnd_3537631 := by exact prefixLift 3537631
  have htrace : WordTrace (prefixWord ++ tailWord_3537631) baseStart_3537631 baseEnd_3537631 := by
    simpa [prefixWord, tailWord_3537631, baseEnd_3537631] using wordTrace_append hprefix tailTrace_3537631
  have hstable : (prefixWord ++ tailWord_3537631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537631).length < 2 ^ (prefixWord ++ tailWord_3537631).sum := by decide
  have hdescent : baseEnd_3537631 < baseStart_3537631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537635 : List Nat := [1, 1, 1, 7, 1, 1, 3, 1, 1, 4, 2]
def baseStart_3537635 : Nat := 118140960795 + 3537635 * 2 ^ 59
def prefixEnd_3537635 : Nat := 4983230072969 + 3 ^ 40 * 3537635 * 2
def baseEnd_3537635 : Nat := 1816507135168371720493219

theorem tailTrace_3537635 : CollatzResearch.WordTrace tailWord_3537635 prefixEnd_3537635 1816507135168371720493219 := by
  unfold tailWord_3537635
  simp only [CollatzResearch.WordTrace]
  refine ⟨129028148538760049801886359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86018765692506699867924239 129028148538760049801886359)
  ·
    refine ⟨193542222808140074702829539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129028148538760049801886359 193542222808140074702829539)
    ·
      refine ⟨290313334212210112054244309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193542222808140074702829539 290313334212210112054244309)
      ·
        refine ⟨6804218770598674501271351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 290313334212210112054244309 6804218770598674501271351)
        ·
          refine ⟨10206328155898011751907027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6804218770598674501271351 10206328155898011751907027)
          ·
            refine ⟨15309492233847017627860541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10206328155898011751907027 15309492233847017627860541)
            ·
              refine ⟨5741059587692631610447703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15309492233847017627860541 5741059587692631610447703)
              ·
                refine ⟨8611589381538947415671555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5741059587692631610447703 8611589381538947415671555)
                ·
                  refine ⟨12917384072308421123507333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8611589381538947415671555 12917384072308421123507333)
                  ·
                    refine ⟨2422009513557828960657625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12917384072308421123507333 2422009513557828960657625)
                    ·
                      refine ⟨1816507135168371720493219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2422009513557828960657625 1816507135168371720493219)
                      ·
                        rfl

theorem cell23_3537635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_3537635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537635 prefixEnd_3537635 := by exact prefixLift 3537635
  have htrace : WordTrace (prefixWord ++ tailWord_3537635) baseStart_3537635 baseEnd_3537635 := by
    simpa [prefixWord, tailWord_3537635, baseEnd_3537635] using wordTrace_append hprefix tailTrace_3537635
  have hstable : (prefixWord ++ tailWord_3537635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537635).length < 2 ^ (prefixWord ++ tailWord_3537635).sum := by decide
  have hdescent : baseEnd_3537635 < baseStart_3537635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537658 : List Nat := [3, 1, 1, 1, 1, 3, 5, 3, 5]
def baseStart_3537658 : Nat := 118140960795 + 3537658 * 2 ^ 59
def prefixEnd_3537658 : Nat := 4983230072969 + 3 ^ 40 * 3537658 * 2
def baseEnd_3537658 : Nat := 201835438358158347833957

theorem tailTrace_3537658 : CollatzResearch.WordTrace tailWord_3537658 prefixEnd_3537658 201835438358158347833957 := by
  unfold tailWord_3537658
  simp only [CollatzResearch.WordTrace]
  refine ⟨32257246854419181182493407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86019324945117816486649085 32257246854419181182493407)
  ·
    refine ⟨48385870281628771773740111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32257246854419181182493407 48385870281628771773740111)
    ·
      refine ⟨72578805422443157660610167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48385870281628771773740111 72578805422443157660610167)
      ·
        refine ⟨108868208133664736490915251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72578805422443157660610167 108868208133664736490915251)
        ·
          refine ⟨163302312200497104736372877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108868208133664736490915251 163302312200497104736372877)
          ·
            refine ⟨61238367075186414276139829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163302312200497104736372877 61238367075186414276139829)
            ·
              refine ⟨5741096913298726338388109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61238367075186414276139829 5741096913298726338388109)
              ·
                refine ⟨2152911342487022376895541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5741096913298726338388109 2152911342487022376895541)
                ·
                  refine ⟨201835438358158347833957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2152911342487022376895541 201835438358158347833957)
                  ·
                    rfl

theorem cell23_3537658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 3, 5].length) (baseStart_3537658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537658 prefixEnd_3537658 := by exact prefixLift 3537658
  have htrace : WordTrace (prefixWord ++ tailWord_3537658) baseStart_3537658 baseEnd_3537658 := by
    simpa [prefixWord, tailWord_3537658, baseEnd_3537658] using wordTrace_append hprefix tailTrace_3537658
  have hstable : (prefixWord ++ tailWord_3537658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537658).length < 2 ^ (prefixWord ++ tailWord_3537658).sum := by decide
  have hdescent : baseEnd_3537658 < baseStart_3537658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537678 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2]
def baseStart_3537678 : Nat := 118140960795 + 3537678 * 2 ^ 59
def prefixEnd_3537678 : Nat := 4983230072969 + 3 ^ 40 * 3537678 * 2
def baseEnd_3537678 : Nat := 1816529214836515052255521

theorem tailTrace_3537678 : CollatzResearch.WordTrace tailWord_3537678 prefixEnd_3537678 1816529214836515052255521 := by
  unfold tailWord_3537678
  simp only [CollatzResearch.WordTrace]
  refine ⟨16128714609700533518212711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86019811251736178763801125 16128714609700533518212711)
  ·
    refine ⟨24193071914550800277319067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16128714609700533518212711 24193071914550800277319067)
    ·
      refine ⟨36289607871826200415978601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24193071914550800277319067 36289607871826200415978601)
      ·
        refine ⟨27217205903869650311983951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36289607871826200415978601 27217205903869650311983951)
        ·
          refine ⟨40825808855804475467975927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27217205903869650311983951 40825808855804475467975927)
          ·
            refine ⟨61238713283706713201963891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40825808855804475467975927 61238713283706713201963891)
            ·
              refine ⟨91858069925560069802945837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61238713283706713201963891 91858069925560069802945837)
              ·
                refine ⟨34446776222085026176104689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91858069925560069802945837 34446776222085026176104689)
                ·
                  refine ⟨25835082166563769632078517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34446776222085026176104689 25835082166563769632078517)
                  ·
                    refine ⟨2422038953115353403007361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25835082166563769632078517 2422038953115353403007361)
                    ·
                      refine ⟨1816529214836515052255521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2422038953115353403007361 1816529214836515052255521)
                      ·
                        rfl

theorem cell23_3537678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_3537678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537678 prefixEnd_3537678 := by exact prefixLift 3537678
  have htrace : WordTrace (prefixWord ++ tailWord_3537678) baseStart_3537678 baseEnd_3537678 := by
    simpa [prefixWord, tailWord_3537678, baseEnd_3537678] using wordTrace_append hprefix tailTrace_3537678
  have hstable : (prefixWord ++ tailWord_3537678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537678).length < 2 ^ (prefixWord ++ tailWord_3537678).sum := by decide
  have hdescent : baseEnd_3537678 < baseStart_3537678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537708 : List Nat := [2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 4]
def baseStart_3537708 : Nat := 118140960795 + 3537708 * 2 ^ 59
def prefixEnd_3537708 : Nat := 4983230072969 + 3 ^ 40 * 3537708 * 2
def baseEnd_3537708 : Nat := 1816544619256149934880383

theorem tailTrace_3537708 : CollatzResearch.WordTrace tailWord_3537708 prefixEnd_3537708 1816544619256149934880383 := by
  unfold tailWord_3537708
  simp only [CollatzResearch.WordTrace]
  refine ⟨64515405533747791634646889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86020540711663722179529185 64515405533747791634646889)
  ·
    refine ⟨48386554150310843725985167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64515405533747791634646889 48386554150310843725985167)
    ·
      refine ⟨72579831225466265588977751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48386554150310843725985167 72579831225466265588977751)
      ·
        refine ⟨108869746838199398383466627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72579831225466265588977751 108869746838199398383466627)
        ·
          refine ⟨163304620257299097575199941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108869746838199398383466627 163304620257299097575199941)
          ·
            refine ⟨30619616298243580795349989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163304620257299097575199941 30619616298243580795349989)
            ·
              refine ⟨5741178055920671399128123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30619616298243580795349989 5741178055920671399128123)
              ·
                refine ⟨8611767083881007098692185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5741178055920671399128123 8611767083881007098692185)
                ·
                  refine ⟨6458825312910755324019139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8611767083881007098692185 6458825312910755324019139)
                  ·
                    refine ⟨9688237969366132986028709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6458825312910755324019139 9688237969366132986028709)
                    ·
                      refine ⟨1816544619256149934880383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9688237969366132986028709 1816544619256149934880383)
                      ·
                        rfl

theorem cell23_3537708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 4].length) (baseStart_3537708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537708 prefixEnd_3537708 := by exact prefixLift 3537708
  have htrace : WordTrace (prefixWord ++ tailWord_3537708) baseStart_3537708 baseEnd_3537708 := by
    simpa [prefixWord, tailWord_3537708, baseEnd_3537708] using wordTrace_append hprefix tailTrace_3537708
  have hstable : (prefixWord ++ tailWord_3537708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537708).length < 2 ^ (prefixWord ++ tailWord_3537708).sum := by decide
  have hdescent : baseEnd_3537708 < baseStart_3537708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537782 : List Nat := [5, 1, 1, 3, 1, 3, 1, 2, 6]
def baseStart_3537782 : Nat := 118140960795 + 3537782 * 2 ^ 59
def prefixEnd_3537782 : Nat := 4983230072969 + 3 ^ 40 * 3537782 * 2
def baseEnd_3537782 : Nat := 201842512980509182817227

theorem tailTrace_3537782 : CollatzResearch.WordTrace tailWord_3537782 prefixEnd_3537782 201842512980509182817227 := by
  unfold tailWord_3537782
  simp only [CollatzResearch.WordTrace]
  refine ⟨8064594379326718369217975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86022340046151662604991733 8064594379326718369217975)
  ·
    refine ⟨12096891568990077553826963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8064594379326718369217975 12096891568990077553826963)
    ·
      refine ⟨18145337353485116330740445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12096891568990077553826963 18145337353485116330740445)
      ·
        refine ⟨6804501507556918624027667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18145337353485116330740445 6804501507556918624027667)
        ·
          refine ⟨10206752261335377936041501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6804501507556918624027667 10206752261335377936041501)
          ·
            refine ⟨3827532098000766726015563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10206752261335377936041501 3827532098000766726015563)
            ·
              refine ⟨5741298147001150089023345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3827532098000766726015563 5741298147001150089023345)
              ·
                refine ⟨4305973610250862566767509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5741298147001150089023345 4305973610250862566767509)
                ·
                  refine ⟨201842512980509182817227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4305973610250862566767509 201842512980509182817227)
                  ·
                    rfl

theorem cell23_3537782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_3537782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537782 prefixEnd_3537782 := by exact prefixLift 3537782
  have htrace : WordTrace (prefixWord ++ tailWord_3537782) baseStart_3537782 baseEnd_3537782 := by
    simpa [prefixWord, tailWord_3537782, baseEnd_3537782] using wordTrace_append hprefix tailTrace_3537782
  have hstable : (prefixWord ++ tailWord_3537782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537782).length < 2 ^ (prefixWord ++ tailWord_3537782).sum := by decide
  have hdescent : baseEnd_3537782 < baseStart_3537782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537791 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 3, 6]
def baseStart_3537791 : Nat := 118140960795 + 3537791 * 2 ^ 59
def prefixEnd_3537791 : Nat := 4983230072969 + 3 ^ 40 * 3537791 * 2
def baseEnd_3537791 : Nat := 605529079383491036714167

theorem tailTrace_3537791 : CollatzResearch.WordTrace tailWord_3537791 prefixEnd_3537791 605529079383491036714167 := by
  unfold tailWord_3537791
  simp only [CollatzResearch.WordTrace]
  refine ⟨129033838326194888444565227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86022558884129925629710151 129033838326194888444565227)
  ·
    refine ⟨193550757489292332666847841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129033838326194888444565227 193550757489292332666847841)
    ·
      refine ⟨145163068116969249500135881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193550757489292332666847841 145163068116969249500135881)
      ·
        refine ⟨108872301087726937125101911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145163068116969249500135881 108872301087726937125101911)
        ·
          refine ⟨163308451631590405687652867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108872301087726937125101911 163308451631590405687652867)
          ·
            refine ⟨244962677447385608531479301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163308451631590405687652867 244962677447385608531479301)
            ·
              refine ⟨45930502021384801599652369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 244962677447385608531479301 45930502021384801599652369)
              ·
                refine ⟨34447876516038601199739277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45930502021384801599652369 34447876516038601199739277)
                ·
                  refine ⟨12917953693514475449902229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34447876516038601199739277 12917953693514475449902229)
                  ·
                    refine ⟨605529079383491036714167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12917953693514475449902229 605529079383491036714167)
                    ·
                      rfl

theorem cell23_3537791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 6].length) (baseStart_3537791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537791 prefixEnd_3537791 := by exact prefixLift 3537791
  have htrace : WordTrace (prefixWord ++ tailWord_3537791) baseStart_3537791 baseEnd_3537791 := by
    simpa [prefixWord, tailWord_3537791, baseEnd_3537791] using wordTrace_append hprefix tailTrace_3537791
  have hstable : (prefixWord ++ tailWord_3537791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537791).length < 2 ^ (prefixWord ++ tailWord_3537791).sum := by decide
  have hdescent : baseEnd_3537791 < baseStart_3537791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537815 : List Nat := [1, 1, 3, 3, 1, 2, 4, 2, 1, 1, 4]
def baseStart_3537815 : Nat := 118140960795 + 3537815 * 2 ^ 59
def prefixEnd_3537815 : Nat := 4983230072969 + 3 ^ 40 * 3537815 * 2
def baseEnd_3537815 : Nat := 1816599561686181016242391

theorem tailTrace_3537815 : CollatzResearch.WordTrace tailWord_3537815 prefixEnd_3537815 1816599561686181016242391 := by
  unfold tailWord_3537815
  simp only [CollatzResearch.WordTrace]
  refine ⟨129034713678107940543438899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86023142452071960362292599 129034713678107940543438899)
  ·
    refine ⟨193552070517161910815158349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129034713678107940543438899 193552070517161910815158349)
    ·
      refine ⟨72582026443935716555684381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193552070517161910815158349 72582026443935716555684381)
      ·
        refine ⟨27218259916475893708381643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72582026443935716555684381 27218259916475893708381643)
        ·
          refine ⟨40827389874713840562572465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27218259916475893708381643 40827389874713840562572465)
          ·
            refine ⟨30620542406035380421929349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40827389874713840562572465 30620542406035380421929349)
            ·
              refine ⟨5741351701131633829111753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30620542406035380421929349 5741351701131633829111753)
              ·
                refine ⟨4306013775848725371833815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5741351701131633829111753 4306013775848725371833815)
                ·
                  refine ⟨6459020663773088057750723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4306013775848725371833815 6459020663773088057750723)
                  ·
                    refine ⟨9688530995659632086626085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6459020663773088057750723 9688530995659632086626085)
                    ·
                      refine ⟨1816599561686181016242391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9688530995659632086626085 1816599561686181016242391)
                      ·
                        rfl

theorem cell23_3537815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_3537815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537815 prefixEnd_3537815 := by exact prefixLift 3537815
  have htrace : WordTrace (prefixWord ++ tailWord_3537815) baseStart_3537815 baseEnd_3537815 := by
    simpa [prefixWord, tailWord_3537815, baseEnd_3537815] using wordTrace_append hprefix tailTrace_3537815
  have hstable : (prefixWord ++ tailWord_3537815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537815).length < 2 ^ (prefixWord ++ tailWord_3537815).sum := by decide
  have hdescent : baseEnd_3537815 < baseStart_3537815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537825 : List Nat := [1, 2, 3, 4, 1, 1, 1, 2, 4, 4]
def baseStart_3537825 : Nat := 118140960795 + 3537825 * 2 ^ 59
def prefixEnd_3537825 : Nat := 4983230072969 + 3 ^ 40 * 3537825 * 2
def baseEnd_3537825 : Nat := 605534898830908659039115

theorem tailTrace_3537825 : CollatzResearch.WordTrace tailWord_3537825 prefixEnd_3537825 605534898830908659039115 := by
  unfold tailWord_3537825
  simp only [CollatzResearch.WordTrace]
  refine ⟨129035078408071712251302929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86023385605381141500868619 129035078408071712251302929)
  ·
    refine ⟨96776308806053784188477197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129035078408071712251302929 96776308806053784188477197)
    ·
      refine ⟨36291115802270169070678949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96776308806053784188477197 36291115802270169070678949)
      ·
        refine ⟨6804584212925656700752303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36291115802270169070678949 6804584212925656700752303)
        ·
          refine ⟨10206876319388485051128455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6804584212925656700752303 10206876319388485051128455)
          ·
            refine ⟨15310314479082727576692683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10206876319388485051128455 15310314479082727576692683)
            ·
              refine ⟨22965471718624091365039025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15310314479082727576692683 22965471718624091365039025)
              ·
                refine ⟨17224103788968068523779269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22965471718624091365039025 17224103788968068523779269)
                ·
                  refine ⟨3229519460431512848208613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17224103788968068523779269 3229519460431512848208613)
                  ·
                    refine ⟨605534898830908659039115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3229519460431512848208613 605534898830908659039115)
                    ·
                      rfl

theorem cell23_3537825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_3537825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537825 prefixEnd_3537825 := by exact prefixLift 3537825
  have htrace : WordTrace (prefixWord ++ tailWord_3537825) baseStart_3537825 baseEnd_3537825 := by
    simpa [prefixWord, tailWord_3537825, baseEnd_3537825] using wordTrace_append hprefix tailTrace_3537825
  have hstable : (prefixWord ++ tailWord_3537825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537825).length < 2 ^ (prefixWord ++ tailWord_3537825).sum := by decide
  have hdescent : baseEnd_3537825 < baseStart_3537825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537826 : List Nat := [3, 3, 1, 2, 2, 3, 1, 3, 1, 1, 3]
def baseStart_3537826 : Nat := 118140960795 + 3537826 * 2 ^ 59
def prefixEnd_3537826 : Nat := 4983230072969 + 3 ^ 40 * 3537826 * 2
def baseEnd_3537826 : Nat := 1816605209973380473204841

theorem tailTrace_3537826 : CollatzResearch.WordTrace tailWord_3537826 prefixEnd_3537826 1816605209973380473204841 := by
  unfold tailWord_3537826
  simp only [CollatzResearch.WordTrace]
  refine ⟨32258778720267022355522333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86023409920712059614726221 32258778720267022355522333)
  ·
    refine ⟨12097042020100133383320875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32258778720267022355522333 12097042020100133383320875)
    ·
      refine ⟨18145563030150200074981313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12097042020100133383320875 18145563030150200074981313)
      ·
        refine ⟨13609172272612650056235985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18145563030150200074981313 13609172272612650056235985)
        ·
          refine ⟨10206879204459487542176989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13609172272612650056235985 10206879204459487542176989)
          ·
            refine ⟨3827579701672307828316371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10206879204459487542176989 3827579701672307828316371)
            ·
              refine ⟨5741369552508461742474557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3827579701672307828316371 5741369552508461742474557)
              ·
                refine ⟨2153013582190673153427959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5741369552508461742474557 2153013582190673153427959)
                ·
                  refine ⟨3229520373286009730141939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2153013582190673153427959 3229520373286009730141939)
                  ·
                    refine ⟨4844280559929014595212909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3229520373286009730141939 4844280559929014595212909)
                    ·
                      refine ⟨1816605209973380473204841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4844280559929014595212909 1816605209973380473204841)
                      ·
                        rfl

theorem cell23_3537826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_3537826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537826 prefixEnd_3537826 := by exact prefixLift 3537826
  have htrace : WordTrace (prefixWord ++ tailWord_3537826) baseStart_3537826 baseEnd_3537826 := by
    simpa [prefixWord, tailWord_3537826, baseEnd_3537826] using wordTrace_append hprefix tailTrace_3537826
  have hstable : (prefixWord ++ tailWord_3537826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537826).length < 2 ^ (prefixWord ++ tailWord_3537826).sum := by decide
  have hdescent : baseEnd_3537826 < baseStart_3537826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537828 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 3, 2, 4]
def baseStart_3537828 : Nat := 118140960795 + 3537828 * 2 ^ 59
def prefixEnd_3537828 : Nat := 4983230072969 + 3 ^ 40 * 3537828 * 2
def baseEnd_3537828 : Nat := 1816606236934689465379831

theorem tailTrace_3537828 : CollatzResearch.WordTrace tailWord_3537828 prefixEnd_3537828 1816606236934689465379831 := by
  unfold tailWord_3537828
  simp only [CollatzResearch.WordTrace]
  refine ⟨64517593913530421881831069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86023458551373895842441425 64517593913530421881831069)
  ·
    refine ⟨24194097717573908205686651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64517593913530421881831069 24194097717573908205686651)
    ·
      refine ⟨36291146576360862308529977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24194097717573908205686651 36291146576360862308529977)
      ·
        refine ⟨27218359932270646731397483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36291146576360862308529977 27218359932270646731397483)
        ·
          refine ⟨40827539898405970097096225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27218359932270646731397483 40827539898405970097096225)
          ·
            refine ⟨30620654923804477572822169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40827539898405970097096225 30620654923804477572822169)
            ·
              refine ⟨22965491192853358179616627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30620654923804477572822169 22965491192853358179616627)
              ·
                refine ⟨34448236789280037269424941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22965491192853358179616627 34448236789280037269424941)
                ·
                  refine ⟨12918088795980013976034353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34448236789280037269424941 12918088795980013976034353)
                  ·
                    refine ⟨9688566596985010482025765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12918088795980013976034353 9688566596985010482025765)
                    ·
                      refine ⟨1816606236934689465379831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9688566596985010482025765 1816606236934689465379831)
                      ·
                        rfl

theorem cell23_3537828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_3537828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537828 prefixEnd_3537828 := by exact prefixLift 3537828
  have htrace : WordTrace (prefixWord ++ tailWord_3537828) baseStart_3537828 baseEnd_3537828 := by
    simpa [prefixWord, tailWord_3537828, baseEnd_3537828] using wordTrace_append hprefix tailTrace_3537828
  have hstable : (prefixWord ++ tailWord_3537828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537828).length < 2 ^ (prefixWord ++ tailWord_3537828).sum := by decide
  have hdescent : baseEnd_3537828 < baseStart_3537828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537849 : List Nat := [1, 2, 1, 4, 2, 4, 1, 1, 3, 2, 2]
def baseStart_3537849 : Nat := 118140960795 + 3537849 * 2 ^ 59
def prefixEnd_3537849 : Nat := 4983230072969 + 3 ^ 40 * 3537849 * 2
def baseEnd_3537849 : Nat := 1816617020028433883217235

theorem tailTrace_3537849 : CollatzResearch.WordTrace tailWord_3537849 prefixEnd_3537849 1816617020028433883217235 := by
  unfold tailWord_3537849
  simp only [CollatzResearch.WordTrace]
  refine ⟨129035953759984764350176601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86023969173323176233451067 129035953759984764350176601)
  ·
    refine ⟨96776965319988573262632451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129035953759984764350176601 96776965319988573262632451)
    ·
      refine ⟨145165447979982859893948677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96776965319988573262632451 145165447979982859893948677)
      ·
        refine ⟨27218521496246786230115377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145165447979982859893948677 27218521496246786230115377)
        ·
          refine ⟨20413891122185089672586533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27218521496246786230115377 20413891122185089672586533)
          ·
            refine ⟨3827604585409704313609975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20413891122185089672586533 3827604585409704313609975)
            ·
              refine ⟨5741406878114556470414963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3827604585409704313609975 5741406878114556470414963)
              ·
                refine ⟨8612110317171834705622445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5741406878114556470414963 8612110317171834705622445)
                ·
                  refine ⟨3229541368939438014608417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8612110317171834705622445 3229541368939438014608417)
                  ·
                    refine ⟨2422156026704578510956313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3229541368939438014608417 2422156026704578510956313)
                    ·
                      refine ⟨1816617020028433883217235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2422156026704578510956313 1816617020028433883217235)
                      ·
                        rfl

theorem cell23_3537849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_3537849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537849 prefixEnd_3537849 := by exact prefixLift 3537849
  have htrace : WordTrace (prefixWord ++ tailWord_3537849) baseStart_3537849 baseEnd_3537849 := by
    simpa [prefixWord, tailWord_3537849, baseEnd_3537849] using wordTrace_append hprefix tailTrace_3537849
  have hstable : (prefixWord ++ tailWord_3537849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537849).length < 2 ^ (prefixWord ++ tailWord_3537849).sum := by decide
  have hdescent : baseEnd_3537849 < baseStart_3537849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537928 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 9]
def baseStart_3537928 : Nat := 118140960795 + 3537928 * 2 ^ 59
def prefixEnd_3537928 : Nat := 4983230072969 + 3 ^ 40 * 3537928 * 2
def baseEnd_3537928 : Nat := 201850842777793230458819

theorem tailTrace_3537928 : CollatzResearch.WordTrace tailWord_3537928 prefixEnd_3537928 201850842777793230458819 := by
  unfold tailWord_3537928
  simp only [CollatzResearch.WordTrace]
  refine ⟨64519417563349280421151219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86025890084465707228201625 64519417563349280421151219)
  ·
    refine ⟨96779126345023920631726829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64519417563349280421151219 96779126345023920631726829)
    ·
      refine ⟨36292172379383970236897561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96779126345023920631726829 36292172379383970236897561)
      ·
        refine ⟨27219129284537977677673171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36292172379383970236897561 27219129284537977677673171)
        ·
          refine ⟨40828693926806966516509757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27219129284537977677673171 40828693926806966516509757)
          ·
            refine ⟨15310760222552612443691159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40828693926806966516509757 15310760222552612443691159)
            ·
              refine ⟨22966140333828918665536739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15310760222552612443691159 22966140333828918665536739)
              ·
                refine ⟨34449210500743377998305109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22966140333828918665536739 34449210500743377998305109)
                ·
                  refine ⟨201850842777793230458819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34449210500743377998305109 201850842777793230458819)
                  ·
                    rfl

theorem cell23_3537928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 9].length) (baseStart_3537928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537928 prefixEnd_3537928 := by exact prefixLift 3537928
  have htrace : WordTrace (prefixWord ++ tailWord_3537928) baseStart_3537928 baseEnd_3537928 := by
    simpa [prefixWord, tailWord_3537928, baseEnd_3537928] using wordTrace_append hprefix tailTrace_3537928
  have hstable : (prefixWord ++ tailWord_3537928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537928).length < 2 ^ (prefixWord ++ tailWord_3537928).sum := by decide
  have hdescent : baseEnd_3537928 < baseStart_3537928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537945 : List Nat := [1, 2, 1, 2, 1, 1, 5, 5, 5]
def baseStart_3537945 : Nat := 118140960795 + 3537945 * 2 ^ 59
def prefixEnd_3537945 : Nat := 4983230072969 + 3 ^ 40 * 3537945 * 2
def baseEnd_3537945 : Nat := 201851812685696167512977

theorem tailTrace_3537945 : CollatzResearch.WordTrace tailWord_3537945 prefixEnd_3537945 201851812685696167512977 := by
  unfold tailWord_3537945
  simp only [CollatzResearch.WordTrace]
  refine ⟨129039455167636972745671289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86026303445091315163780859 129039455167636972745671289)
  ·
    refine ⟨96779591375727729559253467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129039455167636972745671289 96779591375727729559253467)
    ·
      refine ⟨145169387063591594338880201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96779591375727729559253467 145169387063591594338880201)
      ·
        refine ⟨108877040297693695754160151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145169387063591594338880201 108877040297693695754160151)
        ·
          refine ⟨163315560446540543631240227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108877040297693695754160151 163315560446540543631240227)
          ·
            refine ⟨244973340669810815446860341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163315560446540543631240227 244973340669810815446860341)
            ·
              refine ⟨22966250687794763948143157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 244973340669810815446860341 22966250687794763948143157)
              ·
                refine ⟨2153086001980759120138421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22966250687794763948143157 2153086001980759120138421)
                ·
                  refine ⟨201851812685696167512977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2153086001980759120138421 201851812685696167512977)
                  ·
                    rfl

theorem cell23_3537945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 5, 5].length) (baseStart_3537945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537945 prefixEnd_3537945 := by exact prefixLift 3537945
  have htrace : WordTrace (prefixWord ++ tailWord_3537945) baseStart_3537945 baseEnd_3537945 := by
    simpa [prefixWord, tailWord_3537945, baseEnd_3537945] using wordTrace_append hprefix tailTrace_3537945
  have hstable : (prefixWord ++ tailWord_3537945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537945).length < 2 ^ (prefixWord ++ tailWord_3537945).sum := by decide
  have hdescent : baseEnd_3537945 < baseStart_3537945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537955 : List Nat := [1, 1, 1, 4, 3, 2, 1, 2, 2, 3, 3]
def baseStart_3537955 : Nat := 118140960795 + 3537955 * 2 ^ 59
def prefixEnd_3537955 : Nat := 4983230072969 + 3 ^ 40 * 3537955 * 2
def baseEnd_3537955 : Nat := 1816671448977810468491747

theorem tailTrace_3537955 : CollatzResearch.WordTrace tailWord_3537955 prefixEnd_3537955 1816671448977810468491747 := by
  unfold tailWord_3537955
  simp only [CollatzResearch.WordTrace]
  refine ⟨129039819897600744453535319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86026546598400496302356879 129039819897600744453535319)
  ·
    refine ⟨193559729846401116680302979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129039819897600744453535319 193559729846401116680302979)
    ·
      refine ⟨290339594769601675020454469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193559729846401116680302979 290339594769601675020454469)
      ·
        refine ⟨54438674019300314066335213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 290339594769601675020454469 54438674019300314066335213)
        ·
          refine ⟨20414502757237617774875705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54438674019300314066335213 20414502757237617774875705)
          ·
            refine ⟨15310877067928213331156779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20414502757237617774875705 15310877067928213331156779)
            ·
              refine ⟨22966315601892319996735169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15310877067928213331156779 22966315601892319996735169)
              ·
                refine ⟨17224736701419239997551377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22966315601892319996735169 17224736701419239997551377)
                ·
                  refine ⟨12918552526064429998163533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17224736701419239997551377 12918552526064429998163533)
                  ·
                    refine ⟨4844457197274161249311325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12918552526064429998163533 4844457197274161249311325)
                    ·
                      refine ⟨1816671448977810468491747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4844457197274161249311325 1816671448977810468491747)
                      ·
                        rfl

theorem cell23_3537955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_3537955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537955 prefixEnd_3537955 := by exact prefixLift 3537955
  have htrace : WordTrace (prefixWord ++ tailWord_3537955) baseStart_3537955 baseEnd_3537955 := by
    simpa [prefixWord, tailWord_3537955, baseEnd_3537955] using wordTrace_append hprefix tailTrace_3537955
  have hstable : (prefixWord ++ tailWord_3537955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537955).length < 2 ^ (prefixWord ++ tailWord_3537955).sum := by decide
  have hdescent : baseEnd_3537955 < baseStart_3537955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537956 : List Nat := [2, 3, 1, 4, 1, 1, 3, 2, 2, 2, 2]
def baseStart_3537956 : Nat := 118140960795 + 3537956 * 2 ^ 59
def prefixEnd_3537956 : Nat := 4983230072969 + 3 ^ 40 * 3537956 * 2
def baseEnd_3537956 : Nat := 1816671962458464964579243

theorem tailTrace_3537956 : CollatzResearch.WordTrace tailWord_3537956 prefixEnd_3537956 1816671962458464964579243 := by
  unfold tailWord_3537956
  simp only [CollatzResearch.WordTrace]
  refine ⟨64519928185298560812160861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86026570913731414416214481 64519928185298560812160861)
  ·
    refine ⟨24194973069486960304560323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64519928185298560812160861 24194973069486960304560323)
    ·
      refine ⟨36292459604230440456840485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24194973069486960304560323 36292459604230440456840485)
      ·
        refine ⟨6804836175793207585657591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36292459604230440456840485 6804836175793207585657591)
        ·
          refine ⟨10207254263689811378486387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6804836175793207585657591 10207254263689811378486387)
          ·
            refine ⟨15310881395534717067729581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10207254263689811378486387 15310881395534717067729581)
            ·
              refine ⟨5741580523325518900398593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15310881395534717067729581 5741580523325518900398593)
              ·
                refine ⟨4306185392494139175298945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5741580523325518900398593 4306185392494139175298945)
                ·
                  refine ⟨3229639044370604381474209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4306185392494139175298945 3229639044370604381474209)
                  ·
                    refine ⟨2422229283277953286105657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3229639044370604381474209 2422229283277953286105657)
                    ·
                      refine ⟨1816671962458464964579243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2422229283277953286105657 1816671962458464964579243)
                      ·
                        rfl

theorem cell23_3537956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_3537956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537956 prefixEnd_3537956 := by exact prefixLift 3537956
  have htrace : WordTrace (prefixWord ++ tailWord_3537956) baseStart_3537956 baseEnd_3537956 := by
    simpa [prefixWord, tailWord_3537956, baseEnd_3537956] using wordTrace_append hprefix tailTrace_3537956
  have hstable : (prefixWord ++ tailWord_3537956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537956).length < 2 ^ (prefixWord ++ tailWord_3537956).sum := by decide
  have hdescent : baseEnd_3537956 < baseStart_3537956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537962 : List Nat := [3, 1, 4, 1, 3, 1, 2, 1, 7]
def baseStart_3537962 : Nat := 118140960795 + 3537962 * 2 ^ 59
def prefixEnd_3537962 : Nat := 4983230072969 + 3 ^ 40 * 3537962 * 2
def baseEnd_3537962 : Nat := 201852782593599104567135

theorem tailTrace_3537962 : CollatzResearch.WordTrace tailWord_3537962 prefixEnd_3537962 201852782593599104567135 := by
  unfold tailWord_3537962
  simp only [CollatzResearch.WordTrace]
  refine ⟨32260018802143846162260035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86026716805716923099360093 32260018802143846162260035)
  ·
    refine ⟨48390028203215769243390053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32260018802143846162260035 48390028203215769243390053)
    ·
      refine ⟨9073130288102956733135635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48390028203215769243390053 9073130288102956733135635)
      ·
        refine ⟨13609695432154435099703453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9073130288102956733135635 13609695432154435099703453)
        ·
          refine ⟨5103635787057913162388795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13609695432154435099703453 5103635787057913162388795)
          ·
            refine ⟨7655453680586869743583193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5103635787057913162388795 7655453680586869743583193)
            ·
              refine ⟨5741590260440152307687395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7655453680586869743583193 5741590260440152307687395)
              ·
                refine ⟨8612385390660228461531093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5741590260440152307687395 8612385390660228461531093)
                ·
                  refine ⟨201852782593599104567135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8612385390660228461531093 201852782593599104567135)
                  ·
                    rfl

theorem cell23_3537962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 7].length) (baseStart_3537962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537962 prefixEnd_3537962 := by exact prefixLift 3537962
  have htrace : WordTrace (prefixWord ++ tailWord_3537962) baseStart_3537962 baseEnd_3537962 := by
    simpa [prefixWord, tailWord_3537962, baseEnd_3537962] using wordTrace_append hprefix tailTrace_3537962
  have hstable : (prefixWord ++ tailWord_3537962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537962).length < 2 ^ (prefixWord ++ tailWord_3537962).sum := by decide
  have hdescent : baseEnd_3537962 < baseStart_3537962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537968 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 7]
def baseStart_3537968 : Nat := 118140960795 + 3537968 * 2 ^ 59
def prefixEnd_3537968 : Nat := 4983230072969 + 3 ^ 40 * 3537968 * 2
def baseEnd_3537968 : Nat := 1816678124226318917629187

theorem tailTrace_3537968 : CollatzResearch.WordTrace tailWord_3537968 prefixEnd_3537968 1816678124226318917629187 := by
  unfold tailWord_3537968
  simp only [CollatzResearch.WordTrace]
  refine ⟨64520147023276823836879279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86026862697702431782505705 64520147023276823836879279)
  ·
    refine ⟨96780220534915235755318919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64520147023276823836879279 96780220534915235755318919)
    ·
      refine ⟨145170330802372853632978379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96780220534915235755318919 145170330802372853632978379)
      ·
        refine ⟨217755496203559280449467569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145170330802372853632978379 217755496203559280449467569)
        ·
          refine ⟨163316622152669460337100677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217755496203559280449467569 163316622152669460337100677)
          ·
            refine ⟨30621866653625523813206377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163316622152669460337100677 30621866653625523813206377)
            ·
              refine ⟨22966399990219142859904783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30621866653625523813206377 22966399990219142859904783)
              ·
                refine ⟨34449599985328714289857175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22966399990219142859904783 34449599985328714289857175)
                ·
                  refine ⟨51674399977993071434785763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34449599985328714289857175 51674399977993071434785763)
                  ·
                    refine ⟨77511599966989607152178645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51674399977993071434785763 77511599966989607152178645)
                    ·
                      refine ⟨1816678124226318917629187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 77511599966989607152178645 1816678124226318917629187)
                      ·
                        rfl

theorem cell23_3537968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 7].length) (baseStart_3537968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3537968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3537968 prefixEnd_3537968 := by exact prefixLift 3537968
  have htrace : WordTrace (prefixWord ++ tailWord_3537968) baseStart_3537968 baseEnd_3537968 := by
    simpa [prefixWord, tailWord_3537968, baseEnd_3537968] using wordTrace_append hprefix tailTrace_3537968
  have hstable : (prefixWord ++ tailWord_3537968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537968).length < 2 ^ (prefixWord ++ tailWord_3537968).sum := by decide
  have hdescent : baseEnd_3537968 < baseStart_3537968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538012 : List Nat := [2, 2, 4, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_3538012 : Nat := 118140960795 + 3538012 * 2 ^ 59
def prefixEnd_3538012 : Nat := 4983230072969 + 3 ^ 40 * 3538012 * 2
def baseEnd_3538012 : Nat := 1816700717375116745478985

theorem tailTrace_3538012 : CollatzResearch.WordTrace tailWord_3538012 prefixEnd_3538012 1816700717375116745478985 := by
  unfold tailWord_3538012
  simp only [CollatzResearch.WordTrace]
  refine ⟨64520949429197121594180145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86027932572262828792240193 64520949429197121594180145)
  ·
    refine ⟨48390712071897841195635109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64520949429197121594180145 48390712071897841195635109)
    ·
      refine ⟨9073258513480845224181583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48390712071897841195635109 9073258513480845224181583)
      ·
        refine ⟨13609887770221267836272375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9073258513480845224181583 13609887770221267836272375)
        ·
          refine ⟨20414831655331901754408563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13609887770221267836272375 20414831655331901754408563)
          ·
            refine ⟨30622247482997852631612845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20414831655331901754408563 30622247482997852631612845)
            ·
              refine ⟨11483342806124194736854817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30622247482997852631612845 11483342806124194736854817)
              ·
                refine ⟨8612507104593146052641113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11483342806124194736854817 8612507104593146052641113)
                ·
                  refine ⟨6459380328444859539480835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8612507104593146052641113 6459380328444859539480835)
                  ·
                    refine ⟨9689070492667289309221253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6459380328444859539480835 9689070492667289309221253)
                    ·
                      refine ⟨1816700717375116745478985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9689070492667289309221253 1816700717375116745478985)
                      ·
                        rfl

theorem cell23_3538012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_3538012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538012 prefixEnd_3538012 := by exact prefixLift 3538012
  have htrace : WordTrace (prefixWord ++ tailWord_3538012) baseStart_3538012 baseEnd_3538012 := by
    simpa [prefixWord, tailWord_3538012, baseEnd_3538012] using wordTrace_append hprefix tailTrace_3538012
  have hstable : (prefixWord ++ tailWord_3538012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538012).length < 2 ^ (prefixWord ++ tailWord_3538012).sum := by decide
  have hdescent : baseEnd_3538012 < baseStart_3538012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538049 : List Nat := [1, 2, 4, 2, 2, 2, 2, 1, 2, 2, 3]
def baseStart_3538049 : Nat := 118140960795 + 3538049 * 2 ^ 59
def prefixEnd_3538049 : Nat := 4983230072969 + 3 ^ 40 * 3538049 * 2
def baseEnd_3538049 : Nat := 1816719716159333100716315

theorem tailTrace_3538049 : CollatzResearch.WordTrace tailWord_3538049 prefixEnd_3538049 1816719716159333100716315 := by
  unfold tailWord_3538049
  simp only [CollatzResearch.WordTrace]
  refine ⟨129043248359260198507457201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86028832239506799004971467 129043248359260198507457201)
  ·
    refine ⟨96782436269445148880592901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129043248359260198507457201 96782436269445148880592901)
    ·
      refine ⟨18146706800520965415111169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96782436269445148880592901 18146706800520965415111169)
      ·
        refine ⟨13610030100390724061333377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18146706800520965415111169 13610030100390724061333377)
        ·
          refine ⟨10207522575293043046000033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13610030100390724061333377 10207522575293043046000033)
          ·
            refine ⟨7655641931469782284500025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10207522575293043046000033 7655641931469782284500025)
            ·
              refine ⟨5741731448602336713375019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7655641931469782284500025 5741731448602336713375019)
              ·
                refine ⟨8612597172903505070062529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5741731448602336713375019 8612597172903505070062529)
                ·
                  refine ⟨6459447879677628802546897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8612597172903505070062529 6459447879677628802546897)
                  ·
                    refine ⟨4844585909758221601910173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6459447879677628802546897 4844585909758221601910173)
                    ·
                      refine ⟨1816719716159333100716315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4844585909758221601910173 1816719716159333100716315)
                      ·
                        rfl

theorem cell23_3538049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_3538049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538049 prefixEnd_3538049 := by exact prefixLift 3538049
  have htrace : WordTrace (prefixWord ++ tailWord_3538049) baseStart_3538049 baseEnd_3538049 := by
    simpa [prefixWord, tailWord_3538049, baseEnd_3538049] using wordTrace_append hprefix tailTrace_3538049
  have hstable : (prefixWord ++ tailWord_3538049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538049).length < 2 ^ (prefixWord ++ tailWord_3538049).sum := by decide
  have hdescent : baseEnd_3538049 < baseStart_3538049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538095 : List Nat := [1, 1, 2, 1, 2, 3, 3, 3, 1, 6]
def baseStart_3538095 : Nat := 118140960795 + 3538095 * 2 ^ 59
def prefixEnd_3538095 : Nat := 4983230072969 + 3 ^ 40 * 3538095 * 2
def baseEnd_3538095 : Nat := 605581112089813306913701

theorem tailTrace_3538095 : CollatzResearch.WordTrace tailWord_3538095 prefixEnd_3538095 605581112089813306913701 := by
  unfold tailWord_3538095
  simp only [CollatzResearch.WordTrace]
  refine ⟨129044926117093548363631739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86029950744729032242421159 129044926117093548363631739)
  ·
    refine ⟨193567389175640322545447609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129044926117093548363631739 193567389175640322545447609)
    ·
      refine ⟨145175541881730241909085707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193567389175640322545447609 145175541881730241909085707)
      ·
        refine ⟨217763312822595362863628561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145175541881730241909085707 217763312822595362863628561)
        ·
          refine ⟨163322484616946522147721421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217763312822595362863628561 163322484616946522147721421)
          ·
            refine ⟨61245931731354945805395533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163322484616946522147721421 61245931731354945805395533)
            ·
              refine ⟨22967224399258104677023325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61245931731354945805395533 22967224399258104677023325)
              ·
                refine ⟨8612709149721789253883747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22967224399258104677023325 8612709149721789253883747)
                ·
                  refine ⟨12919063724582683880825621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8612709149721789253883747 12919063724582683880825621)
                  ·
                    refine ⟨605581112089813306913701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12919063724582683880825621 605581112089813306913701)
                    ·
                      rfl

theorem cell23_3538095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 6].length) (baseStart_3538095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538095 prefixEnd_3538095 := by exact prefixLift 3538095
  have htrace : WordTrace (prefixWord ++ tailWord_3538095) baseStart_3538095 baseEnd_3538095 := by
    simpa [prefixWord, tailWord_3538095, baseEnd_3538095] using wordTrace_append hprefix tailTrace_3538095
  have hstable : (prefixWord ++ tailWord_3538095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538095).length < 2 ^ (prefixWord ++ tailWord_3538095).sum := by decide
  have hdescent : baseEnd_3538095 < baseStart_3538095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538113 : List Nat := [1, 2, 6, 1, 1, 1, 1, 5, 1, 1, 3]
def baseStart_3538113 : Nat := 118140960795 + 3538113 * 2 ^ 59
def prefixEnd_3538113 : Nat := 4983230072969 + 3 ^ 40 * 3538113 * 2
def baseEnd_3538113 : Nat := 1816752578921220850316021

theorem tailTrace_3538113 : CollatzResearch.WordTrace tailWord_3538113 prefixEnd_3538113 1816752578921220850316021 := by
  unfold tailWord_3538113
  simp only [CollatzResearch.WordTrace]
  refine ⟨129045582631028337437786993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86030388420685558291857995 129045582631028337437786993)
  ·
    refine ⟨96784186973271253078340245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129045582631028337437786993 96784186973271253078340245)
    ·
      refine ⟨4536758764372089988047199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 96784186973271253078340245 4536758764372089988047199)
      ·
        refine ⟨6805138146558134982070799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4536758764372089988047199 6805138146558134982070799)
        ·
          refine ⟨10207707219837202473106199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6805138146558134982070799 10207707219837202473106199)
          ·
            refine ⟨15311560829755803709659299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10207707219837202473106199 15311560829755803709659299)
            ·
              refine ⟨22967341244633705564488949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15311560829755803709659299 22967341244633705564488949)
              ·
                refine ⟨2153188241684409896670839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22967341244633705564488949 2153188241684409896670839)
                ·
                  refine ⟨3229782362526614845006259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2153188241684409896670839 3229782362526614845006259)
                  ·
                    refine ⟨4844673543789922267509389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3229782362526614845006259 4844673543789922267509389)
                    ·
                      refine ⟨1816752578921220850316021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4844673543789922267509389 1816752578921220850316021)
                      ·
                        rfl

theorem cell23_3538113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_3538113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538113 prefixEnd_3538113 := by exact prefixLift 3538113
  have htrace : WordTrace (prefixWord ++ tailWord_3538113) baseStart_3538113 baseEnd_3538113 := by
    simpa [prefixWord, tailWord_3538113, baseEnd_3538113] using wordTrace_append hprefix tailTrace_3538113
  have hstable : (prefixWord ++ tailWord_3538113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538113).length < 2 ^ (prefixWord ++ tailWord_3538113).sum := by decide
  have hdescent : baseEnd_3538113 < baseStart_3538113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538115 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 4]
def baseStart_3538115 : Nat := 118140960795 + 3538115 * 2 ^ 59
def prefixEnd_3538115 : Nat := 4983230072969 + 3 ^ 40 * 3538115 * 2
def baseEnd_3538115 : Nat := 1816753605882529842491011

theorem tailTrace_3538115 : CollatzResearch.WordTrace tailWord_3538115 prefixEnd_3538115 1816753605882529842491011 := by
  unfold tailWord_3538115
  simp only [CollatzResearch.WordTrace]
  refine ⟨129045655577021091779359799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86030437051347394519573199 129045655577021091779359799)
  ·
    refine ⟨193568483365531637669039699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129045655577021091779359799 193568483365531637669039699)
    ·
      refine ⟨290352725048297456503559549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193568483365531637669039699 290352725048297456503559549)
      ·
        refine ⟨108882271893111546188834831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290352725048297456503559549 108882271893111546188834831)
        ·
          refine ⟨163323407839667319283252247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108882271893111546188834831 163323407839667319283252247)
          ·
            refine ⟨244985111759500978924878371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163323407839667319283252247 244985111759500978924878371)
            ·
              refine ⟨367477667639251468387317557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244985111759500978924878371 367477667639251468387317557)
              ·
                refine ⟨34451031341179825161311021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 367477667639251468387317557 34451031341179825161311021)
                ·
                  refine ⟨12919136752942434435491633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34451031341179825161311021 12919136752942434435491633)
                  ·
                    refine ⟨9689352564706825826618725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12919136752942434435491633 9689352564706825826618725)
                    ·
                      refine ⟨1816753605882529842491011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9689352564706825826618725 1816753605882529842491011)
                      ·
                        rfl

theorem cell23_3538115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_3538115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538115 prefixEnd_3538115 := by exact prefixLift 3538115
  have htrace : WordTrace (prefixWord ++ tailWord_3538115) baseStart_3538115 baseEnd_3538115 := by
    simpa [prefixWord, tailWord_3538115, baseEnd_3538115] using wordTrace_append hprefix tailTrace_3538115
  have hstable : (prefixWord ++ tailWord_3538115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538115).length < 2 ^ (prefixWord ++ tailWord_3538115).sum := by decide
  have hdescent : baseEnd_3538115 < baseStart_3538115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538159 : List Nat := [1, 1, 2, 1, 7, 2, 2, 7]
def baseStart_3538159 : Nat := 118140960795 + 3538159 * 2 ^ 59
def prefixEnd_3538159 : Nat := 4983230072969 + 3 ^ 40 * 3538159 * 2
def baseEnd_3538159 : Nat := 67288007371530654457067

theorem tailTrace_3538159 : CollatzResearch.WordTrace tailWord_3538159 prefixEnd_3538159 67288007371530654457067 := by
  unfold tailWord_3538159
  simp only [CollatzResearch.WordTrace]
  refine ⟨129047260388861687293961531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86031506925907791529307687 129047260388861687293961531)
  ·
    refine ⟨193570890583292530940942297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129047260388861687293961531 193570890583292530940942297)
    ·
      refine ⟨145178167937469398205706723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193570890583292530940942297 145178167937469398205706723)
      ·
        refine ⟨217767251906204097308560085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145178167937469398205706723 217767251906204097308560085)
        ·
          refine ⟨5103919966551658530669377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 217767251906204097308560085 5103919966551658530669377)
          ·
            refine ⟨3827939974913743898002033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5103919966551658530669377 3827939974913743898002033)
            ·
              refine ⟨2870954981185307923501525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3827939974913743898002033 2870954981185307923501525)
              ·
                refine ⟨67288007371530654457067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2870954981185307923501525 67288007371530654457067)
                ·
                  rfl

theorem cell23_3538159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 7].length) (baseStart_3538159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538159 prefixEnd_3538159 := by exact prefixLift 3538159
  have htrace : WordTrace (prefixWord ++ tailWord_3538159) baseStart_3538159 baseEnd_3538159 := by
    simpa [prefixWord, tailWord_3538159, baseEnd_3538159] using wordTrace_append hprefix tailTrace_3538159
  have hstable : (prefixWord ++ tailWord_3538159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538159).length < 2 ^ (prefixWord ++ tailWord_3538159).sum := by decide
  have hdescent : baseEnd_3538159 < baseStart_3538159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538164 : List Nat := [2, 6, 1, 2, 1, 2, 1, 3, 1, 1, 3]
def baseStart_3538164 : Nat := 118140960795 + 3538164 * 2 ^ 59
def prefixEnd_3538164 : Nat := 4983230072969 + 3 ^ 40 * 3538164 * 2
def baseEnd_3538164 : Nat := 1816778766434600150778287

theorem tailTrace_3538164 : CollatzResearch.WordTrace tailWord_3538164 prefixEnd_3538164 1816778766434600150778287 := by
  unfold tailWord_3538164
  simp only [CollatzResearch.WordTrace]
  refine ⟨64523721376921786573946773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86031628502562382098595697 64523721376921786573946773)
  ·
    refine ⟨3024549439543208745653755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 64523721376921786573946773 3024549439543208745653755)
    ·
      refine ⟨4536824159314813118480633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3024549439543208745653755 4536824159314813118480633)
      ·
        refine ⟨3402618119486109838860475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4536824159314813118480633 3402618119486109838860475)
        ·
          refine ⟨5103927179229164758290713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3402618119486109838860475 5103927179229164758290713)
          ·
            refine ⟨3827945384421873568718035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5103927179229164758290713 3827945384421873568718035)
            ·
              refine ⟨5741918076632810353077053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3827945384421873568718035 5741918076632810353077053)
              ·
                refine ⟨2153219278737303882403895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5741918076632810353077053 2153219278737303882403895)
                ·
                  refine ⟨3229828918105955823605843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2153219278737303882403895 3229828918105955823605843)
                  ·
                    refine ⟨4844743377158933735408765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3229828918105955823605843 4844743377158933735408765)
                    ·
                      refine ⟨1816778766434600150778287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4844743377158933735408765 1816778766434600150778287)
                      ·
                        rfl

theorem cell23_3538164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_3538164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538164 prefixEnd_3538164 := by exact prefixLift 3538164
  have htrace : WordTrace (prefixWord ++ tailWord_3538164) baseStart_3538164 baseEnd_3538164 := by
    simpa [prefixWord, tailWord_3538164, baseEnd_3538164] using wordTrace_append hprefix tailTrace_3538164
  have hstable : (prefixWord ++ tailWord_3538164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538164).length < 2 ^ (prefixWord ++ tailWord_3538164).sum := by decide
  have hdescent : baseEnd_3538164 < baseStart_3538164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538209 : List Nat := [1, 2, 3, 2, 1, 1, 1, 5, 1, 4, 2]
def baseStart_3538209 : Nat := 118140960795 + 3538209 * 2 ^ 59
def prefixEnd_3538209 : Nat := 4983230072969 + 3 ^ 40 * 3538209 * 2
def baseEnd_3538209 : Nat := 1816801873064052474715579

theorem tailTrace_3538209 : CollatzResearch.WordTrace tailWord_3538209 prefixEnd_3538209 1816801873064052474715579 := by
  unfold tailWord_3538209
  simp only [CollatzResearch.WordTrace]
  refine ⟨129049084038680545833281681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86032722692453697222187787 129049084038680545833281681)
  ·
    refine ⟨96786813029010409374961261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129049084038680545833281681 96786813029010409374961261)
    ·
      refine ⟨36295054885878903515610473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96786813029010409374961261 36295054885878903515610473)
      ·
        refine ⟨27221291164409177636707855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36295054885878903515610473 27221291164409177636707855)
        ·
          refine ⟨40831936746613766455061783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27221291164409177636707855 40831936746613766455061783)
          ·
            refine ⟨61247905119920649682592675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40831936746613766455061783 61247905119920649682592675)
            ·
              refine ⟨91871857679880974523889013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61247905119920649682592675 91871857679880974523889013)
              ·
                refine ⟨8612986657488841361614595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91871857679880974523889013 8612986657488841361614595)
                ·
                  refine ⟨12919479986233262042421893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8612986657488841361614595 12919479986233262042421893)
                  ·
                    refine ⟨2422402497418736632954105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12919479986233262042421893 2422402497418736632954105)
                    ·
                      refine ⟨1816801873064052474715579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2422402497418736632954105 1816801873064052474715579)
                      ·
                        rfl

theorem cell23_3538209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_3538209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538209 prefixEnd_3538209 := by exact prefixLift 3538209
  have htrace : WordTrace (prefixWord ++ tailWord_3538209) baseStart_3538209 baseEnd_3538209 := by
    simpa [prefixWord, tailWord_3538209, baseEnd_3538209] using wordTrace_append hprefix tailTrace_3538209
  have hstable : (prefixWord ++ tailWord_3538209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538209).length < 2 ^ (prefixWord ++ tailWord_3538209).sum := by decide
  have hdescent : baseEnd_3538209 < baseStart_3538209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538212 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 4, 1, 5]
def baseStart_3538212 : Nat := 118140960795 + 3538212 * 2 ^ 59
def prefixEnd_3538212 : Nat := 4983230072969 + 3 ^ 40 * 3538212 * 2
def baseEnd_3538212 : Nat := 1816803413506015962978065

theorem tailTrace_3538212 : CollatzResearch.WordTrace tailWord_3538212 prefixEnd_3538212 1816803413506015962978065 := by
  unfold tailWord_3538212
  simp only [CollatzResearch.WordTrace]
  refine ⟨64524596728834838672820445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86032795638446451563760593 64524596728834838672820445)
  ·
    refine ⟨24196723773313064502307667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64524596728834838672820445 24196723773313064502307667)
    ·
      refine ⟨36295085659969596753461501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24196723773313064502307667 36295085659969596753461501)
      ·
        refine ⟨13610657122488598782548063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36295085659969596753461501 13610657122488598782548063)
        ·
          refine ⟨20415985683732898173822095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13610657122488598782548063 20415985683732898173822095)
          ·
            refine ⟨30623978525599347260733143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20415985683732898173822095 30623978525599347260733143)
            ·
              refine ⟨45935967788399020891099715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30623978525599347260733143 45935967788399020891099715)
              ·
                refine ⟨68903951682598531336649573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45935967788399020891099715 68903951682598531336649573)
                ·
                  refine ⟨12919490940487224625621795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68903951682598531336649573 12919490940487224625621795)
                  ·
                    refine ⟨19379236410730836938432693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12919490940487224625621795 19379236410730836938432693)
                    ·
                      refine ⟨1816803413506015962978065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19379236410730836938432693 1816803413506015962978065)
                      ·
                        rfl

theorem cell23_3538212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_3538212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538212 prefixEnd_3538212 := by exact prefixLift 3538212
  have htrace : WordTrace (prefixWord ++ tailWord_3538212) baseStart_3538212 baseEnd_3538212 := by
    simpa [prefixWord, tailWord_3538212, baseEnd_3538212] using wordTrace_append hprefix tailTrace_3538212
  have hstable : (prefixWord ++ tailWord_3538212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538212).length < 2 ^ (prefixWord ++ tailWord_3538212).sum := by decide
  have hdescent : baseEnd_3538212 < baseStart_3538212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538213 : List Nat := [1, 3, 1, 2, 4, 3, 1, 2, 1, 3, 2]
def baseStart_3538213 : Nat := 118140960795 + 3538213 * 2 ^ 59
def prefixEnd_3538213 : Nat := 4983230072969 + 3 ^ 40 * 3538213 * 2
def baseEnd_3538213 : Nat := 1816803926986670459065561

theorem tailTrace_3538213 : CollatzResearch.WordTrace tailWord_3538213 prefixEnd_3538213 1816803926986670459065561 := by
  unfold tailWord_3538213
  simp only [CollatzResearch.WordTrace]
  refine ⟨129049229930666054516427293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86032819953777369677618195 129049229930666054516427293)
  ·
    refine ⟨48393461223999770443660235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129049229930666054516427293 48393461223999770443660235)
    ·
      refine ⟨72590191835999655665490353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48393461223999770443660235 72590191835999655665490353)
      ·
        refine ⟨54442643876999741749117765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72590191835999655665490353 54442643876999741749117765)
        ·
          refine ⟨10207995726937451577959581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54442643876999741749117765 10207995726937451577959581)
          ·
            refine ⟨3827998397601544341734843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10207995726937451577959581 3827998397601544341734843)
            ·
              refine ⟨5741997596402316512602265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3827998397601544341734843 5741997596402316512602265)
              ·
                refine ⟨4306498197301737384451699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5741997596402316512602265 4306498197301737384451699)
                ·
                  refine ⟨6459747295952606076677549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4306498197301737384451699 6459747295952606076677549)
                  ·
                    refine ⟨2422405235982227278754081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6459747295952606076677549 2422405235982227278754081)
                    ·
                      refine ⟨1816803926986670459065561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2422405235982227278754081 1816803926986670459065561)
                      ·
                        rfl

theorem cell23_3538213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 3, 2].length) (baseStart_3538213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538213 prefixEnd_3538213 := by exact prefixLift 3538213
  have htrace : WordTrace (prefixWord ++ tailWord_3538213) baseStart_3538213 baseEnd_3538213 := by
    simpa [prefixWord, tailWord_3538213, baseEnd_3538213] using wordTrace_append hprefix tailTrace_3538213
  have hstable : (prefixWord ++ tailWord_3538213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538213).length < 2 ^ (prefixWord ++ tailWord_3538213).sum := by decide
  have hdescent : baseEnd_3538213 < baseStart_3538213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538226 : List Nat := [3, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2]
def baseStart_3538226 : Nat := 118140960795 + 3538226 * 2 ^ 59
def prefixEnd_3538226 : Nat := 4983230072969 + 3 ^ 40 * 3538226 * 2
def baseEnd_3538226 : Nat := 1816810602235178908203001

theorem tailTrace_3538226 : CollatzResearch.WordTrace tailWord_3538226 prefixEnd_3538226 1816810602235178908203001 := by
  unfold tailWord_3538226
  simp only [CollatzResearch.WordTrace]
  refine ⟨32262426019904739434162633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86033136053079305157767021 32262426019904739434162633)
  ·
    refine ⟨24196819514928554575621975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32262426019904739434162633 24196819514928554575621975)
    ·
      refine ⟨36295229272392831863432963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24196819514928554575621975 36295229272392831863432963)
      ·
        refine ⟨54442843908589247795149445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36295229272392831863432963 54442843908589247795149445)
        ·
          refine ⟨10208033232860483961590521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54442843908589247795149445 10208033232860483961590521)
          ·
            refine ⟨7656024924645362971192891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10208033232860483961590521 7656024924645362971192891)
            ·
              refine ⟨11484037386968044456789337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7656024924645362971192891 11484037386968044456789337)
              ·
                refine ⟨8613028040226033342592003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11484037386968044456789337 8613028040226033342592003)
                ·
                  refine ⟨12919542060339050013888005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8613028040226033342592003 12919542060339050013888005)
                  ·
                    refine ⟨2422414136313571877604001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12919542060339050013888005 2422414136313571877604001)
                    ·
                      refine ⟨1816810602235178908203001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2422414136313571877604001 1816810602235178908203001)
                      ·
                        rfl

theorem cell23_3538226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2].length) (baseStart_3538226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538226 prefixEnd_3538226 := by exact prefixLift 3538226
  have htrace : WordTrace (prefixWord ++ tailWord_3538226) baseStart_3538226 baseEnd_3538226 := by
    simpa [prefixWord, tailWord_3538226, baseEnd_3538226] using wordTrace_append hprefix tailTrace_3538226
  have hstable : (prefixWord ++ tailWord_3538226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538226).length < 2 ^ (prefixWord ++ tailWord_3538226).sum := by decide
  have hdescent : baseEnd_3538226 < baseStart_3538226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538235 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 8]
def baseStart_3538235 : Nat := 118140960795 + 3538235 * 2 ^ 59
def prefixEnd_3538235 : Nat := 4983230072969 + 3 ^ 40 * 3538235 * 2
def baseEnd_3538235 : Nat := 1816815223561069372990459

theorem tailTrace_3538235 : CollatzResearch.WordTrace tailWord_3538235 prefixEnd_3538235 1816815223561069372990459 := by
  unfold tailWord_3538235
  simp only [CollatzResearch.WordTrace]
  refine ⟨129050032336586352273728159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86033354891057568182485439 129050032336586352273728159)
  ·
    refine ⟨193575048504879528410592239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129050032336586352273728159 193575048504879528410592239)
    ·
      refine ⟨290362572757319292615888359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193575048504879528410592239 290362572757319292615888359)
      ·
        refine ⟨435543859135978938923832539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290362572757319292615888359 435543859135978938923832539)
        ·
          refine ⟨653315788703968408385748809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435543859135978938923832539 653315788703968408385748809)
          ·
            refine ⟨489986841527976306289311607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 653315788703968408385748809 489986841527976306289311607)
            ·
              refine ⟨734980262291964459433967411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489986841527976306289311607 734980262291964459433967411)
              ·
                refine ⟨1102470393437946689150951117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 734980262291964459433967411 1102470393437946689150951117)
                ·
                  refine ⟨413426397539230008431606669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1102470393437946689150951117 413426397539230008431606669)
                  ·
                    refine ⟨155034899077211253161852501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 413426397539230008431606669 155034899077211253161852501)
                    ·
                      refine ⟨1816815223561069372990459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 155034899077211253161852501 1816815223561069372990459)
                      ·
                        rfl

theorem cell23_3538235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 8].length) (baseStart_3538235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538235 prefixEnd_3538235 := by exact prefixLift 3538235
  have htrace : WordTrace (prefixWord ++ tailWord_3538235) baseStart_3538235 baseEnd_3538235 := by
    simpa [prefixWord, tailWord_3538235, baseEnd_3538235] using wordTrace_append hprefix tailTrace_3538235
  have hstable : (prefixWord ++ tailWord_3538235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538235).length < 2 ^ (prefixWord ++ tailWord_3538235).sum := by decide
  have hdescent : baseEnd_3538235 < baseStart_3538235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538279 : List Nat := [1, 1, 5, 1, 4, 1, 1, 1, 1, 7]
def baseStart_3538279 : Nat := 118140960795 + 3538279 * 2 ^ 59
def prefixEnd_3538279 : Nat := 4983230072969 + 3 ^ 40 * 3538279 * 2
def baseEnd_3538279 : Nat := 605612605569955733613419

theorem tailTrace_3538279 : CollatzResearch.WordTrace tailWord_3538279 prefixEnd_3538279 605612605569955733613419 := by
  unfold tailWord_3538279
  simp only [CollatzResearch.WordTrace]
  refine ⟨129051637148426947788329891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86034424765617965192219927 129051637148426947788329891)
  ·
    refine ⟨193577455722640421682494837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129051637148426947788329891 193577455722640421682494837)
    ·
      refine ⟨18147886473997539532733891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 193577455722640421682494837 18147886473997539532733891)
      ·
        refine ⟨27221829710996309299100837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18147886473997539532733891 27221829710996309299100837)
        ·
          refine ⟨5104093070811807993581407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27221829710996309299100837 5104093070811807993581407)
          ·
            refine ⟨7656139606217711990372111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5104093070811807993581407 7656139606217711990372111)
            ·
              refine ⟨11484209409326567985558167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7656139606217711990372111 11484209409326567985558167)
              ·
                refine ⟨17226314113989851978337251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11484209409326567985558167 17226314113989851978337251)
                ·
                  refine ⟨25839471170984777967505877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17226314113989851978337251 25839471170984777967505877)
                  ·
                    refine ⟨605612605569955733613419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25839471170984777967505877 605612605569955733613419)
                    ·
                      rfl

theorem cell23_3538279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_3538279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538279 prefixEnd_3538279 := by exact prefixLift 3538279
  have htrace : WordTrace (prefixWord ++ tailWord_3538279) baseStart_3538279 baseEnd_3538279 := by
    simpa [prefixWord, tailWord_3538279, baseEnd_3538279] using wordTrace_append hprefix tailTrace_3538279
  have hstable : (prefixWord ++ tailWord_3538279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538279).length < 2 ^ (prefixWord ++ tailWord_3538279).sum := by decide
  have hdescent : baseEnd_3538279 < baseStart_3538279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538299 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 4, 4, 2]
def baseStart_3538299 : Nat := 118140960795 + 3538299 * 2 ^ 59
def prefixEnd_3538299 : Nat := 4983230072969 + 3 ^ 40 * 3538299 * 2
def baseEnd_3538299 : Nat := 1816848086322957122590165

theorem tailTrace_3538299 : CollatzResearch.WordTrace tailWord_3538299 prefixEnd_3538299 1816848086322957122590165 := by
  unfold tailWord_3538299
  simp only [CollatzResearch.WordTrace]
  refine ⟨129052366608354491204057951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86034911072236327469371967 129052366608354491204057951)
  ·
    refine ⟨193578549912531736806086927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129052366608354491204057951 193578549912531736806086927)
    ·
      refine ⟨290367824868797605209130391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193578549912531736806086927 290367824868797605209130391)
      ·
        refine ⟨435551737303196407813695587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290367824868797605209130391 435551737303196407813695587)
        ·
          refine ⟨653327605954794611720543381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435551737303196407813695587 653327605954794611720543381)
          ·
            refine ⟨30624731529130997424400471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 653327605954794611720543381 30624731529130997424400471)
            ·
              refine ⟨45937097293696496136600707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30624731529130997424400471 45937097293696496136600707)
              ·
                refine ⟨68905645940544744204901061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45937097293696496136600707 68905645940544744204901061)
                ·
                  refine ⟨12919808613852139538418949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68905645940544744204901061 12919808613852139538418949)
                  ·
                    refine ⟨2422464115097276163453553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12919808613852139538418949 2422464115097276163453553)
                    ·
                      refine ⟨1816848086322957122590165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2422464115097276163453553 1816848086322957122590165)
                      ·
                        rfl

theorem cell23_3538299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 4, 2].length) (baseStart_3538299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538299 prefixEnd_3538299 := by exact prefixLift 3538299
  have htrace : WordTrace (prefixWord ++ tailWord_3538299) baseStart_3538299 baseEnd_3538299 := by
    simpa [prefixWord, tailWord_3538299, baseEnd_3538299] using wordTrace_append hprefix tailTrace_3538299
  have hstable : (prefixWord ++ tailWord_3538299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538299).length < 2 ^ (prefixWord ++ tailWord_3538299).sum := by decide
  have hdescent : baseEnd_3538299 < baseStart_3538299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538309 : List Nat := [1, 3, 1, 1, 3, 1, 3, 3, 3, 4]
def baseStart_3538309 : Nat := 118140960795 + 3538309 * 2 ^ 59
def prefixEnd_3538309 : Nat := 4983230072969 + 3 ^ 40 * 3538309 * 2
def baseEnd_3538309 : Nat := 605617740376500694488373

theorem tailTrace_3538309 : CollatzResearch.WordTrace tailWord_3538309 prefixEnd_3538309 605617740376500694488373 := by
  unfold tailWord_3538309
  simp only [CollatzResearch.WordTrace]
  refine ⟨129052731338318262911921981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86035154225545508607947987 129052731338318262911921981)
  ·
    refine ⟨48394774251869348591970743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129052731338318262911921981 48394774251869348591970743)
    ·
      refine ⟨72592161377804022887956115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48394774251869348591970743 72592161377804022887956115)
      ·
        refine ⟨108888242066706034331934173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72592161377804022887956115 108888242066706034331934173)
        ·
          refine ⟨40833090775014762874475315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108888242066706034331934173 40833090775014762874475315)
          ·
            refine ⟨61249636162522144311712973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40833090775014762874475315 61249636162522144311712973)
            ·
              refine ⟨22968613560945804116892365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61249636162522144311712973 22968613560945804116892365)
              ·
                refine ⟨8613230085354676543834637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22968613560945804116892365 8613230085354676543834637)
                ·
                  refine ⟨3229961282008003703937989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8613230085354676543834637 3229961282008003703937989)
                  ·
                    refine ⟨605617740376500694488373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3229961282008003703937989 605617740376500694488373)
                    ·
                      rfl

theorem cell23_3538309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 3, 4].length) (baseStart_3538309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538309 prefixEnd_3538309 := by exact prefixLift 3538309
  have htrace : WordTrace (prefixWord ++ tailWord_3538309) baseStart_3538309 baseEnd_3538309 := by
    simpa [prefixWord, tailWord_3538309, baseEnd_3538309] using wordTrace_append hprefix tailTrace_3538309
  have hstable : (prefixWord ++ tailWord_3538309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538309).length < 2 ^ (prefixWord ++ tailWord_3538309).sum := by decide
  have hdescent : baseEnd_3538309 < baseStart_3538309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538362 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 4, 1, 7]
def baseStart_3538362 : Nat := 118140960795 + 3538362 * 2 ^ 59
def prefixEnd_3538362 : Nat := 4983230072969 + 3 ^ 40 * 3538362 * 2
def baseEnd_3538362 : Nat := 1816880435604190376102375

theorem tailTrace_3538362 : CollatzResearch.WordTrace tailWord_3538362 prefixEnd_3538362 1816880435604190376102375 := by
  unfold tailWord_3538362
  simp only [CollatzResearch.WordTrace]
  refine ⟨32263666101781563240900335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86036442938084168642400893 32263666101781563240900335)
  ·
    refine ⟨48395499152672344861350503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32263666101781563240900335 48395499152672344861350503)
    ·
      refine ⟨72593248729008517292025755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48395499152672344861350503 72593248729008517292025755)
      ·
        refine ⟨108889873093512775938038633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72593248729008517292025755 108889873093512775938038633)
        ·
          refine ⟨81667404820134581953528975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108889873093512775938038633 81667404820134581953528975)
          ·
            refine ⟨122501107230201872930293463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81667404820134581953528975 122501107230201872930293463)
            ·
              refine ⟨183751660845302809395440195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122501107230201872930293463 183751660845302809395440195)
              ·
                refine ⟨275627491267954214093160293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183751660845302809395440195 275627491267954214093160293)
                ·
                  refine ⟨51680154612741415142467555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 275627491267954214093160293 51680154612741415142467555)
                  ·
                    refine ⟨77520231919112122713701333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51680154612741415142467555 77520231919112122713701333)
                    ·
                      refine ⟨1816880435604190376102375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 77520231919112122713701333 1816880435604190376102375)
                      ·
                        rfl

theorem cell23_3538362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_3538362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538362 prefixEnd_3538362 := by exact prefixLift 3538362
  have htrace : WordTrace (prefixWord ++ tailWord_3538362) baseStart_3538362 baseEnd_3538362 := by
    simpa [prefixWord, tailWord_3538362, baseEnd_3538362] using wordTrace_append hprefix tailTrace_3538362
  have hstable : (prefixWord ++ tailWord_3538362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538362).length < 2 ^ (prefixWord ++ tailWord_3538362).sum := by decide
  have hdescent : baseEnd_3538362 < baseStart_3538362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538376 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 4, 3, 2]
def baseStart_3538376 : Nat := 118140960795 + 3538376 * 2 ^ 59
def prefixEnd_3538376 : Nat := 4983230072969 + 3 ^ 40 * 3538376 * 2
def baseEnd_3538376 : Nat := 1816887624333353321327311

theorem tailTrace_3538376 : CollatzResearch.WordTrace tailWord_3538376 prefixEnd_3538376 1816887624333353321327311 := by
  unfold tailWord_3538376
  simp only [CollatzResearch.WordTrace]
  refine ⟨64527587514537766677305491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86036783352717022236407321 64527587514537766677305491)
  ·
    refine ⟨96791381271806650015958237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64527587514537766677305491 96791381271806650015958237)
    ·
      refine ⟨36296767976927493755984339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96791381271806650015958237 36296767976927493755984339)
      ·
        refine ⟨54445151965391240633976509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36296767976927493755984339 54445151965391240633976509)
        ·
          refine ⟨20416931987021715237741191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54445151965391240633976509 20416931987021715237741191)
          ·
            refine ⟨30625397980532572856611787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20416931987021715237741191 30625397980532572856611787)
            ·
              refine ⟨45938096970798859284917681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30625397980532572856611787 45938096970798859284917681)
              ·
                refine ⟨34453572728099144463688261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45938096970798859284917681 34453572728099144463688261)
                ·
                  refine ⟨6460044886518589586941549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34453572728099144463688261 6460044886518589586941549)
                  ·
                    refine ⟨2422516832444471095103081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6460044886518589586941549 2422516832444471095103081)
                    ·
                      refine ⟨1816887624333353321327311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2422516832444471095103081 1816887624333353321327311)
                      ·
                        rfl

theorem cell23_3538376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 4, 3, 2].length) (baseStart_3538376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538376 prefixEnd_3538376 := by exact prefixLift 3538376
  have htrace : WordTrace (prefixWord ++ tailWord_3538376) baseStart_3538376 baseEnd_3538376 := by
    simpa [prefixWord, tailWord_3538376, baseEnd_3538376] using wordTrace_append hprefix tailTrace_3538376
  have hstable : (prefixWord ++ tailWord_3538376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538376).length < 2 ^ (prefixWord ++ tailWord_3538376).sum := by decide
  have hdescent : baseEnd_3538376 < baseStart_3538376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538393 : List Nat := [1, 2, 1, 2, 4, 3, 2, 1, 2, 3, 2]
def baseStart_3538393 : Nat := 118140960795 + 3538393 * 2 ^ 59
def prefixEnd_3538393 : Nat := 4983230072969 + 3 ^ 40 * 3538393 * 2
def baseEnd_3538393 : Nat := 1816896353504479754814733

theorem tailTrace_3538393 : CollatzResearch.WordTrace tailWord_3538393 prefixEnd_3538393 1816896353504479754814733 := by
  unfold tailWord_3538393
  simp only [CollatzResearch.WordTrace]
  refine ⟨129055795070013945257979833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86037196713342630171986555 129055795070013945257979833)
  ·
    refine ⟨96791846302510458943484875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129055795070013945257979833 96791846302510458943484875)
    ·
      refine ⟨145187769453765688415227313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96791846302510458943484875 145187769453765688415227313)
      ·
        refine ⟨108890827090324266311420485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145187769453765688415227313 108890827090324266311420485)
        ·
          refine ⟨20417030079435799933391341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108890827090324266311420485 20417030079435799933391341)
          ·
            refine ⟨7656386279788424975021753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20417030079435799933391341 7656386279788424975021753)
            ·
              refine ⟨5742289709841318731266315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7656386279788424975021753 5742289709841318731266315)
              ·
                refine ⟨8613434564761978096899473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5742289709841318731266315 8613434564761978096899473)
                ·
                  refine ⟨6460075923571483572674605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8613434564761978096899473 6460075923571483572674605)
                  ·
                    refine ⟨2422528471339306339752977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6460075923571483572674605 2422528471339306339752977)
                    ·
                      refine ⟨1816896353504479754814733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2422528471339306339752977 1816896353504479754814733)
                      ·
                        rfl

theorem cell23_3538393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 3, 2].length) (baseStart_3538393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538393 prefixEnd_3538393 := by exact prefixLift 3538393
  have htrace : WordTrace (prefixWord ++ tailWord_3538393) baseStart_3538393 baseEnd_3538393 := by
    simpa [prefixWord, tailWord_3538393, baseEnd_3538393] using wordTrace_append hprefix tailTrace_3538393
  have hstable : (prefixWord ++ tailWord_3538393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538393).length < 2 ^ (prefixWord ++ tailWord_3538393).sum := by decide
  have hdescent : baseEnd_3538393 < baseStart_3538393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538399 : List Nat := [1, 1, 2, 3, 3, 1, 3, 2, 1, 6]
def baseStart_3538399 : Nat := 118140960795 + 3538399 * 2 ^ 59
def prefixEnd_3538399 : Nat := 4983230072969 + 3 ^ 40 * 3538399 * 2
def baseEnd_3538399 : Nat := 605633144796135577113235

theorem tailTrace_3538399 : CollatzResearch.WordTrace tailWord_3538399 prefixEnd_3538399 605633144796135577113235 := by
  unfold tailWord_3538399
  simp only [CollatzResearch.WordTrace]
  refine ⟨129056013907992208282698251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86037342605328138855132167 129056013907992208282698251)
  ·
    refine ⟨193584020861988312424047377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129056013907992208282698251 193584020861988312424047377)
    ·
      refine ⟨145188015646491234318035533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193584020861988312424047377 145188015646491234318035533)
      ·
        refine ⟨54445505867434212869263325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145188015646491234318035533 54445505867434212869263325)
        ·
          refine ⟨20417064700287829825973747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54445505867434212869263325 20417064700287829825973747)
          ·
            refine ⟨30625597050431744738960621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20417064700287829825973747 30625597050431744738960621)
            ·
              refine ⟨11484598893911904277110233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30625597050431744738960621 11484598893911904277110233)
              ·
                refine ⟨8613449170433928207832675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11484598893911904277110233 8613449170433928207832675)
                ·
                  refine ⟨12920173755650892311749013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8613449170433928207832675 12920173755650892311749013)
                  ·
                    refine ⟨605633144796135577113235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12920173755650892311749013 605633144796135577113235)
                    ·
                      rfl

theorem cell23_3538399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 6].length) (baseStart_3538399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538399 prefixEnd_3538399 := by exact prefixLift 3538399
  have htrace : WordTrace (prefixWord ++ tailWord_3538399) baseStart_3538399 baseEnd_3538399 := by
    simpa [prefixWord, tailWord_3538399, baseEnd_3538399] using wordTrace_append hprefix tailTrace_3538399
  have hstable : (prefixWord ++ tailWord_3538399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538399).length < 2 ^ (prefixWord ++ tailWord_3538399).sum := by decide
  have hdescent : baseEnd_3538399 < baseStart_3538399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538403 : List Nat := [1, 1, 1, 6, 2, 2, 3, 1, 1, 5]
def baseStart_3538403 : Nat := 118140960795 + 3538403 * 2 ^ 59
def prefixEnd_3538403 : Nat := 4983230072969 + 3 ^ 40 * 3538403 * 2
def baseEnd_3538403 : Nat := 605633829437008238563229

theorem tailTrace_3538403 : CollatzResearch.WordTrace tailWord_3538403 prefixEnd_3538403 605633829437008238563229 := by
  unfold tailWord_3538403
  simp only [CollatzResearch.WordTrace]
  refine ⟨129056159799977716965843863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86037439866651811310562575 129056159799977716965843863)
  ·
    refine ⟨193584239699966575448765795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129056159799977716965843863 193584239699966575448765795)
    ·
      refine ⟨290376359549949863173148693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193584239699966575448765795 290376359549949863173148693)
      ·
        refine ⟨13611391853903899836241345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 290376359549949863173148693 13611391853903899836241345)
        ·
          refine ⟨10208543890427924877181009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13611391853903899836241345 10208543890427924877181009)
          ·
            refine ⟨7656407917820943657885757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10208543890427924877181009 7656407917820943657885757)
            ·
              refine ⟨2871152969182853871707159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7656407917820943657885757 2871152969182853871707159)
              ·
                refine ⟨4306729453774280807560739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2871152969182853871707159 4306729453774280807560739)
                ·
                  refine ⟨6460094180661421211341109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4306729453774280807560739 6460094180661421211341109)
                  ·
                    refine ⟨605633829437008238563229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6460094180661421211341109 605633829437008238563229)
                    ·
                      rfl

theorem cell23_3538403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 1, 5].length) (baseStart_3538403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538403 prefixEnd_3538403 := by exact prefixLift 3538403
  have htrace : WordTrace (prefixWord ++ tailWord_3538403) baseStart_3538403 baseEnd_3538403 := by
    simpa [prefixWord, tailWord_3538403, baseEnd_3538403] using wordTrace_append hprefix tailTrace_3538403
  have hstable : (prefixWord ++ tailWord_3538403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538403).length < 2 ^ (prefixWord ++ tailWord_3538403).sum := by decide
  have hdescent : baseEnd_3538403 < baseStart_3538403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538416 : List Nat := [2, 1, 1, 1, 3, 4, 1, 4, 2, 4]
def baseStart_3538416 : Nat := 118140960795 + 3538416 * 2 ^ 59
def prefixEnd_3538416 : Nat := 4983230072969 + 3 ^ 40 * 3538416 * 2
def baseEnd_3538416 : Nat := 605636054519844388275709

theorem tailTrace_3538416 : CollatzResearch.WordTrace tailWord_3538416 prefixEnd_3538416 605636054519844388275709 := by
  unfold tailWord_3538416
  simp only [CollatzResearch.WordTrace]
  refine ⟨64528316974465310093033551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86037755965953746790711401 64528316974465310093033551)
  ·
    refine ⟨96792475461697965139550327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64528316974465310093033551 96792475461697965139550327)
    ·
      refine ⟨145188713192546947709325491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96792475461697965139550327 145188713192546947709325491)
      ·
        refine ⟨217783069788820421563988237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145188713192546947709325491 217783069788820421563988237)
        ·
          refine ⟨81668651170807658086495589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217783069788820421563988237 81668651170807658086495589)
          ·
            refine ⟨15312872094526435891217923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81668651170807658086495589 15312872094526435891217923)
            ·
              refine ⟨22969308141789653836826885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15312872094526435891217923 22969308141789653836826885)
              ·
                refine ⟨4306745276585560094405041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22969308141789653836826885 4306745276585560094405041)
                ·
                  refine ⟨3230058957439170070803781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4306745276585560094405041 3230058957439170070803781)
                  ·
                    refine ⟨605636054519844388275709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3230058957439170070803781 605636054519844388275709)
                    ·
                      rfl

theorem cell23_3538416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 2, 4].length) (baseStart_3538416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538416 prefixEnd_3538416 := by exact prefixLift 3538416
  have htrace : WordTrace (prefixWord ++ tailWord_3538416) baseStart_3538416 baseEnd_3538416 := by
    simpa [prefixWord, tailWord_3538416, baseEnd_3538416] using wordTrace_append hprefix tailTrace_3538416
  have hstable : (prefixWord ++ tailWord_3538416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538416).length < 2 ^ (prefixWord ++ tailWord_3538416).sum := by decide
  have hdescent : baseEnd_3538416 < baseStart_3538416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538417 : List Nat := [1, 2, 2, 2, 3, 4, 2, 2, 1, 1, 3]
def baseStart_3538417 : Nat := 118140960795 + 3538417 * 2 ^ 59
def prefixEnd_3538417 : Nat := 4983230072969 + 3 ^ 40 * 3538417 * 2
def baseEnd_3538417 : Nat := 1816908677040187660914623

theorem tailTrace_3538417 : CollatzResearch.WordTrace tailWord_3538417 prefixEnd_3538417 1816908677040187660914623 := by
  unfold tailWord_3538417
  simp only [CollatzResearch.WordTrace]
  refine ⟨129056670421926997356853505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86037780281284664904569003 129056670421926997356853505)
  ·
    refine ⟨96792502816445248017640129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129056670421926997356853505 96792502816445248017640129)
    ·
      refine ⟨72594377112333936013230097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96792502816445248017640129 72594377112333936013230097)
      ·
        refine ⟨54445782834250452009922573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72594377112333936013230097 54445782834250452009922573)
        ·
          refine ⟨20417168562843919503720965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54445782834250452009922573 20417168562843919503720965)
          ·
            refine ⟨3828219105533234906947681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20417168562843919503720965 3828219105533234906947681)
            ·
              refine ⟨2871164329149926180210761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3828219105533234906947681 2871164329149926180210761)
              ·
                refine ⟨2153373246862444635158071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2871164329149926180210761 2153373246862444635158071)
                ·
                  refine ⟨3230059870293666952737107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2153373246862444635158071 3230059870293666952737107)
                  ·
                    refine ⟨4845089805440500429105661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3230059870293666952737107 4845089805440500429105661)
                    ·
                      refine ⟨1816908677040187660914623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4845089805440500429105661 1816908677040187660914623)
                      ·
                        rfl

theorem cell23_3538417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 2, 1, 1, 3].length) (baseStart_3538417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538417 prefixEnd_3538417 := by exact prefixLift 3538417
  have htrace : WordTrace (prefixWord ++ tailWord_3538417) baseStart_3538417 baseEnd_3538417 := by
    simpa [prefixWord, tailWord_3538417, baseEnd_3538417] using wordTrace_append hprefix tailTrace_3538417
  have hstable : (prefixWord ++ tailWord_3538417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538417).length < 2 ^ (prefixWord ++ tailWord_3538417).sum := by decide
  have hdescent : baseEnd_3538417 < baseStart_3538417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538429 : List Nat := [1, 4, 1, 1, 1, 4, 3, 8]
def baseStart_3538429 : Nat := 118140960795 + 3538429 * 2 ^ 59
def prefixEnd_3538429 : Nat := 4983230072969 + 3 ^ 40 * 3538429 * 2
def baseEnd_3538429 : Nat := 67293142178075615332021

theorem tailTrace_3538429 : CollatzResearch.WordTrace tailWord_3538429 prefixEnd_3538429 67293142178075615332021 := by
  unfold tailWord_3538429
  simp only [CollatzResearch.WordTrace]
  refine ⟨129057108097883523406290341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86038072065255682270860227 129057108097883523406290341)
  ·
    refine ⟨24198207768353160638679439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129057108097883523406290341 24198207768353160638679439)
    ·
      refine ⟨36297311652529740958019159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24198207768353160638679439 36297311652529740958019159)
      ·
        refine ⟨54445967478794611437028739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36297311652529740958019159 54445967478794611437028739)
        ·
          refine ⟨81668951218191917155543109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54445967478794611437028739 81668951218191917155543109)
          ·
            refine ⟨15312928353410984466664333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81668951218191917155543109 15312928353410984466664333)
            ·
              refine ⟨5742348132529119174999125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15312928353410984466664333 5742348132529119174999125)
              ·
                refine ⟨67293142178075615332021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5742348132529119174999125 67293142178075615332021)
                ·
                  rfl

theorem cell23_3538429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 8].length) (baseStart_3538429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538429 prefixEnd_3538429 := by exact prefixLift 3538429
  have htrace : WordTrace (prefixWord ++ tailWord_3538429) baseStart_3538429 baseEnd_3538429 := by
    simpa [prefixWord, tailWord_3538429, baseEnd_3538429] using wordTrace_append hprefix tailTrace_3538429
  have hstable : (prefixWord ++ tailWord_3538429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538429).length < 2 ^ (prefixWord ++ tailWord_3538429).sum := by decide
  have hdescent : baseEnd_3538429 < baseStart_3538429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538490 : List Nat := [3, 1, 1, 1, 3, 2, 5, 1, 2, 1, 3]
def baseStart_3538490 : Nat := 118140960795 + 3538490 * 2 ^ 59
def prefixEnd_3538490 : Nat := 4983230072969 + 3 ^ 40 * 3538490 * 2
def baseEnd_3538490 : Nat := 1816946161127965875301787

theorem tailTrace_3538490 : CollatzResearch.WordTrace tailWord_3538490 prefixEnd_3538490 1816946161127965875301787 := by
  unfold tailWord_3538490
  simp only [CollatzResearch.WordTrace]
  refine ⟨32264833237665632706065231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86039555300441687216173949 32264833237665632706065231)
  ·
    refine ⟨48397249856498449059097847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32264833237665632706065231 48397249856498449059097847)
    ·
      refine ⟨72595874784747673588646771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48397249856498449059097847 72595874784747673588646771)
      ·
        refine ⟨108893812177121510382970157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72595874784747673588646771 108893812177121510382970157)
        ·
          refine ⟨40835179566420566393613809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108893812177121510382970157 40835179566420566393613809)
          ·
            refine ⟨30626384674815424795210357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40835179566420566393613809 30626384674815424795210357)
            ·
              refine ⟨2871223563263946074550971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30626384674815424795210357 2871223563263946074550971)
              ·
                refine ⟨4306835344895919111826457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2871223563263946074550971 4306835344895919111826457)
                ·
                  refine ⟨3230126508671939333869843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4306835344895919111826457 3230126508671939333869843)
                  ·
                    refine ⟨4845189763007909000804765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3230126508671939333869843 4845189763007909000804765)
                    ·
                      refine ⟨1816946161127965875301787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4845189763007909000804765 1816946161127965875301787)
                      ·
                        rfl

theorem cell23_3538490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 2, 1, 3].length) (baseStart_3538490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538490 prefixEnd_3538490 := by exact prefixLift 3538490
  have htrace : WordTrace (prefixWord ++ tailWord_3538490) baseStart_3538490 baseEnd_3538490 := by
    simpa [prefixWord, tailWord_3538490, baseEnd_3538490] using wordTrace_append hprefix tailTrace_3538490
  have hstable : (prefixWord ++ tailWord_3538490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538490).length < 2 ^ (prefixWord ++ tailWord_3538490).sum := by decide
  have hdescent : baseEnd_3538490 < baseStart_3538490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538513 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 6, 2, 2]
def baseStart_3538513 : Nat := 118140960795 + 3538513 * 2 ^ 59
def prefixEnd_3538513 : Nat := 4983230072969 + 3 ^ 40 * 3538513 * 2
def baseEnd_3538513 : Nat := 1816957971183019285314181

theorem tailTrace_3538513 : CollatzResearch.WordTrace tailWord_3538513 prefixEnd_3538513 1816957971183019285314181 := by
  unfold tailWord_3538513
  simp only [CollatzResearch.WordTrace]
  refine ⟨129060171829579205752348193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86040114553052803834898795 129060171829579205752348193)
  ·
    refine ⟨96795128872184404314261145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129060171829579205752348193 96795128872184404314261145)
    ·
      refine ⟨72596346654138303235695859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96795128872184404314261145 72596346654138303235695859)
      ·
        refine ⟨108894519981207454853543789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72596346654138303235695859 108894519981207454853543789)
        ·
          refine ⟨40835444992952795570078921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108894519981207454853543789 40835444992952795570078921)
          ·
            refine ⟨30626583744714596677559191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40835444992952795570078921 30626583744714596677559191)
            ·
              refine ⟨45939875617071895016338787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30626583744714596677559191 45939875617071895016338787)
              ·
                refine ⟨68909813425607842524508181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45939875617071895016338787 68909813425607842524508181)
                ·
                  refine ⟨3230147504325367618336321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 68909813425607842524508181 3230147504325367618336321)
                  ·
                    refine ⟨2422610628244025713752241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3230147504325367618336321 2422610628244025713752241)
                    ·
                      refine ⟨1816957971183019285314181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2422610628244025713752241 1816957971183019285314181)
                      ·
                        rfl

theorem cell23_3538513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 6, 2, 2].length) (baseStart_3538513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538513 prefixEnd_3538513 := by exact prefixLift 3538513
  have htrace : WordTrace (prefixWord ++ tailWord_3538513) baseStart_3538513 baseEnd_3538513 := by
    simpa [prefixWord, tailWord_3538513, baseEnd_3538513] using wordTrace_append hprefix tailTrace_3538513
  have hstable : (prefixWord ++ tailWord_3538513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538513).length < 2 ^ (prefixWord ++ tailWord_3538513).sum := by decide
  have hdescent : baseEnd_3538513 < baseStart_3538513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538516 : List Nat := [2, 4, 1, 1, 1, 2, 3, 1, 2, 1, 5]
def baseStart_3538516 : Nat := 118140960795 + 3538516 * 2 ^ 59
def prefixEnd_3538516 : Nat := 4983230072969 + 3 ^ 40 * 3538516 * 2
def baseEnd_3538516 : Nat := 1816959511624982773576667

theorem tailTrace_3538516 : CollatzResearch.WordTrace tailWord_3538516 prefixEnd_3538516 1816959511624982773576667 := by
  unfold tailWord_3538516
  simp only [CollatzResearch.WordTrace]
  refine ⟨64530140624284168632353701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86040187499045558176471601 64530140624284168632353701)
  ·
    refine ⟨12099401367053281618566319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64530140624284168632353701 12099401367053281618566319)
    ·
      refine ⟨18149102050579922427849479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12099401367053281618566319 18149102050579922427849479)
      ·
        refine ⟨27223653075869883641774219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18149102050579922427849479 27223653075869883641774219)
        ·
          refine ⟨40835479613804825462661329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27223653075869883641774219 40835479613804825462661329)
          ·
            refine ⟨30626609710353619096995997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40835479613804825462661329 30626609710353619096995997)
            ·
              refine ⟨11484978641382607161373499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30626609710353619096995997 11484978641382607161373499)
              ·
                refine ⟨17227467962073910742060249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11484978641382607161373499 17227467962073910742060249)
                ·
                  refine ⟨12920600971555433056545187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17227467962073910742060249 12920600971555433056545187)
                  ·
                    refine ⟨19380901457333149584817781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12920600971555433056545187 19380901457333149584817781)
                    ·
                      refine ⟨1816959511624982773576667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19380901457333149584817781 1816959511624982773576667)
                      ·
                        rfl

theorem cell23_3538516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_3538516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538516 prefixEnd_3538516 := by exact prefixLift 3538516
  have htrace : WordTrace (prefixWord ++ tailWord_3538516) baseStart_3538516 baseEnd_3538516 := by
    simpa [prefixWord, tailWord_3538516, baseEnd_3538516] using wordTrace_append hprefix tailTrace_3538516
  have hstable : (prefixWord ++ tailWord_3538516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538516).length < 2 ^ (prefixWord ++ tailWord_3538516).sum := by decide
  have hdescent : baseEnd_3538516 < baseStart_3538516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538529 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 1, 2, 7]
def baseStart_3538529 : Nat := 118140960795 + 3538529 * 2 ^ 59
def prefixEnd_3538529 : Nat := 4983230072969 + 3 ^ 40 * 3538529 * 2
def baseEnd_3538529 : Nat := 1816966186873491222714107

theorem tailTrace_3538529 : CollatzResearch.WordTrace tailWord_3538529 prefixEnd_3538529 1816966186873491222714107 := by
  unfold tailWord_3538529
  simp only [CollatzResearch.WordTrace]
  refine ⟨129060755397521240484930641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86040503598347493656620427 129060755397521240484930641)
  ·
    refine ⟨96795566548140930363697981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129060755397521240484930641 96795566548140930363697981)
    ·
      refine ⟨36298337455552848886386743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96795566548140930363697981 36298337455552848886386743)
      ·
        refine ⟨54447506183329273329580115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36298337455552848886386743 54447506183329273329580115)
        ·
          refine ⟨81671259274993909994370173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54447506183329273329580115 81671259274993909994370173)
          ·
            refine ⟨30626722228122716247888815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81671259274993909994370173 30626722228122716247888815)
            ·
              refine ⟨45940083342184074371833223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30626722228122716247888815 45940083342184074371833223)
              ·
                refine ⟨68910125013276111557749835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45940083342184074371833223 68910125013276111557749835)
                ·
                  refine ⟨103365187519914167336624753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68910125013276111557749835 103365187519914167336624753)
                  ·
                    refine ⟨77523890639935625502468565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103365187519914167336624753 77523890639935625502468565)
                    ·
                      refine ⟨1816966186873491222714107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 77523890639935625502468565 1816966186873491222714107)
                      ·
                        rfl

theorem cell23_3538529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_3538529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538529 prefixEnd_3538529 := by exact prefixLift 3538529
  have htrace : WordTrace (prefixWord ++ tailWord_3538529) baseStart_3538529 baseEnd_3538529 := by
    simpa [prefixWord, tailWord_3538529, baseEnd_3538529] using wordTrace_append hprefix tailTrace_3538529
  have hstable : (prefixWord ++ tailWord_3538529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538529).length < 2 ^ (prefixWord ++ tailWord_3538529).sum := by decide
  have hdescent : baseEnd_3538529 < baseStart_3538529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538590 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 2, 5, 2]
def baseStart_3538590 : Nat := 118140960795 + 3538590 * 2 ^ 59
def prefixEnd_3538590 : Nat := 4983230072969 + 3 ^ 40 * 3538590 * 2
def baseEnd_3538590 : Nat := 1816997509193415484051327

theorem tailTrace_3538590 : CollatzResearch.WordTrace tailWord_3538590 prefixEnd_3538590 1816997509193415484051327 := by
  unfold tailWord_3538590
  simp only [CollatzResearch.WordTrace]
  refine ⟨16132872531287530987862653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86041986833533498601934149 16132872531287530987862653)
  ·
    refine ⟨6049827199232824120448495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16132872531287530987862653 6049827199232824120448495)
    ·
      refine ⟨9074740798849236180672743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6049827199232824120448495 9074740798849236180672743)
      ·
        refine ⟨13612111198273854271009115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9074740798849236180672743 13612111198273854271009115)
        ·
          refine ⟨20418166797410781406513673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13612111198273854271009115 20418166797410781406513673)
          ·
            refine ⟨15313625098058086054885255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20418166797410781406513673 15313625098058086054885255)
            ·
              refine ⟨22970437647087129082327883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15313625098058086054885255 22970437647087129082327883)
              ·
                refine ⟨34455656470630693623491825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22970437647087129082327883 34455656470630693623491825)
                ·
                  refine ⟨25841742352973020217618869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34455656470630693623491825 25841742352973020217618869)
                  ·
                    refine ⟨2422663345591220645401769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25841742352973020217618869 2422663345591220645401769)
                    ·
                      refine ⟨1816997509193415484051327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2422663345591220645401769 1816997509193415484051327)
                      ·
                        rfl

theorem cell23_3538590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_3538590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538590 prefixEnd_3538590 := by exact prefixLift 3538590
  have htrace : WordTrace (prefixWord ++ tailWord_3538590) baseStart_3538590 baseEnd_3538590 := by
    simpa [prefixWord, tailWord_3538590, baseEnd_3538590] using wordTrace_append hprefix tailTrace_3538590
  have hstable : (prefixWord ++ tailWord_3538590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538590).length < 2 ^ (prefixWord ++ tailWord_3538590).sum := by decide
  have hdescent : baseEnd_3538590 < baseStart_3538590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538620 : List Nat := [2, 2, 2, 3, 1, 4, 1, 1, 2, 1, 4]
def baseStart_3538620 : Nat := 118140960795 + 3538620 * 2 ^ 59
def prefixEnd_3538620 : Nat := 4983230072969 + 3 ^ 40 * 3538620 * 2
def baseEnd_3538620 : Nat := 1817012913613050366676189

theorem tailTrace_3538620 : CollatzResearch.WordTrace tailWord_3538620 prefixEnd_3538620 1817012913613050366676189 := by
  unfold tailWord_3538620
  simp only [CollatzResearch.WordTrace]
  refine ⟨64532037220095781513246657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86042716293461042017662209 64532037220095781513246657)
  ·
    refine ⟨48399027915071836134934993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64532037220095781513246657 48399027915071836134934993)
    ·
      refine ⟨36299270936303877101201245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48399027915071836134934993 36299270936303877101201245)
      ·
        refine ⟨13612226601113953912950467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36299270936303877101201245 13612226601113953912950467)
        ·
          refine ⟨20418339901670930869425701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13612226601113953912950467 20418339901670930869425701)
          ·
            refine ⟨3828438731563299538017319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20418339901670930869425701 3828438731563299538017319)
            ·
              refine ⟨5742658097344949307025979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3828438731563299538017319 5742658097344949307025979)
              ·
                refine ⟨8613987146017423960538969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5742658097344949307025979 8613987146017423960538969)
                ·
                  refine ⟨6460490359513067970404227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8613987146017423960538969 6460490359513067970404227)
                  ·
                    refine ⟨9690735539269601955606341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6460490359513067970404227 9690735539269601955606341)
                    ·
                      refine ⟨1817012913613050366676189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9690735539269601955606341 1817012913613050366676189)
                      ·
                        rfl

theorem cell23_3538620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_3538620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538620 prefixEnd_3538620 := by exact prefixLift 3538620
  have htrace : WordTrace (prefixWord ++ tailWord_3538620) baseStart_3538620 baseEnd_3538620 := by
    simpa [prefixWord, tailWord_3538620, baseEnd_3538620] using wordTrace_append hprefix tailTrace_3538620
  have hstable : (prefixWord ++ tailWord_3538620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538620).length < 2 ^ (prefixWord ++ tailWord_3538620).sum := by decide
  have hdescent : baseEnd_3538620 < baseStart_3538620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538637 : List Nat := [1, 6, 2, 1, 1, 1, 1, 2, 2, 4, 2]
def baseStart_3538637 : Nat := 118140960795 + 3538637 * 2 ^ 59
def prefixEnd_3538637 : Nat := 4983230072969 + 3 ^ 40 * 3538637 * 2
def baseEnd_3538637 : Nat := 1817021642784176800163611

theorem tailTrace_3538637 : CollatzResearch.WordTrace tailWord_3538637 prefixEnd_3538637 1817021642784176800163611 := by
  unfold tailWord_3538637
  simp only [CollatzResearch.WordTrace]
  refine ⟨129064694481129974929862165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86043129654086649953241443 129064694481129974929862165)
  ·
    refine ⟨6049907553802967574837289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 129064694481129974929862165 6049907553802967574837289)
    ·
      refine ⟨4537430665352225681127967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6049907553802967574837289 4537430665352225681127967)
      ·
        refine ⟨6806145998028338521691951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4537430665352225681127967 6806145998028338521691951)
        ·
          refine ⟨10209218997042507782537927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6806145998028338521691951 10209218997042507782537927)
          ·
            refine ⟨15313828495563761673806891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10209218997042507782537927 15313828495563761673806891)
            ·
              refine ⟨22970742743345642510710337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15313828495563761673806891 22970742743345642510710337)
              ·
                refine ⟨17228057057509231883032753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22970742743345642510710337 17228057057509231883032753)
                ·
                  refine ⟨12921042793131923912274565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17228057057509231883032753 12921042793131923912274565)
                  ·
                    refine ⟨2422695523712235733551481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12921042793131923912274565 2422695523712235733551481)
                    ·
                      refine ⟨1817021642784176800163611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2422695523712235733551481 1817021642784176800163611)
                      ·
                        rfl

theorem cell23_3538637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_3538637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538637 prefixEnd_3538637 := by exact prefixLift 3538637
  have htrace : WordTrace (prefixWord ++ tailWord_3538637) baseStart_3538637 baseEnd_3538637 := by
    simpa [prefixWord, tailWord_3538637, baseEnd_3538637] using wordTrace_append hprefix tailTrace_3538637
  have hstable : (prefixWord ++ tailWord_3538637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538637).length < 2 ^ (prefixWord ++ tailWord_3538637).sum := by decide
  have hdescent : baseEnd_3538637 < baseStart_3538637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538656 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 5, 5]
def baseStart_3538656 : Nat := 118140960795 + 3538656 * 2 ^ 59
def prefixEnd_3538656 : Nat := 4983230072969 + 3 ^ 40 * 3538656 * 2
def baseEnd_3538656 : Nat := 605677132972204075275341

theorem tailTrace_3538656 : CollatzResearch.WordTrace tailWord_3538656 prefixEnd_3538656 605677132972204075275341 := by
  unfold tailWord_3538656
  simp only [CollatzResearch.WordTrace]
  refine ⟨64532693734030570587401911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86043591645374094116535881 64532693734030570587401911)
  ·
    refine ⟨96799040601045855881102867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64532693734030570587401911 96799040601045855881102867)
    ·
      refine ⟨145198560901568783821654301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96799040601045855881102867 145198560901568783821654301)
      ·
        refine ⟨54449460338088293933120363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145198560901568783821654301 54449460338088293933120363)
        ·
          refine ⟨81674190507132440899680545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54449460338088293933120363 81674190507132440899680545)
          ·
            refine ⟨61255642880349330674760409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81674190507132440899680545 61255642880349330674760409)
            ·
              refine ⟨45941732160261998006070307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61255642880349330674760409 45941732160261998006070307)
              ·
                refine ⟨68912598240392997009105461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45941732160261998006070307 68912598240392997009105461)
                ·
                  refine ⟨6460556085036843469603637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68912598240392997009105461 6460556085036843469603637)
                  ·
                    refine ⟨605677132972204075275341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6460556085036843469603637 605677132972204075275341)
                    ·
                      rfl

theorem cell23_3538656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 5, 5].length) (baseStart_3538656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538656 prefixEnd_3538656 := by exact prefixLift 3538656
  have htrace : WordTrace (prefixWord ++ tailWord_3538656) baseStart_3538656 baseEnd_3538656 := by
    simpa [prefixWord, tailWord_3538656, baseEnd_3538656] using wordTrace_append hprefix tailTrace_3538656
  have hstable : (prefixWord ++ tailWord_3538656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538656).length < 2 ^ (prefixWord ++ tailWord_3538656).sum := by decide
  have hdescent : baseEnd_3538656 < baseStart_3538656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538666 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 2, 1, 7]
def baseStart_3538666 : Nat := 118140960795 + 3538666 * 2 ^ 59
def prefixEnd_3538666 : Nat := 4983230072969 + 3 ^ 40 * 3538666 * 2
def baseEnd_3538666 : Nat := 1817036533723157186700977

theorem tailTrace_3538666 : CollatzResearch.WordTrace tailWord_3538666 prefixEnd_3538666 1817036533723157186700977 := by
  unfold tailWord_3538666
  simp only [CollatzResearch.WordTrace]
  refine ⟨32266438049506228220666963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86043834798683275255111901 32266438049506228220666963)
  ·
    refine ⟨48399657074259342331000445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32266438049506228220666963 48399657074259342331000445)
    ·
      refine ⟨18149871402847253374125167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48399657074259342331000445 18149871402847253374125167)
      ·
        refine ⟨27224807104270880061187751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18149871402847253374125167 27224807104270880061187751)
        ·
          refine ⟨40837210656406320091781627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27224807104270880061187751 40837210656406320091781627)
          ·
            refine ⟨61255815984609480137672441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40837210656406320091781627 61255815984609480137672441)
            ·
              refine ⟨45941861988457110103254331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61255815984609480137672441 45941861988457110103254331)
              ·
                refine ⟨68912792982685665154881497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45941861988457110103254331 68912792982685665154881497)
                ·
                  refine ⟨51684594737014248866161123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68912792982685665154881497 51684594737014248866161123)
                  ·
                    refine ⟨77526892105521373299241685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51684594737014248866161123 77526892105521373299241685)
                    ·
                      refine ⟨1817036533723157186700977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 77526892105521373299241685 1817036533723157186700977)
                      ·
                        rfl

theorem cell23_3538666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_3538666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538666 prefixEnd_3538666 := by exact prefixLift 3538666
  have htrace : WordTrace (prefixWord ++ tailWord_3538666) baseStart_3538666 baseEnd_3538666 := by
    simpa [prefixWord, tailWord_3538666, baseEnd_3538666] using wordTrace_append hprefix tailTrace_3538666
  have hstable : (prefixWord ++ tailWord_3538666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538666).length < 2 ^ (prefixWord ++ tailWord_3538666).sum := by decide
  have hdescent : baseEnd_3538666 < baseStart_3538666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538670 : List Nat := [4, 1, 2, 1, 1, 2, 1, 4, 3, 1, 3]
def baseStart_3538670 : Nat := 118140960795 + 3538670 * 2 ^ 59
def prefixEnd_3538670 : Nat := 4983230072969 + 3 ^ 40 * 3538670 * 2
def baseEnd_3538670 : Nat := 1817038587645775171050959

theorem tailTrace_3538670 : CollatzResearch.WordTrace tailWord_3538670 prefixEnd_3538670 1817038587645775171050959 := by
  unfold tailWord_3538670
  simp only [CollatzResearch.WordTrace]
  refine ⟨16133237261251302695726683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86043932060006947710542309 16133237261251302695726683)
  ·
    refine ⟨24199855891876954043590025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16133237261251302695726683 24199855891876954043590025)
    ·
      refine ⟨18149891918907715532692519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24199855891876954043590025 18149891918907715532692519)
      ·
        refine ⟨27224837878361573299038779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18149891918907715532692519 27224837878361573299038779)
        ·
          refine ⟨40837256817542359948558169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27224837878361573299038779 40837256817542359948558169)
          ·
            refine ⟨30627942613156769961418627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40837256817542359948558169 30627942613156769961418627)
            ·
              refine ⟨45941913919735154942127941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30627942613156769961418627 45941913919735154942127941)
              ·
                refine ⟨8614108859950341551648989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45941913919735154942127941 8614108859950341551648989)
                ·
                  refine ⟨3230290822481378081868371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8614108859950341551648989 3230290822481378081868371)
                  ·
                    refine ⟨4845436233722067122802557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3230290822481378081868371 4845436233722067122802557)
                    ·
                      refine ⟨1817038587645775171050959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4845436233722067122802557 1817038587645775171050959)
                      ·
                        rfl

theorem cell23_3538670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_3538670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538670 prefixEnd_3538670 := by exact prefixLift 3538670
  have htrace : WordTrace (prefixWord ++ tailWord_3538670) baseStart_3538670 baseEnd_3538670 := by
    simpa [prefixWord, tailWord_3538670, baseEnd_3538670] using wordTrace_append hprefix tailTrace_3538670
  have hstable : (prefixWord ++ tailWord_3538670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538670).length < 2 ^ (prefixWord ++ tailWord_3538670).sum := by decide
  have hdescent : baseEnd_3538670 < baseStart_3538670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538673 : List Nat := [1, 2, 2, 2, 2, 3, 1, 4, 1, 5]
def baseStart_3538673 : Nat := 118140960795 + 3538673 * 2 ^ 59
def prefixEnd_3538673 : Nat := 4983230072969 + 3 ^ 40 * 3538673 * 2
def baseEnd_3538673 : Nat := 605680042695912886437815

theorem tailTrace_3538673 : CollatzResearch.WordTrace tailWord_3538673 prefixEnd_3538673 605680042695912886437815 := by
  unfold tailWord_3538673
  simp only [CollatzResearch.WordTrace]
  refine ⟨129066007508999553078172673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86044005005999702052115115 129066007508999553078172673)
  ·
    refine ⟨96799505631749664808629505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129066007508999553078172673 96799505631749664808629505)
    ·
      refine ⟨72599629223812248606472129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96799505631749664808629505 72599629223812248606472129)
      ·
        refine ⟨54449721917859186454854097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72599629223812248606472129 54449721917859186454854097)
        ·
          refine ⟨40837291438394389841140573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54449721917859186454854097 40837291438394389841140573)
          ·
            refine ⟨15313984289397896190427715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40837291438394389841140573 15313984289397896190427715)
            ·
              refine ⟨22970976434096844285641573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15313984289397896190427715 22970976434096844285641573)
              ·
                refine ⟨4307058081393158303557795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22970976434096844285641573 4307058081393158303557795)
                ·
                  refine ⟨6460587122089737455336693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4307058081393158303557795 6460587122089737455336693)
                  ·
                    refine ⟨605680042695912886437815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6460587122089737455336693 605680042695912886437815)
                    ·
                      rfl

theorem cell23_3538673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 5].length) (baseStart_3538673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538673 prefixEnd_3538673 := by exact prefixLift 3538673
  have htrace : WordTrace (prefixWord ++ tailWord_3538673) baseStart_3538673 baseEnd_3538673 := by
    simpa [prefixWord, tailWord_3538673, baseEnd_3538673] using wordTrace_append hprefix tailTrace_3538673
  have hstable : (prefixWord ++ tailWord_3538673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538673).length < 2 ^ (prefixWord ++ tailWord_3538673).sum := by decide
  have hdescent : baseEnd_3538673 < baseStart_3538673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538687 : List Nat := [1, 1, 2, 2, 1, 3, 5, 3, 1, 1, 3]
def baseStart_3538687 : Nat := 118140960795 + 3538687 * 2 ^ 59
def prefixEnd_3538687 : Nat := 4983230072969 + 3 ^ 40 * 3538687 * 2
def baseEnd_3538687 : Nat := 1817047316816901604538381

theorem tailTrace_3538687 : CollatzResearch.WordTrace tailWord_3538687 prefixEnd_3538687 1817047316816901604538381 := by
  unfold tailWord_3538687
  simp only [CollatzResearch.WordTrace]
  refine ⟨129066518130948833469182315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86044345420632555646121543 129066518130948833469182315)
  ·
    refine ⟨193599777196423250203773473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129066518130948833469182315 193599777196423250203773473)
    ·
      refine ⟨145199832897317437652830105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193599777196423250203773473 145199832897317437652830105)
      ·
        refine ⟨108899874672988078239622579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145199832897317437652830105 108899874672988078239622579)
        ·
          refine ⟨163349812009482117359433869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108899874672988078239622579 163349812009482117359433869)
          ·
            refine ⟨61256179503555794009787701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163349812009482117359433869 61256179503555794009787701)
            ·
              refine ⟨5742766828458355688417597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61256179503555794009787701 5742766828458355688417597)
              ·
                refine ⟨2153537560671883383156599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5742766828458355688417597 2153537560671883383156599)
                ·
                  refine ⟨3230306341007825074734899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2153537560671883383156599 3230306341007825074734899)
                  ·
                    refine ⟨4845459511511737612102349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3230306341007825074734899 4845459511511737612102349)
                    ·
                      refine ⟨1817047316816901604538381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4845459511511737612102349 1817047316816901604538381)
                      ·
                        rfl

theorem cell23_3538687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 3, 1, 1, 3].length) (baseStart_3538687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538687 prefixEnd_3538687 := by exact prefixLift 3538687
  have htrace : WordTrace (prefixWord ++ tailWord_3538687) baseStart_3538687 baseEnd_3538687 := by
    simpa [prefixWord, tailWord_3538687, baseEnd_3538687] using wordTrace_append hprefix tailTrace_3538687
  have hstable : (prefixWord ++ tailWord_3538687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538687).length < 2 ^ (prefixWord ++ tailWord_3538687).sum := by decide
  have hdescent : baseEnd_3538687 < baseStart_3538687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538690 : List Nat := [3, 4, 1, 1, 1, 1, 1, 5, 1, 5]
def baseStart_3538690 : Nat := 118140960795 + 3538690 * 2 ^ 59
def prefixEnd_3538690 : Nat := 4983230072969 + 3 ^ 40 * 3538690 * 2
def baseEnd_3538690 : Nat := 605682952419621697600289

theorem tailTrace_3538690 : CollatzResearch.WordTrace tailWord_3538690 prefixEnd_3538690 605682952419621697600289 := by
  unfold tailWord_3538690
  simp only [CollatzResearch.WordTrace]
  refine ⟨32266656887484491245385381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86044418366625309987694349 32266656887484491245385381)
  ·
    refine ⟨6049998166403342108509759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32266656887484491245385381 6049998166403342108509759)
    ·
      refine ⟨9074997249605013162764639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6049998166403342108509759 9074997249605013162764639)
      ·
        refine ⟨13612495874407519744146959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9074997249605013162764639 13612495874407519744146959)
        ·
          refine ⟨20418743811611279616220439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13612495874407519744146959 20418743811611279616220439)
          ·
            refine ⟨30628115717416919424330659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20418743811611279616220439 30628115717416919424330659)
            ·
              refine ⟨45942173576125379136495989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30628115717416919424330659 45942173576125379136495989)
              ·
                refine ⟨4307078772761754294046499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45942173576125379136495989 4307078772761754294046499)
                ·
                  refine ⟨6460618159142631441069749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4307078772761754294046499 6460618159142631441069749)
                  ·
                    refine ⟨605682952419621697600289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6460618159142631441069749 605682952419621697600289)
                    ·
                      rfl

theorem cell23_3538690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_3538690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538690 prefixEnd_3538690 := by exact prefixLift 3538690
  have htrace : WordTrace (prefixWord ++ tailWord_3538690) baseStart_3538690 baseEnd_3538690 := by
    simpa [prefixWord, tailWord_3538690, baseEnd_3538690] using wordTrace_append hprefix tailTrace_3538690
  have hstable : (prefixWord ++ tailWord_3538690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538690).length < 2 ^ (prefixWord ++ tailWord_3538690).sum := by decide
  have hdescent : baseEnd_3538690 < baseStart_3538690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538720 : List Nat := [2, 1, 1, 5, 1, 1, 3, 3, 2, 4]
def baseStart_3538720 : Nat := 118140960795 + 3538720 * 2 ^ 59
def prefixEnd_3538720 : Nat := 4983230072969 + 3 ^ 40 * 3538720 * 2
def baseEnd_3538720 : Nat := 605688087226166658475243

theorem tailTrace_3538720 : CollatzResearch.WordTrace tailWord_3538720 prefixEnd_3538720 605688087226166658475243 := by
  unfold tailWord_3538720
  simp only [CollatzResearch.WordTrace]
  refine ⟨64533860869914640052566807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86045147826552853403422409 64533860869914640052566807)
  ·
    refine ⟨96800791304871960078850211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64533860869914640052566807 96800791304871960078850211)
    ·
      refine ⟨145201186957307940118275317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96800791304871960078850211 145201186957307940118275317)
      ·
        refine ⟨13612611277247619386088311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145201186957307940118275317 13612611277247619386088311)
        ·
          refine ⟨20418916915871429079132467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13612611277247619386088311 20418916915871429079132467)
          ·
            refine ⟨30628375373807143618698701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20418916915871429079132467 30628375373807143618698701)
            ·
              refine ⟨11485640765177678857012013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30628375373807143618698701 11485640765177678857012013)
              ·
                refine ⟨4307115286941629571379505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11485640765177678857012013 4307115286941629571379505)
                ·
                  refine ⟨3230336465206222178534629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4307115286941629571379505 3230336465206222178534629)
                  ·
                    refine ⟨605688087226166658475243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3230336465206222178534629 605688087226166658475243)
                    ·
                      rfl

theorem cell23_3538720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 2, 4].length) (baseStart_3538720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538720 prefixEnd_3538720 := by exact prefixLift 3538720
  have htrace : WordTrace (prefixWord ++ tailWord_3538720) baseStart_3538720 baseEnd_3538720 := by
    simpa [prefixWord, tailWord_3538720, baseEnd_3538720] using wordTrace_append hprefix tailTrace_3538720
  have hstable : (prefixWord ++ tailWord_3538720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538720).length < 2 ^ (prefixWord ++ tailWord_3538720).sum := by decide
  have hdescent : baseEnd_3538720 < baseStart_3538720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538740 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_3538740 : Nat := 118140960795 + 3538740 * 2 ^ 59
def prefixEnd_3538740 : Nat := 4983230072969 + 3 ^ 40 * 3538740 * 2
def baseEnd_3538740 : Nat := 1817074531291589897175637

theorem tailTrace_3538740 : CollatzResearch.WordTrace tailWord_3538740 prefixEnd_3538740 1817074531291589897175637 := by
  unfold tailWord_3538740
  simp only [CollatzResearch.WordTrace]
  refine ⟨64534225599878411760430837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86045634133171215680574449 64534225599878411760430837)
  ·
    refine ⟨6050083649988601102540391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64534225599878411760430837 6050083649988601102540391)
    ·
      refine ⟨9075125474982901653810587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6050083649988601102540391 9075125474982901653810587)
      ·
        refine ⟨13612688212474352480715881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9075125474982901653810587 13612688212474352480715881)
        ·
          refine ⟨10209516159355764360536911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13612688212474352480715881 10209516159355764360536911)
          ·
            refine ⟨15314274239033646540805367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10209516159355764360536911 15314274239033646540805367)
            ·
              refine ⟨22971411358550469811208051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15314274239033646540805367 22971411358550469811208051)
              ·
                refine ⟨34457117037825704716812077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22971411358550469811208051 34457117037825704716812077)
                ·
                  refine ⟨12921418889184639268804529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34457117037825704716812077 12921418889184639268804529)
                  ·
                    refine ⟨9691064166888479451603397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12921418889184639268804529 9691064166888479451603397)
                    ·
                      refine ⟨1817074531291589897175637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9691064166888479451603397 1817074531291589897175637)
                      ·
                        rfl

theorem cell23_3538740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_3538740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538740 prefixEnd_3538740 := by exact prefixLift 3538740
  have htrace : WordTrace (prefixWord ++ tailWord_3538740) baseStart_3538740 baseEnd_3538740 := by
    simpa [prefixWord, tailWord_3538740, baseEnd_3538740] using wordTrace_append hprefix tailTrace_3538740
  have hstable : (prefixWord ++ tailWord_3538740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538740).length < 2 ^ (prefixWord ++ tailWord_3538740).sum := by decide
  have hdescent : baseEnd_3538740 < baseStart_3538740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538834 : List Nat := [3, 2, 3, 2, 1, 1, 3, 1, 1, 4, 2]
def baseStart_3538834 : Nat := 118140960795 + 3538834 * 2 ^ 59
def prefixEnd_3538834 : Nat := 4983230072969 + 3 ^ 40 * 3538834 * 2
def baseEnd_3538834 : Nat := 1817122798473112529400205

theorem tailTrace_3538834 : CollatzResearch.WordTrace tailWord_3538834 prefixEnd_3538834 1817122798473112529400205 := by
  unfold tailWord_3538834
  simp only [CollatzResearch.WordTrace]
  refine ⟨32267969915354069393695889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86047919774277518383189037 32267969915354069393695889)
  ·
    refine ⟨24200977436515552045271917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32267969915354069393695889 24200977436515552045271917)
    ·
      refine ⟨9075366538693332016976969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24200977436515552045271917 9075366538693332016976969)
      ·
        refine ⟨6806524904019999012732727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9075366538693332016976969 6806524904019999012732727)
        ·
          refine ⟨10209787356029998519099091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6806524904019999012732727 10209787356029998519099091)
          ·
            refine ⟨15314681034044997778648637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10209787356029998519099091 15314681034044997778648637)
            ·
              refine ⟨5743005387766874166993239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15314681034044997778648637 5743005387766874166993239)
              ·
                refine ⟨8614508081650311250489859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5743005387766874166993239 8614508081650311250489859)
                ·
                  refine ⟨12921762122475466875734789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8614508081650311250489859 12921762122475466875734789)
                  ·
                    refine ⟨2422830397964150039200273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12921762122475466875734789 2422830397964150039200273)
                    ·
                      refine ⟨1817122798473112529400205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2422830397964150039200273 1817122798473112529400205)
                      ·
                        rfl

theorem cell23_3538834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_3538834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538834 prefixEnd_3538834 := by exact prefixLift 3538834
  have htrace : WordTrace (prefixWord ++ tailWord_3538834) baseStart_3538834 baseEnd_3538834 := by
    simpa [prefixWord, tailWord_3538834, baseEnd_3538834] using wordTrace_append hprefix tailTrace_3538834
  have hstable : (prefixWord ++ tailWord_3538834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538834).length < 2 ^ (prefixWord ++ tailWord_3538834).sum := by decide
  have hdescent : baseEnd_3538834 < baseStart_3538834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538853 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 6, 5]
def baseStart_3538853 : Nat := 118140960795 + 3538853 * 2 ^ 59
def prefixEnd_3538853 : Nat := 4983230072969 + 3 ^ 40 * 3538853 * 2
def baseEnd_3538853 : Nat := 605710851535182651687539

theorem tailTrace_3538853 : CollatzResearch.WordTrace tailWord_3538853 prefixEnd_3538853 605710851535182651687539 := by
  unfold tailWord_3538853
  simp only [CollatzResearch.WordTrace]
  refine ⟨129072572648347443819725213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86048381765564962546483475 129072572648347443819725213)
  ·
    refine ⟨48402214743130291432396955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129072572648347443819725213 48402214743130291432396955)
    ·
      refine ⟨72603322114695437148595433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48402214743130291432396955 72603322114695437148595433)
      ·
        refine ⟨54452491586021577861446575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72603322114695437148595433 54452491586021577861446575)
        ·
          refine ⟨81678737379032366792169863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54452491586021577861446575 81678737379032366792169863)
          ·
            refine ⟨122518106068548550188254795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81678737379032366792169863 122518106068548550188254795)
            ·
              refine ⟨183777159102822825282382193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122518106068548550188254795 183777159102822825282382193)
              ·
                refine ⟨137832869327117118961786645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183777159102822825282382193 137832869327117118961786645)
                ·
                  refine ⟨6460915749708614951333749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 137832869327117118961786645 6460915749708614951333749)
                  ·
                    refine ⟨605710851535182651687539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6460915749708614951333749 605710851535182651687539)
                    ·
                      rfl

theorem cell23_3538853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 5].length) (baseStart_3538853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538853 prefixEnd_3538853 := by exact prefixLift 3538853
  have htrace : WordTrace (prefixWord ++ tailWord_3538853) baseStart_3538853 baseEnd_3538853 := by
    simpa [prefixWord, tailWord_3538853, baseEnd_3538853] using wordTrace_append hprefix tailTrace_3538853
  have hstable : (prefixWord ++ tailWord_3538853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538853).length < 2 ^ (prefixWord ++ tailWord_3538853).sum := by decide
  have hdescent : baseEnd_3538853 < baseStart_3538853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538863 : List Nat := [1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 5]
def baseStart_3538863 : Nat := 118140960795 + 3538863 * 2 ^ 59
def prefixEnd_3538863 : Nat := 4983230072969 + 3 ^ 40 * 3538863 * 2
def baseEnd_3538863 : Nat := 1817137689412092915937571

theorem tailTrace_3538863 : CollatzResearch.WordTrace tailWord_3538863 prefixEnd_3538863 1817137689412092915937571 := by
  unfold tailWord_3538863
  simp only [CollatzResearch.WordTrace]
  refine ⟨129072937378311215527589243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86048624918874143685059495 129072937378311215527589243)
  ·
    refine ⟨193609406067466823291383865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129072937378311215527589243 193609406067466823291383865)
    ·
      refine ⟨145207054550600117468537899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193609406067466823291383865 145207054550600117468537899)
      ·
        refine ⟨217810581825900176202806849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145207054550600117468537899 217810581825900176202806849)
        ·
          refine ⟨163357936369425132152105137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217810581825900176202806849 163357936369425132152105137)
          ·
            refine ⟨122518452277068849114078853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163357936369425132152105137 122518452277068849114078853)
            ·
              refine ⟨22972209801950409208889785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122518452277068849114078853 22972209801950409208889785)
              ·
                refine ⟨17229157351462806906667339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22972209801950409208889785 17229157351462806906667339)
                ·
                  refine ⟨25843736027194210360001009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17229157351462806906667339 25843736027194210360001009)
                  ·
                    refine ⟨19382802020395657770000757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25843736027194210360001009 19382802020395657770000757)
                    ·
                      refine ⟨1817137689412092915937571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19382802020395657770000757 1817137689412092915937571)
                      ·
                        rfl

theorem cell23_3538863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 5].length) (baseStart_3538863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538863 prefixEnd_3538863 := by exact prefixLift 3538863
  have htrace : WordTrace (prefixWord ++ tailWord_3538863) baseStart_3538863 baseEnd_3538863 := by
    simpa [prefixWord, tailWord_3538863, baseEnd_3538863] using wordTrace_append hprefix tailTrace_3538863
  have hstable : (prefixWord ++ tailWord_3538863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538863).length < 2 ^ (prefixWord ++ tailWord_3538863).sum := by decide
  have hdescent : baseEnd_3538863 < baseStart_3538863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538913 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 10]
def baseStart_3538913 : Nat := 118140960795 + 3538913 * 2 ^ 59
def prefixEnd_3538913 : Nat := 4983230072969 + 3 ^ 40 * 3538913 * 2
def baseEnd_3538913 : Nat := 201907040382757524479149

theorem tailTrace_3538913 : CollatzResearch.WordTrace tailWord_3538913 prefixEnd_3538913 201907040382757524479149 := by
  unfold tailWord_3538913
  simp only [CollatzResearch.WordTrace]
  refine ⟨129074761028130074066909393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86049840685420049377939595 129074761028130074066909393)
  ·
    refine ⟨96806070771097555550182045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129074761028130074066909393 96806070771097555550182045)
    ·
      refine ⟨36302276539161583331318267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96806070771097555550182045 36302276539161583331318267)
      ·
        refine ⟨54453414808742374996977401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36302276539161583331318267 54453414808742374996977401)
        ·
          refine ⟨40840061106556781247733051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54453414808742374996977401 40840061106556781247733051)
          ·
            refine ⟨61260091659835171871599577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40840061106556781247733051 61260091659835171871599577)
            ·
              refine ⟨45945068744876378903699683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61260091659835171871599577 45945068744876378903699683)
              ·
                refine ⟨68917603117314568355549525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45945068744876378903699683 68917603117314568355549525)
                ·
                  refine ⟨201907040382757524479149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 68917603117314568355549525 201907040382757524479149)
                  ·
                    rfl

theorem cell23_3538913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 10].length) (baseStart_3538913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3538913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3538913 prefixEnd_3538913 := by exact prefixLift 3538913
  have htrace : WordTrace (prefixWord ++ tailWord_3538913) baseStart_3538913 baseEnd_3538913 := by
    simpa [prefixWord, tailWord_3538913, baseEnd_3538913] using wordTrace_append hprefix tailTrace_3538913
  have hstable : (prefixWord ++ tailWord_3538913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538913).length < 2 ^ (prefixWord ++ tailWord_3538913).sum := by decide
  have hdescent : baseEnd_3538913 < baseStart_3538913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539007 : List Nat := [1, 1, 2, 2, 3, 1, 2, 5, 2, 4]
def baseStart_3539007 : Nat := 118140960795 + 3539007 * 2 ^ 59
def prefixEnd_3539007 : Nat := 4983230072969 + 3 ^ 40 * 3539007 * 2
def baseEnd_3539007 : Nat := 605737210208780117512303

theorem tailTrace_3539007 : CollatzResearch.WordTrace tailWord_3539007 prefixEnd_3539007 605737210208780117512303 := by
  unfold tailWord_3539007
  simp only [CollatzResearch.WordTrace]
  refine ⟨129078189489789528120831275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86052126326526352080554183 129078189489789528120831275)
  ·
    refine ⟨193617284234684292181246913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129078189489789528120831275 193617284234684292181246913)
    ·
      refine ⟨145212963176013219135935185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193617284234684292181246913 145212963176013219135935185)
      ·
        refine ⟨108909722382009914351951389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145212963176013219135935185 108909722382009914351951389)
        ·
          refine ⟨40841145893253717881981771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108909722382009914351951389 40841145893253717881981771)
          ·
            refine ⟨61261718839880576822972657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40841145893253717881981771 61261718839880576822972657)
            ·
              refine ⟨45946289129910432617229493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61261718839880576822972657 45946289129910432617229493)
              ·
                refine ⟨4307464605929103057865265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45946289129910432617229493 4307464605929103057865265)
                ·
                  refine ⟨3230598454446827293398949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4307464605929103057865265 3230598454446827293398949)
                  ·
                    refine ⟨605737210208780117512303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3230598454446827293398949 605737210208780117512303)
                    ·
                      rfl

theorem cell23_3539007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 2, 4].length) (baseStart_3539007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539007 prefixEnd_3539007 := by exact prefixLift 3539007
  have htrace : WordTrace (prefixWord ++ tailWord_3539007) baseStart_3539007 baseEnd_3539007 := by
    simpa [prefixWord, tailWord_3539007, baseEnd_3539007] using wordTrace_append hprefix tailTrace_3539007
  have hstable : (prefixWord ++ tailWord_3539007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539007).length < 2 ^ (prefixWord ++ tailWord_3539007).sum := by decide
  have hdescent : baseEnd_3539007 < baseStart_3539007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539037 : List Nat := [1, 4, 4, 1, 1, 1, 11]
def baseStart_3539037 : Nat := 118140960795 + 3539037 * 2 ^ 59
def prefixEnd_3539037 : Nat := 4983230072969 + 3 ^ 40 * 3539037 * 2
def baseEnd_3539037 : Nat := 22434901667234262162491

theorem tailTrace_3539037 : CollatzResearch.WordTrace tailWord_3539037 prefixEnd_3539037 22434901667234262162491 := by
  unfold tailWord_3539037
  simp only [CollatzResearch.WordTrace]
  refine ⟨129079283679680843244423365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86052855786453895496282243 129079283679680843244423365)
  ·
    refine ⟨24202365689940158108329381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129079283679680843244423365 24202365689940158108329381)
    ·
      refine ⟨4537943566863779645311759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24202365689940158108329381 4537943566863779645311759)
      ·
        refine ⟨6806915350295669467967639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4537943566863779645311759 6806915350295669467967639)
        ·
          refine ⟨10210373025443504201951459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6806915350295669467967639 10210373025443504201951459)
          ·
            refine ⟨15315559538165256302927189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10210373025443504201951459 15315559538165256302927189)
            ·
              refine ⟨22434901667234262162491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 15315559538165256302927189 22434901667234262162491)
              ·
                rfl

theorem cell23_3539037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 11].length) (baseStart_3539037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539037 prefixEnd_3539037 := by exact prefixLift 3539037
  have htrace : WordTrace (prefixWord ++ tailWord_3539037) baseStart_3539037 baseEnd_3539037 := by
    simpa [prefixWord, tailWord_3539037, baseEnd_3539037] using wordTrace_append hprefix tailTrace_3539037
  have hstable : (prefixWord ++ tailWord_3539037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539037).length < 2 ^ (prefixWord ++ tailWord_3539037).sum := by decide
  have hdescent : baseEnd_3539037 < baseStart_3539037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539098 : List Nat := [3, 1, 1, 5, 2, 1, 2, 2, 2, 1, 3]
def baseStart_3539098 : Nat := 118140960795 + 3539098 * 2 ^ 59
def prefixEnd_3539098 : Nat := 4983230072969 + 3 ^ 40 * 3539098 * 2
def baseEnd_3539098 : Nat := 1817258357365899496498991

theorem tailTrace_3539098 : CollatzResearch.WordTrace tailWord_3539098 prefixEnd_3539098 1817258357365899496498991 := by
  unfold tailWord_3539098
  simp only [CollatzResearch.WordTrace]
  refine ⟨32270377133114962665598487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86054339021639900441595965 32270377133114962665598487)
  ·
    refine ⟨48405565699672443998397731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32270377133114962665598487 48405565699672443998397731)
    ·
      refine ⟨72608348549508665997596597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48405565699672443998397731 72608348549508665997596597)
      ·
        refine ⟨6807032676516437437274681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72608348549508665997596597 6807032676516437437274681)
        ·
          refine ⟨5105274507387328077956011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6807032676516437437274681 5105274507387328077956011)
          ·
            refine ⟨7657911761080992116934017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5105274507387328077956011 7657911761080992116934017)
            ·
              refine ⟨5743433820810744087700513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7657911761080992116934017 5743433820810744087700513)
              ·
                refine ⟨4307575365608058065775385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5743433820810744087700513 4307575365608058065775385)
                ·
                  refine ⟨3230681524206043549331539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4307575365608058065775385 3230681524206043549331539)
                  ·
                    refine ⟨4846022286309065323997309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3230681524206043549331539 4846022286309065323997309)
                    ·
                      refine ⟨1817258357365899496498991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4846022286309065323997309 1817258357365899496498991)
                      ·
                        rfl

theorem cell23_3539098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_3539098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539098 prefixEnd_3539098 := by exact prefixLift 3539098
  have htrace : WordTrace (prefixWord ++ tailWord_3539098) baseStart_3539098 baseEnd_3539098 := by
    simpa [prefixWord, tailWord_3539098, baseEnd_3539098] using wordTrace_append hprefix tailTrace_3539098
  have hstable : (prefixWord ++ tailWord_3539098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539098).length < 2 ^ (prefixWord ++ tailWord_3539098).sum := by decide
  have hdescent : baseEnd_3539098 < baseStart_3539098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539127 : List Nat := [1, 1, 3, 1, 4, 3, 1, 2, 7]
def baseStart_3539127 : Nat := 118140960795 + 3539127 * 2 ^ 59
def prefixEnd_3539127 : Nat := 4983230072969 + 3 ^ 40 * 3539127 * 2
def baseEnd_3539127 : Nat := 201919249811653320337373

theorem tailTrace_3539127 : CollatzResearch.WordTrace tailWord_3539127 prefixEnd_3539127 201919249811653320337373 := by
  unfold tailWord_3539127
  simp only [CollatzResearch.WordTrace]
  refine ⟨129082566249354788615199635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86055044166236525743466423 129082566249354788615199635)
  ·
    refine ⟨193623849374032182922799453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129082566249354788615199635 193623849374032182922799453)
    ·
      refine ⟨72608943515262068596049795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193623849374032182922799453 72608943515262068596049795)
      ·
        refine ⟨108913415272893102894074693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72608943515262068596049795 108913415272893102894074693)
        ·
          refine ⟨20421265363667456792639005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108913415272893102894074693 20421265363667456792639005)
          ·
            refine ⟨7657974511375296297239627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20421265363667456792639005 7657974511375296297239627)
            ·
              refine ⟨11486961767062944445859441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7657974511375296297239627 11486961767062944445859441)
              ·
                refine ⟨8615221325297208334394581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11486961767062944445859441 8615221325297208334394581)
                ·
                  refine ⟨201919249811653320337373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8615221325297208334394581 201919249811653320337373)
                  ·
                    rfl

theorem cell23_3539127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 7].length) (baseStart_3539127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539127 prefixEnd_3539127 := by exact prefixLift 3539127
  have htrace : WordTrace (prefixWord ++ tailWord_3539127) baseStart_3539127 baseEnd_3539127 := by
    simpa [prefixWord, tailWord_3539127, baseEnd_3539127] using wordTrace_append hprefix tailTrace_3539127
  have hstable : (prefixWord ++ tailWord_3539127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539127).length < 2 ^ (prefixWord ++ tailWord_3539127).sum := by decide
  have hdescent : baseEnd_3539127 < baseStart_3539127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539154 : List Nat := [3, 2, 2, 2, 1, 2, 1, 2, 2, 3, 3]
def baseStart_3539154 : Nat := 118140960795 + 3539154 * 2 ^ 59
def prefixEnd_3539154 : Nat := 4983230072969 + 3 ^ 40 * 3539154 * 2
def baseEnd_3539154 : Nat := 1817287112282551277398733

theorem tailTrace_3539154 : CollatzResearch.WordTrace tailWord_3539154 prefixEnd_3539154 1817287112282551277398733 := by
  unfold tailWord_3539154
  simp only [CollatzResearch.WordTrace]
  refine ⟨32270887755064243056608129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86055700680171314817621677 32270887755064243056608129)
  ·
    refine ⟨24203165816298182292456097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32270887755064243056608129 24203165816298182292456097)
    ·
      refine ⟨18152374362223636719342073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24203165816298182292456097 18152374362223636719342073)
      ·
        refine ⟨13614280771667727539506555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18152374362223636719342073 13614280771667727539506555)
        ·
          refine ⟨20421421157501591309259833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13614280771667727539506555 20421421157501591309259833)
          ·
            refine ⟨15316065868126193481944875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20421421157501591309259833 15316065868126193481944875)
            ·
              refine ⟨22974098802189290222917313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15316065868126193481944875 22974098802189290222917313)
              ·
                refine ⟨17230574101641967667187985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22974098802189290222917313 17230574101641967667187985)
                ·
                  refine ⟨12922930576231475750390989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17230574101641967667187985 12922930576231475750390989)
                  ·
                    refine ⟨4846098966086803406396621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12922930576231475750390989 4846098966086803406396621)
                    ·
                      refine ⟨1817287112282551277398733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4846098966086803406396621 1817287112282551277398733)
                      ·
                        rfl

theorem cell23_3539154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_3539154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539154 prefixEnd_3539154 := by exact prefixLift 3539154
  have htrace : WordTrace (prefixWord ++ tailWord_3539154) baseStart_3539154 baseEnd_3539154 := by
    simpa [prefixWord, tailWord_3539154, baseEnd_3539154] using wordTrace_append hprefix tailTrace_3539154
  have hstable : (prefixWord ++ tailWord_3539154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539154).length < 2 ^ (prefixWord ++ tailWord_3539154).sum := by decide
  have hdescent : baseEnd_3539154 < baseStart_3539154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539177 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 4, 1, 4]
def baseStart_3539177 : Nat := 118140960795 + 3539177 * 2 ^ 59
def prefixEnd_3539177 : Nat := 4983230072969 + 3 ^ 40 * 3539177 * 2
def baseEnd_3539177 : Nat := 1817298922337604687411127

theorem tailTrace_3539177 : CollatzResearch.WordTrace tailWord_3539177 prefixEnd_3539177 1817298922337604687411127 := by
  unfold tailWord_3539177
  simp only [CollatzResearch.WordTrace]
  refine ⟨129084389899173647154519785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86056259932782431436346523 129084389899173647154519785)
  ·
    refine ⟨96813292424380235365889839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129084389899173647154519785 96813292424380235365889839)
    ·
      refine ⟨145219938636570353048834759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96813292424380235365889839 145219938636570353048834759)
      ·
        refine ⟨217829907954855529573252139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145219938636570353048834759 217829907954855529573252139)
        ·
          refine ⟨326744861932283294359878209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217829907954855529573252139 326744861932283294359878209)
          ·
            refine ⟨245058646449212470769908657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326744861932283294359878209 245058646449212470769908657)
            ·
              refine ⟨183793984836909353077431493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245058646449212470769908657 183793984836909353077431493)
              ·
                refine ⟨34461372156920503702018405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 183793984836909353077431493 34461372156920503702018405)
                ·
                  refine ⟨6461507279422594444128451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34461372156920503702018405 6461507279422594444128451)
                  ·
                    refine ⟨9692260919133891666192677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6461507279422594444128451 9692260919133891666192677)
                    ·
                      refine ⟨1817298922337604687411127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9692260919133891666192677 1817298922337604687411127)
                      ·
                        rfl

theorem cell23_3539177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 1, 4].length) (baseStart_3539177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539177 prefixEnd_3539177 := by exact prefixLift 3539177
  have htrace : WordTrace (prefixWord ++ tailWord_3539177) baseStart_3539177 baseEnd_3539177 := by
    simpa [prefixWord, tailWord_3539177, baseEnd_3539177] using wordTrace_append hprefix tailTrace_3539177
  have hstable : (prefixWord ++ tailWord_3539177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539177).length < 2 ^ (prefixWord ++ tailWord_3539177).sum := by decide
  have hdescent : baseEnd_3539177 < baseStart_3539177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539217 : List Nat := [1, 2, 2, 1, 1, 5, 2, 1, 8]
def baseStart_3539217 : Nat := 118140960795 + 3539217 * 2 ^ 59
def prefixEnd_3539217 : Nat := 4983230072969 + 3 ^ 40 * 3539217 * 2
def baseEnd_3539217 : Nat := 201924384618198281212327

theorem tailTrace_3539217 : CollatzResearch.WordTrace tailWord_3539217 prefixEnd_3539217 201924384618198281212327 := by
  unfold tailWord_3539217
  simp only [CollatzResearch.WordTrace]
  refine ⟨129085848819028733985975905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86057232546019155990650603 129085848819028733985975905)
  ·
    refine ⟨96814386614271550489481929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129085848819028733985975905 96814386614271550489481929)
    ·
      refine ⟨72610789960703662867111447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96814386614271550489481929 72610789960703662867111447)
      ·
        refine ⟨108916184941055494300667171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72610789960703662867111447 108916184941055494300667171)
        ·
          refine ⟨163374277411583241451000757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108916184941055494300667171 163374277411583241451000757)
          ·
            refine ⟨15316338507335928886031321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163374277411583241451000757 15316338507335928886031321)
            ·
              refine ⟨11487253880501946664523491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15316338507335928886031321 11487253880501946664523491)
              ·
                refine ⟨17230880820752919996785237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11487253880501946664523491 17230880820752919996785237)
                ·
                  refine ⟨201924384618198281212327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17230880820752919996785237 201924384618198281212327)
                  ·
                    rfl

theorem cell23_3539217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 8].length) (baseStart_3539217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539217 prefixEnd_3539217 := by exact prefixLift 3539217
  have htrace : WordTrace (prefixWord ++ tailWord_3539217) baseStart_3539217 baseEnd_3539217 := by
    simpa [prefixWord, tailWord_3539217, baseEnd_3539217] using wordTrace_append hprefix tailTrace_3539217
  have hstable : (prefixWord ++ tailWord_3539217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539217).length < 2 ^ (prefixWord ++ tailWord_3539217).sum := by decide
  have hdescent : baseEnd_3539217 < baseStart_3539217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539221 : List Nat := [1, 3, 2, 1, 2, 1, 2, 6, 1, 4]
def baseStart_3539221 : Nat := 118140960795 + 3539221 * 2 ^ 59
def prefixEnd_3539221 : Nat := 4983230072969 + 3 ^ 40 * 3539221 * 2
def baseEnd_3539221 : Nat := 605773838495467505086975

theorem tailTrace_3539221 : CollatzResearch.WordTrace tailWord_3539221 prefixEnd_3539221 605773838495467505086975 := by
  unfold tailWord_3539221
  simp only [CollatzResearch.WordTrace]
  refine ⟨129085994711014242669121517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86057329807342828446081011 129085994711014242669121517)
  ·
    refine ⟨48407248016630341000920569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129085994711014242669121517 48407248016630341000920569)
    ·
      refine ⟨36305436012472755750690427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48407248016630341000920569 36305436012472755750690427)
      ·
        refine ⟨54458154018709133626035641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36305436012472755750690427 54458154018709133626035641)
        ·
          refine ⟨40843615514031850219526731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54458154018709133626035641 40843615514031850219526731)
          ·
            refine ⟨61265423271047775329290097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40843615514031850219526731 61265423271047775329290097)
            ·
              refine ⟨45949067453285831496967573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61265423271047775329290097 45949067453285831496967573)
              ·
                refine ⟨2153862536872773351420355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45949067453285831496967573 2153862536872773351420355)
                ·
                  refine ⟨3230793805309160027130533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2153862536872773351420355 3230793805309160027130533)
                  ·
                    refine ⟨605773838495467505086975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3230793805309160027130533 605773838495467505086975)
                    ·
                      rfl

theorem cell23_3539221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_3539221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539221 prefixEnd_3539221 := by exact prefixLift 3539221
  have htrace : WordTrace (prefixWord ++ tailWord_3539221) baseStart_3539221 baseEnd_3539221 := by
    simpa [prefixWord, tailWord_3539221, baseEnd_3539221] using wordTrace_append hprefix tailTrace_3539221
  have hstable : (prefixWord ++ tailWord_3539221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539221).length < 2 ^ (prefixWord ++ tailWord_3539221).sum := by decide
  have hdescent : baseEnd_3539221 < baseStart_3539221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539268 : List Nat := [2, 3, 4, 1, 2, 1, 2, 2, 6]
def baseStart_3539268 : Nat := 118140960795 + 3539268 * 2 ^ 59
def prefixEnd_3539268 : Nat := 4983230072969 + 3 ^ 40 * 3539268 * 2
def baseEnd_3539268 : Nat := 201927294341907092374801

theorem tailTrace_3539268 : CollatzResearch.WordTrace tailWord_3539268 prefixEnd_3539268 201927294341907092374801 := by
  unfold tailWord_3539268
  simp only [CollatzResearch.WordTrace]
  refine ⟨64543854470921984848041229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86058472627895979797388305 64543854470921984848041229)
  ·
    refine ⟨24203945426595744318015461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64543854470921984848041229 24203945426595744318015461)
    ·
      refine ⟨4538239767486702059627899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24203945426595744318015461 4538239767486702059627899)
      ·
        refine ⟨6807359651230053089441849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4538239767486702059627899 6807359651230053089441849)
        ·
          refine ⟨5105519738422539817081387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6807359651230053089441849 5105519738422539817081387)
          ·
            refine ⟨7658279607633809725622081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5105519738422539817081387 7658279607633809725622081)
            ·
              refine ⟨5743709705725357294216561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7658279607633809725622081 5743709705725357294216561)
              ·
                refine ⟨4307782279294017970662421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5743709705725357294216561 4307782279294017970662421)
                ·
                  refine ⟨201927294341907092374801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4307782279294017970662421 201927294341907092374801)
                  ·
                    rfl

theorem cell23_3539268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 6].length) (baseStart_3539268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539268 prefixEnd_3539268 := by exact prefixLift 3539268
  have htrace : WordTrace (prefixWord ++ tailWord_3539268) baseStart_3539268 baseEnd_3539268 := by
    simpa [prefixWord, tailWord_3539268, baseEnd_3539268] using wordTrace_append hprefix tailTrace_3539268
  have hstable : (prefixWord ++ tailWord_3539268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539268).length < 2 ^ (prefixWord ++ tailWord_3539268).sum := by decide
  have hdescent : baseEnd_3539268 < baseStart_3539268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539271 : List Nat := [1, 1, 4, 1, 2, 2, 1, 4, 2, 3, 2]
def baseStart_3539271 : Nat := 118140960795 + 3539271 * 2 ^ 59
def prefixEnd_3539271 : Nat := 4983230072969 + 3 ^ 40 * 3539271 * 2
def baseEnd_3539271 : Nat := 1817347189519127319635695

theorem tailTrace_3539271 : CollatzResearch.WordTrace tailWord_3539271 prefixEnd_3539271 1817347189519127319635695 := by
  unfold tailWord_3539271
  simp only [CollatzResearch.WordTrace]
  refine ⟨129087818360833101208441667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86058545573888734138961111 129087818360833101208441667)
  ·
    refine ⟨193631727541249651812662501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129087818360833101208441667 193631727541249651812662501)
    ·
      refine ⟨36305948913984309714874219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193631727541249651812662501 36305948913984309714874219)
      ·
        refine ⟨54458923370976464572311329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36305948913984309714874219 54458923370976464572311329)
        ·
          refine ⟨40844192528232348429233497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54458923370976464572311329 40844192528232348429233497)
          ·
            refine ⟨30633144396174261321925123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40844192528232348429233497 30633144396174261321925123)
            ·
              refine ⟨45949716594261391982887685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30633144396174261321925123 45949716594261391982887685)
              ·
                refine ⟨8615571861424010996791441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45949716594261391982887685 8615571861424010996791441)
                ·
                  refine ⟨6461678896068008247593581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8615571861424010996791441 6461678896068008247593581)
                  ·
                    refine ⟨2423129586025503092847593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6461678896068008247593581 2423129586025503092847593)
                    ·
                      refine ⟨1817347189519127319635695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2423129586025503092847593 1817347189519127319635695)
                      ·
                        rfl

theorem cell23_3539271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 3, 2].length) (baseStart_3539271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539271 prefixEnd_3539271 := by exact prefixLift 3539271
  have htrace : WordTrace (prefixWord ++ tailWord_3539271) baseStart_3539271 baseEnd_3539271 := by
    simpa [prefixWord, tailWord_3539271, baseEnd_3539271] using wordTrace_append hprefix tailTrace_3539271
  have hstable : (prefixWord ++ tailWord_3539271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539271).length < 2 ^ (prefixWord ++ tailWord_3539271).sum := by decide
  have hdescent : baseEnd_3539271 < baseStart_3539271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539335 : List Nat := [1, 1, 4, 2, 2, 1, 1, 6, 1, 2, 2]
def baseStart_3539335 : Nat := 118140960795 + 3539335 * 2 ^ 59
def prefixEnd_3539335 : Nat := 4983230072969 + 3 ^ 40 * 3539335 * 2
def baseEnd_3539335 : Nat := 1817380052281015069235401

theorem tailTrace_3539335 : CollatzResearch.WordTrace tailWord_3539335 prefixEnd_3539335 1817380052281015069235401 := by
  unfold tailWord_3539335
  simp only [CollatzResearch.WordTrace]
  refine ⟨129090152632601240138771459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86060101755067493425847639 129090152632601240138771459)
  ·
    refine ⟨193635228948901860208157189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129090152632601240138771459 193635228948901860208157189)
    ·
      refine ⟨36306605427919098789029473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193635228948901860208157189 36306605427919098789029473)
      ·
        refine ⟨27229954070939324091772105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36306605427919098789029473 27229954070939324091772105)
        ·
          refine ⟨20422465553204493068829079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27229954070939324091772105 20422465553204493068829079)
          ·
            refine ⟨30633698329806739603243619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20422465553204493068829079 30633698329806739603243619)
            ·
              refine ⟨45950547494710109404865429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30633698329806739603243619 45950547494710109404865429)
              ·
                refine ⟨2153931913814536378353067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45950547494710109404865429 2153931913814536378353067)
                ·
                  refine ⟨3230897870721804567529601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2153931913814536378353067 3230897870721804567529601)
                  ·
                    refine ⟨2423173403041353425647201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3230897870721804567529601 2423173403041353425647201)
                    ·
                      refine ⟨1817380052281015069235401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2423173403041353425647201 1817380052281015069235401)
                      ·
                        rfl

theorem cell23_3539335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_3539335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539335 prefixEnd_3539335 := by exact prefixLift 3539335
  have htrace : WordTrace (prefixWord ++ tailWord_3539335) baseStart_3539335 baseEnd_3539335 := by
    simpa [prefixWord, tailWord_3539335, baseEnd_3539335] using wordTrace_append hprefix tailTrace_3539335
  have hstable : (prefixWord ++ tailWord_3539335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539335).length < 2 ^ (prefixWord ++ tailWord_3539335).sum := by decide
  have hdescent : baseEnd_3539335 < baseStart_3539335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539338 : List Nat := [3, 1, 2, 5, 1, 1, 1, 2, 1, 1, 5]
def baseStart_3539338 : Nat := 118140960795 + 3539338 * 2 ^ 59
def prefixEnd_3539338 : Nat := 4983230072969 + 3 ^ 40 * 3539338 * 2
def baseEnd_3539338 : Nat := 1817381592722978557497887

theorem tailTrace_3539338 : CollatzResearch.WordTrace tailWord_3539338 prefixEnd_3539338 1817381592722978557497887 := by
  unfold tailWord_3539338
  simp only [CollatzResearch.WordTrace]
  refine ⟨32272565512897592912782667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86060174701060247767420445 32272565512897592912782667)
  ·
    refine ⟨48408848269346389369174001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32272565512897592912782667 48408848269346389369174001)
    ·
      refine ⟨36306636202009792026880501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48408848269346389369174001 36306636202009792026880501)
      ·
        refine ⟨3403747143938418002520047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36306636202009792026880501 3403747143938418002520047)
        ·
          refine ⟨5105620715907627003780071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3403747143938418002520047 5105620715907627003780071)
          ·
            refine ⟨7658431073861440505670107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5105620715907627003780071 7658431073861440505670107)
            ·
              refine ⟨11487646610792160758505161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7658431073861440505670107 11487646610792160758505161)
              ·
                refine ⟨8615734958094120568878871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11487646610792160758505161 8615734958094120568878871)
                ·
                  refine ⟨12923602437141180853318307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8615734958094120568878871 12923602437141180853318307)
                  ·
                    refine ⟨19385403655711771279977461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12923602437141180853318307 19385403655711771279977461)
                    ·
                      refine ⟨1817381592722978557497887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19385403655711771279977461 1817381592722978557497887)
                      ·
                        rfl

theorem cell23_3539338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_3539338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539338 prefixEnd_3539338 := by exact prefixLift 3539338
  have htrace : WordTrace (prefixWord ++ tailWord_3539338) baseStart_3539338 baseEnd_3539338 := by
    simpa [prefixWord, tailWord_3539338, baseEnd_3539338] using wordTrace_append hprefix tailTrace_3539338
  have hstable : (prefixWord ++ tailWord_3539338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539338).length < 2 ^ (prefixWord ++ tailWord_3539338).sum := by decide
  have hdescent : baseEnd_3539338 < baseStart_3539338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539351 : List Nat := [1, 1, 3, 3, 1, 1, 5, 1, 1, 3, 3]
def baseStart_3539351 : Nat := 118140960795 + 3539351 * 2 ^ 59
def prefixEnd_3539351 : Nat := 4983230072969 + 3 ^ 40 * 3539351 * 2
def baseEnd_3539351 : Nat := 1817388267971487006635327

theorem tailTrace_3539351 : CollatzResearch.WordTrace tailWord_3539351 prefixEnd_3539351 1817388267971487006635327 := by
  unfold tailWord_3539351
  simp only [CollatzResearch.WordTrace]
  refine ⟨129090736200543274871353907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86060490800362183247569271 129090736200543274871353907)
  ·
    refine ⟨193636104300814912307030861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129090736200543274871353907 193636104300814912307030861)
    ·
      refine ⟨72613539112805592115136573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193636104300814912307030861 72613539112805592115136573)
      ·
        refine ⟨27230077167302097043176215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72613539112805592115136573 27230077167302097043176215)
        ·
          refine ⟨40845115750953145564764323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27230077167302097043176215 40845115750953145564764323)
          ·
            refine ⟨61267673626429718347146485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40845115750953145564764323 61267673626429718347146485)
            ·
              refine ⟨5743844402477786095044983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61267673626429718347146485 5743844402477786095044983)
              ·
                refine ⟨8615766603716679142567475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5743844402477786095044983 8615766603716679142567475)
                ·
                  refine ⟨12923649905575018713851213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8615766603716679142567475 12923649905575018713851213)
                  ·
                    refine ⟨4846368714590632017694205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12923649905575018713851213 4846368714590632017694205)
                    ·
                      refine ⟨1817388267971487006635327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4846368714590632017694205 1817388267971487006635327)
                      ·
                        rfl

theorem cell23_3539351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_3539351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539351 prefixEnd_3539351 := by exact prefixLift 3539351
  have htrace : WordTrace (prefixWord ++ tailWord_3539351) baseStart_3539351 baseEnd_3539351 := by
    simpa [prefixWord, tailWord_3539351, baseEnd_3539351] using wordTrace_append hprefix tailTrace_3539351
  have hstable : (prefixWord ++ tailWord_3539351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539351).length < 2 ^ (prefixWord ++ tailWord_3539351).sum := by decide
  have hdescent : baseEnd_3539351 < baseStart_3539351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539358 : List Nat := [4, 3, 1, 2, 1, 1, 4, 7]
def baseStart_3539358 : Nat := 118140960795 + 3539358 * 2 ^ 59
def prefixEnd_3539358 : Nat := 4983230072969 + 3 ^ 40 * 3539358 * 2
def baseEnd_3539358 : Nat := 67310809716150684416585

theorem tailTrace_3539358 : CollatzResearch.WordTrace tailWord_3539358 prefixEnd_3539358 67310809716150684416585 := by
  unfold tailWord_3539358
  simp only [CollatzResearch.WordTrace]
  refine ⟨16136373938939739383357341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86060661007678610044572485 16136373938939739383357341)
  ·
    refine ⟨6051140227102402268759003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16136373938939739383357341 6051140227102402268759003)
    ·
      refine ⟨9076710340653603403138505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6051140227102402268759003 9076710340653603403138505)
      ·
        refine ⟨6807532755490202552353879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9076710340653603403138505 6807532755490202552353879)
        ·
          refine ⟨10211299133235303828530819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6807532755490202552353879 10211299133235303828530819)
          ·
            refine ⟨15316948699852955742796229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10211299133235303828530819 15316948699852955742796229)
            ·
              refine ⟨2871927881222429201774293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15316948699852955742796229 2871927881222429201774293)
              ·
                refine ⟨67310809716150684416585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2871927881222429201774293 67310809716150684416585)
                ·
                  rfl

theorem cell23_3539358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 7].length) (baseStart_3539358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539358 prefixEnd_3539358 := by exact prefixLift 3539358
  have htrace : WordTrace (prefixWord ++ tailWord_3539358) baseStart_3539358 baseEnd_3539358 := by
    simpa [prefixWord, tailWord_3539358, baseEnd_3539358] using wordTrace_append hprefix tailTrace_3539358
  have hstable : (prefixWord ++ tailWord_3539358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539358).length < 2 ^ (prefixWord ++ tailWord_3539358).sum := by decide
  have hdescent : baseEnd_3539358 < baseStart_3539358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539364 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 2, 2, 5]
def baseStart_3539364 : Nat := 118140960795 + 3539364 * 2 ^ 59
def prefixEnd_3539364 : Nat := 4983230072969 + 3 ^ 40 * 3539364 * 2
def baseEnd_3539364 : Nat := 1817394943219995455772767

theorem tailTrace_3539364 : CollatzResearch.WordTrace tailWord_3539364 prefixEnd_3539364 1817394943219995455772767 := by
  unfold tailWord_3539364
  simp only [CollatzResearch.WordTrace]
  refine ⟨64545605174748089045788573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86060806899664118727718097 64545605174748089045788573)
  ·
    refine ⟨24204601940530533392170715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64545605174748089045788573 24204601940530533392170715)
    ·
      refine ⟨36306902910795800088256073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24204601940530533392170715 36306902910795800088256073)
      ·
        refine ⟨27230177183096850066192055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36306902910795800088256073 27230177183096850066192055)
        ·
          refine ⟨40845265774645275099288083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27230177183096850066192055 40845265774645275099288083)
          ·
            refine ⟨61267898661967912648932125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40845265774645275099288083 61267898661967912648932125)
            ·
              refine ⟨22975461998237967243349547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61267898661967912648932125 22975461998237967243349547)
              ·
                refine ⟨34463192997356950865024321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22975461998237967243349547 34463192997356950865024321)
                ·
                  refine ⟨25847394748017713148768241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34463192997356950865024321 25847394748017713148768241)
                  ·
                    refine ⟨19385546061013284861576181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25847394748017713148768241 19385546061013284861576181)
                    ·
                      refine ⟨1817394943219995455772767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19385546061013284861576181 1817394943219995455772767)
                      ·
                        rfl

theorem cell23_3539364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_3539364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539364 prefixEnd_3539364 := by exact prefixLift 3539364
  have htrace : WordTrace (prefixWord ++ tailWord_3539364) baseStart_3539364 baseEnd_3539364 := by
    simpa [prefixWord, tailWord_3539364, baseEnd_3539364] using wordTrace_append hprefix tailTrace_3539364
  have hstable : (prefixWord ++ tailWord_3539364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539364).length < 2 ^ (prefixWord ++ tailWord_3539364).sum := by decide
  have hdescent : baseEnd_3539364 < baseStart_3539364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539378 : List Nat := [3, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2]
def baseStart_3539378 : Nat := 118140960795 + 3539378 * 2 ^ 59
def prefixEnd_3539378 : Nat := 4983230072969 + 3 ^ 40 * 3539378 * 2
def baseEnd_3539378 : Nat := 1817402131949158400997703

theorem tailTrace_3539378 : CollatzResearch.WordTrace tailWord_3539378 prefixEnd_3539378 1817402131949158400997703 := by
  unfold tailWord_3539378
  simp only [CollatzResearch.WordTrace]
  refine ⟨32272930242861364620646697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86061147314296972321724525 32272930242861364620646697)
  ·
    refine ⟨24204697682146023465485023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32272930242861364620646697 24204697682146023465485023)
    ·
      refine ⟨36307046523219035198227535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24204697682146023465485023 36307046523219035198227535)
      ·
        refine ⟨54460569784828552797341303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36307046523219035198227535 54460569784828552797341303)
        ·
          refine ⟨81690854677242829196011955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54460569784828552797341303 81690854677242829196011955)
          ·
            refine ⟨122536282015864243794017933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81690854677242829196011955 122536282015864243794017933)
            ·
              refine ⟨45951105755949091422756725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122536282015864243794017933 45951105755949091422756725)
              ·
                refine ⟨4307916164620227320883443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45951105755949091422756725 4307916164620227320883443)
                ·
                  refine ⟨6461874246930340981325165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4307916164620227320883443 6461874246930340981325165)
                  ·
                    refine ⟨2423202842598877867996937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6461874246930340981325165 2423202842598877867996937)
                    ·
                      refine ⟨1817402131949158400997703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2423202842598877867996937 1817402131949158400997703)
                      ·
                        rfl

theorem cell23_3539378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2].length) (baseStart_3539378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539378 prefixEnd_3539378 := by exact prefixLift 3539378
  have htrace : WordTrace (prefixWord ++ tailWord_3539378) baseStart_3539378 baseEnd_3539378 := by
    simpa [prefixWord, tailWord_3539378, baseEnd_3539378] using wordTrace_append hprefix tailTrace_3539378
  have hstable : (prefixWord ++ tailWord_3539378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539378).length < 2 ^ (prefixWord ++ tailWord_3539378).sum := by decide
  have hdescent : baseEnd_3539378 < baseStart_3539378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539412 : List Nat := [2, 4, 1, 2, 2, 3, 1, 2, 1, 3, 2]
def baseStart_3539412 : Nat := 118140960795 + 3539412 * 2 ^ 59
def prefixEnd_3539412 : Nat := 4983230072969 + 3 ^ 40 * 3539412 * 2
def baseEnd_3539412 : Nat := 1817419590291411267972547

theorem tailTrace_3539412 : CollatzResearch.WordTrace tailWord_3539412 prefixEnd_3539412 1817419590291411267972547 := by
  unfold tailWord_3539412
  simp only [CollatzResearch.WordTrace]
  refine ⟨64546480526661141144662245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86061974035548188192882993 64546480526661141144662245)
  ·
    refine ⟨12102465098748963964624171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64546480526661141144662245 12102465098748963964624171)
    ·
      refine ⟨18153697648123445946936257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12102465098748963964624171 18153697648123445946936257)
      ·
        refine ⟨13615273236092584460202193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18153697648123445946936257 13615273236092584460202193)
        ·
          refine ⟨10211454927069438345151645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13615273236092584460202193 10211454927069438345151645)
          ·
            refine ⟨3829295597651039379431867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10211454927069438345151645 3829295597651039379431867)
            ·
              refine ⟨5743943396476559069147801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3829295597651039379431867 5743943396476559069147801)
              ·
                refine ⟨4307957547357419301860851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5743943396476559069147801 4307957547357419301860851)
                ·
                  refine ⟨6461936321036128952791277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4307957547357419301860851 6461936321036128952791277)
                  ·
                    refine ⟨2423226120388548357296729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6461936321036128952791277 2423226120388548357296729)
                    ·
                      refine ⟨1817419590291411267972547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2423226120388548357296729 1817419590291411267972547)
                      ·
                        rfl

theorem cell23_3539412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_3539412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539412 prefixEnd_3539412 := by exact prefixLift 3539412
  have htrace : WordTrace (prefixWord ++ tailWord_3539412) baseStart_3539412 baseEnd_3539412 := by
    simpa [prefixWord, tailWord_3539412, baseEnd_3539412] using wordTrace_append hprefix tailTrace_3539412
  have hstable : (prefixWord ++ tailWord_3539412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539412).length < 2 ^ (prefixWord ++ tailWord_3539412).sum := by decide
  have hdescent : baseEnd_3539412 < baseStart_3539412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539441 : List Nat := [1, 2, 2, 2, 3, 1, 2, 2, 2, 3, 3]
def baseStart_3539441 : Nat := 118140960795 + 3539441 * 2 ^ 59
def prefixEnd_3539441 : Nat := 4983230072969 + 3 ^ 40 * 3539441 * 2
def baseEnd_3539441 : Nat := 1817434481230391654509913

theorem tailTrace_3539441 : CollatzResearch.WordTrace tailWord_3539441 prefixEnd_3539441 1817434481230391654509913 := by
  unfold tailWord_3539441
  simp only [CollatzResearch.WordTrace]
  refine ⟨129094018770217220242130177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86062679180144813494753451 129094018770217220242130177)
  ·
    refine ⟨96820514077662915181597633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129094018770217220242130177 96820514077662915181597633)
    ·
      refine ⟨72615385558247186386198225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96820514077662915181597633 72615385558247186386198225)
      ·
        refine ⟨54461539168685389789648669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72615385558247186386198225 54461539168685389789648669)
        ·
          refine ⟨20423077188257021171118251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54461539168685389789648669 20423077188257021171118251)
          ·
            refine ⟨30634615782385531756677377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20423077188257021171118251 30634615782385531756677377)
            ·
              refine ⟨22975961836789148817508033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30634615782385531756677377 22975961836789148817508033)
              ·
                refine ⟨17231971377591861613131025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22975961836789148817508033 17231971377591861613131025)
                ·
                  refine ⟨12923978533193896209848269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17231971377591861613131025 12923978533193896209848269)
                  ·
                    refine ⟨4846491949947711078693101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12923978533193896209848269 4846491949947711078693101)
                    ·
                      refine ⟨1817434481230391654509913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4846491949947711078693101 1817434481230391654509913)
                      ·
                        rfl

theorem cell23_3539441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_3539441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539441 prefixEnd_3539441 := by exact prefixLift 3539441
  have htrace : WordTrace (prefixWord ++ tailWord_3539441) baseStart_3539441 baseEnd_3539441 := by
    simpa [prefixWord, tailWord_3539441, baseEnd_3539441] using wordTrace_append hprefix tailTrace_3539441
  have hstable : (prefixWord ++ tailWord_3539441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539441).length < 2 ^ (prefixWord ++ tailWord_3539441).sum := by decide
  have hdescent : baseEnd_3539441 < baseStart_3539441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539586 : List Nat := [3, 4, 3, 1, 1, 1, 2, 1, 2, 2, 3]
def baseStart_3539586 : Nat := 118140960795 + 3539586 * 2 ^ 59
def prefixEnd_3539586 : Nat := 4983230072969 + 3 ^ 40 * 3539586 * 2
def baseEnd_3539586 : Nat := 1817508935925293587196747

theorem tailTrace_3539586 : CollatzResearch.WordTrace tailWord_3539586 prefixEnd_3539586 1817508935925293587196747 := by
  unfold tailWord_3539586
  simp only [CollatzResearch.WordTrace]
  refine ⟨32274826838672977501539653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86066204903127940004105741 32274826838672977501539653)
  ·
    refine ⟨6051530032251183281538685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32274826838672977501539653 6051530032251183281538685)
    ·
      refine ⟨2269323762094193730577007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6051530032251183281538685 2269323762094193730577007)
      ·
        refine ⟨3403985643141290595865511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2269323762094193730577007 3403985643141290595865511)
        ·
          refine ⟨5105978464711935893798267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3403985643141290595865511 5105978464711935893798267)
          ·
            refine ⟨7658967697067903840697401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5105978464711935893798267 7658967697067903840697401)
            ·
              refine ⟨5744225772800927880523051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7658967697067903840697401 5744225772800927880523051)
              ·
                refine ⟨8616338659201391820784577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5744225772800927880523051 8616338659201391820784577)
                ·
                  refine ⟨6462253994401043865588433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8616338659201391820784577 6462253994401043865588433)
                  ·
                    refine ⟨4846690495800782899191325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6462253994401043865588433 4846690495800782899191325)
                    ·
                      refine ⟨1817508935925293587196747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4846690495800782899191325 1817508935925293587196747)
                      ·
                        rfl

theorem cell23_3539586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_3539586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539586 prefixEnd_3539586 := by exact prefixLift 3539586
  have htrace : WordTrace (prefixWord ++ tailWord_3539586) baseStart_3539586 baseEnd_3539586 := by
    simpa [prefixWord, tailWord_3539586, baseEnd_3539586] using wordTrace_append hprefix tailTrace_3539586
  have hstable : (prefixWord ++ tailWord_3539586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539586).length < 2 ^ (prefixWord ++ tailWord_3539586).sum := by decide
  have hdescent : baseEnd_3539586 < baseStart_3539586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539598 : List Nat := [4, 1, 1, 3, 1, 1, 3, 2, 1, 6]
def baseStart_3539598 : Nat := 118140960795 + 3539598 * 2 ^ 59
def prefixEnd_3539598 : Nat := 4983230072969 + 3 ^ 40 * 3539598 * 2
def baseEnd_3539598 : Nat := 605838365897715846748897

theorem tailTrace_3539598 : CollatzResearch.WordTrace tailWord_3539598 prefixEnd_3539598 605838365897715846748897 := by
  unfold tailWord_3539598
  simp only [CollatzResearch.WordTrace]
  refine ⟨16137468128831054506949431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86066496687098957370396965 16137468128831054506949431)
  ·
    refine ⟨24206202193246581760424147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16137468128831054506949431 24206202193246581760424147)
    ·
      refine ⟨36309303289869872640636221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24206202193246581760424147 36309303289869872640636221)
      ·
        refine ⟨13615988733701202240238583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36309303289869872640636221 13615988733701202240238583)
        ·
          refine ⟨20423983100551803360357875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13615988733701202240238583 20423983100551803360357875)
          ·
            refine ⟨30635974650827705040536813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20423983100551803360357875 30635974650827705040536813)
            ·
              refine ⟨11488490494060389390201305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30635974650827705040536813 11488490494060389390201305)
              ·
                refine ⟨8616367870545292042650979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11488490494060389390201305 8616367870545292042650979)
                ·
                  refine ⟨12924551805817938063976469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8616367870545292042650979 12924551805817938063976469)
                  ·
                    refine ⟨605838365897715846748897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12924551805817938063976469 605838365897715846748897)
                    ·
                      rfl

theorem cell23_3539598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_3539598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539598 prefixEnd_3539598 := by exact prefixLift 3539598
  have htrace : WordTrace (prefixWord ++ tailWord_3539598) baseStart_3539598 baseEnd_3539598 := by
    simpa [prefixWord, tailWord_3539598, baseEnd_3539598] using wordTrace_append hprefix tailTrace_3539598
  have hstable : (prefixWord ++ tailWord_3539598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539598).length < 2 ^ (prefixWord ++ tailWord_3539598).sum := by decide
  have hdescent : baseEnd_3539598 < baseStart_3539598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539602 : List Nat := [3, 2, 3, 1, 2, 2, 3, 1, 1, 5]
def baseStart_3539602 : Nat := 118140960795 + 3539602 * 2 ^ 59
def prefixEnd_3539602 : Nat := 4983230072969 + 3 ^ 40 * 3539602 * 2
def baseEnd_3539602 : Nat := 605839050538588508198891

theorem tailTrace_3539602 : CollatzResearch.WordTrace tailWord_3539602 prefixEnd_3539602 605839050538588508198891 := by
  unfold tailWord_3539602
  simp only [CollatzResearch.WordTrace]
  refine ⟨32274972730658486184685265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86066593948422629825827373 32274972730658486184685265)
  ·
    refine ⟨24206229547993864638513949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32274972730658486184685265 24206229547993864638513949)
    ·
      refine ⟨9077336080497699239442731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24206229547993864638513949 9077336080497699239442731)
      ·
        refine ⟨13616004120746548859164097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9077336080497699239442731 13616004120746548859164097)
        ·
          refine ⟨10212003090559911644373073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13616004120746548859164097 10212003090559911644373073)
          ·
            refine ⟨7659002317919933733279805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10212003090559911644373073 7659002317919933733279805)
            ·
              refine ⟨2872125869219975149979927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7659002317919933733279805 2872125869219975149979927)
              ·
                refine ⟨4308188803829962724969891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2872125869219975149979927 4308188803829962724969891)
                ·
                  refine ⟨6462283205744944087454837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4308188803829962724969891 6462283205744944087454837)
                  ·
                    refine ⟨605839050538588508198891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6462283205744944087454837 605839050538588508198891)
                    ·
                      rfl

theorem cell23_3539602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_3539602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539602 prefixEnd_3539602 := by exact prefixLift 3539602
  have htrace : WordTrace (prefixWord ++ tailWord_3539602) baseStart_3539602 baseEnd_3539602 := by
    simpa [prefixWord, tailWord_3539602, baseEnd_3539602] using wordTrace_append hprefix tailTrace_3539602
  have hstable : (prefixWord ++ tailWord_3539602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539602).length < 2 ^ (prefixWord ++ tailWord_3539602).sum := by decide
  have hdescent : baseEnd_3539602 < baseStart_3539602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539616 : List Nat := [2, 1, 1, 4, 4, 2, 2, 2, 1, 1, 3]
def baseStart_3539616 : Nat := 118140960795 + 3539616 * 2 ^ 59
def prefixEnd_3539616 : Nat := 4983230072969 + 3 ^ 40 * 3539616 * 2
def baseEnd_3539616 : Nat := 1817524340344928469821609

theorem tailTrace_3539616 : CollatzResearch.WordTrace tailWord_3539616 prefixEnd_3539616 1817524340344928469821609 := by
  unfold tailWord_3539616
  simp only [CollatzResearch.WordTrace]
  refine ⟨64550200772291612564875351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86066934363055483419833801 64550200772291612564875351)
  ·
    refine ⟨96825301158437418847313027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64550200772291612564875351 96825301158437418847313027)
    ·
      refine ⟨145237951737656128270969541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96825301158437418847313027 145237951737656128270969541)
      ·
        refine ⟨27232115950810524050806789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145237951737656128270969541 27232115950810524050806789)
        ·
          refine ⟨5106021740776973259526273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27232115950810524050806789 5106021740776973259526273)
          ·
            refine ⟨3829516305582729944644705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5106021740776973259526273 3829516305582729944644705)
            ·
              refine ⟨2872137229187047458483529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3829516305582729944644705 2872137229187047458483529)
              ·
                refine ⟨2154102921890285593862647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2872137229187047458483529 2154102921890285593862647)
                ·
                  refine ⟨3231154382835428390793971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2154102921890285593862647 3231154382835428390793971)
                  ·
                    refine ⟨4846731574253142586190957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3231154382835428390793971 4846731574253142586190957)
                    ·
                      refine ⟨1817524340344928469821609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4846731574253142586190957 1817524340344928469821609)
                      ·
                        rfl

theorem cell23_3539616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_3539616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539616 prefixEnd_3539616 := by exact prefixLift 3539616
  have htrace : WordTrace (prefixWord ++ tailWord_3539616) baseStart_3539616 baseEnd_3539616 := by
    simpa [prefixWord, tailWord_3539616, baseEnd_3539616] using wordTrace_append hprefix tailTrace_3539616
  have hstable : (prefixWord ++ tailWord_3539616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539616).length < 2 ^ (prefixWord ++ tailWord_3539616).sum := by decide
  have hdescent : baseEnd_3539616 < baseStart_3539616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539641 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 4, 7]
def baseStart_3539641 : Nat := 118140960795 + 3539641 * 2 ^ 59
def prefixEnd_3539641 : Nat := 4983230072969 + 3 ^ 40 * 3539641 * 2
def baseEnd_3539641 : Nat := 605845725787096957336331

theorem tailTrace_3539641 : CollatzResearch.WordTrace tailWord_3539641 prefixEnd_3539641 605845725787096957336331 := by
  unfold tailWord_3539641
  simp only [CollatzResearch.WordTrace]
  refine ⟨129101313369492654399410777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86067542246328436266273851 129101313369492654399410777)
  ·
    refine ⟨96825985027119490799558083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129101313369492654399410777 96825985027119490799558083)
    ·
      refine ⟨145238977540679236199337125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96825985027119490799558083 145238977540679236199337125)
      ·
        refine ⟨27232308288877356787375711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145238977540679236199337125 27232308288877356787375711)
        ·
          refine ⟨40848462433316035181063567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27232308288877356787375711 40848462433316035181063567)
          ·
            refine ⟨61272693649974052771595351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40848462433316035181063567 61272693649974052771595351)
            ·
              refine ⟨91909040474961079157393027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61272693649974052771595351 91909040474961079157393027)
              ·
                refine ⟨137863560712441618736089541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91909040474961079157393027 137863560712441618736089541)
                ·
                  refine ⟨25849417633582803513016789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137863560712441618736089541 25849417633582803513016789)
                  ·
                    refine ⟨605845725787096957336331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25849417633582803513016789 605845725787096957336331)
                    ·
                      rfl

theorem cell23_3539641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 7].length) (baseStart_3539641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539641 prefixEnd_3539641 := by exact prefixLift 3539641
  have htrace : WordTrace (prefixWord ++ tailWord_3539641) baseStart_3539641 baseEnd_3539641 := by
    simpa [prefixWord, tailWord_3539641, baseEnd_3539641] using wordTrace_append hprefix tailTrace_3539641
  have hstable : (prefixWord ++ tailWord_3539641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539641).length < 2 ^ (prefixWord ++ tailWord_3539641).sum := by decide
  have hdescent : baseEnd_3539641 < baseStart_3539641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539672 : List Nat := [2, 1, 2, 2, 3, 2, 3, 2, 2, 1, 3]
def baseStart_3539672 : Nat := 118140960795 + 3539672 * 2 ^ 59
def prefixEnd_3539672 : Nat := 4983230072969 + 3 ^ 40 * 3539672 * 2
def baseEnd_3539672 : Nat := 1817553095261580250721351

theorem tailTrace_3539672 : CollatzResearch.WordTrace tailWord_3539672 prefixEnd_3539672 1817553095261580250721351 := by
  unfold tailWord_3539672
  simp only [CollatzResearch.WordTrace]
  refine ⟨64551222016190173346894635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86068296021586897795859513 64551222016190173346894635)
  ·
    refine ⟨96826833024285260020341953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64551222016190173346894635 96826833024285260020341953)
    ·
      refine ⟨72620124768213945015256465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96826833024285260020341953 72620124768213945015256465)
      ·
        refine ⟨54465093576160458761442349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72620124768213945015256465 54465093576160458761442349)
        ·
          refine ⟨20424410091060172035540881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54465093576160458761442349 20424410091060172035540881)
          ·
            refine ⟨15318307568295129026655661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20424410091060172035540881 15318307568295129026655661)
            ·
              refine ⟨5744365338110673384995873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15318307568295129026655661 5744365338110673384995873)
              ·
                refine ⟨4308274003583005038746905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5744365338110673384995873 4308274003583005038746905)
                ·
                  refine ⟨3231205502687253779060179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4308274003583005038746905 3231205502687253779060179)
                  ·
                    refine ⟨4846808254030880668590269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3231205502687253779060179 4846808254030880668590269)
                    ·
                      refine ⟨1817553095261580250721351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4846808254030880668590269 1817553095261580250721351)
                      ·
                        rfl

theorem cell23_3539672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_3539672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539672 prefixEnd_3539672 := by exact prefixLift 3539672
  have htrace : WordTrace (prefixWord ++ tailWord_3539672) baseStart_3539672 baseEnd_3539672 := by
    simpa [prefixWord, tailWord_3539672, baseEnd_3539672] using wordTrace_append hprefix tailTrace_3539672
  have hstable : (prefixWord ++ tailWord_3539672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539672).length < 2 ^ (prefixWord ++ tailWord_3539672).sum := by decide
  have hdescent : baseEnd_3539672 < baseStart_3539672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539746 : List Nat := [3, 3, 1, 1, 2, 2, 4, 1, 2, 2, 2]
def baseStart_3539746 : Nat := 118140960795 + 3539746 * 2 ^ 59
def prefixEnd_3539746 : Nat := 4983230072969 + 3 ^ 40 * 3539746 * 2
def baseEnd_3539746 : Nat := 1817591092830012961196011

theorem tailTrace_3539746 : CollatzResearch.WordTrace tailWord_3539746 prefixEnd_3539746 1817591092830012961196011 := by
  unfold tailWord_3539746
  simp only [CollatzResearch.WordTrace]
  refine ⟨32276285758528064332995773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86070095356074838221322061 32276285758528064332995773)
  ·
    refine ⟨12103607159448024124873415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32276285758528064332995773 12103607159448024124873415)
    ·
      refine ⟨18155410739172036187310123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12103607159448024124873415 18155410739172036187310123)
      ·
        refine ⟨27233116108758054280965185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18155410739172036187310123 27233116108758054280965185)
        ·
          refine ⟨20424837081568540710723889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27233116108758054280965185 20424837081568540710723889)
          ·
            refine ⟨15318627811176405533042917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20424837081568540710723889 15318627811176405533042917)
            ·
              refine ⟨2872242714595576037445547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15318627811176405533042917 2872242714595576037445547)
              ·
                refine ⟨4308364071893364056168321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2872242714595576037445547 4308364071893364056168321)
                ·
                  refine ⟨3231273053920023042126241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4308364071893364056168321 3231273053920023042126241)
                  ·
                    refine ⟨2423454790440017281594681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3231273053920023042126241 2423454790440017281594681)
                    ·
                      refine ⟨1817591092830012961196011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2423454790440017281594681 1817591092830012961196011)
                      ·
                        rfl

theorem cell23_3539746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_3539746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539746 prefixEnd_3539746 := by exact prefixLift 3539746
  have htrace : WordTrace (prefixWord ++ tailWord_3539746) baseStart_3539746 baseEnd_3539746 := by
    simpa [prefixWord, tailWord_3539746, baseEnd_3539746] using wordTrace_append hprefix tailTrace_3539746
  have hstable : (prefixWord ++ tailWord_3539746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539746).length < 2 ^ (prefixWord ++ tailWord_3539746).sum := by decide
  have hdescent : baseEnd_3539746 < baseStart_3539746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539765 : List Nat := [1, 3, 3, 1, 3, 1, 1, 3, 2, 5]
def baseStart_3539765 : Nat := 118140960795 + 3539765 * 2 ^ 59
def prefixEnd_3539765 : Nat := 4983230072969 + 3 ^ 40 * 3539765 * 2
def baseEnd_3539765 : Nat := 605866949654149462286141

theorem tailTrace_3539765 : CollatzResearch.WordTrace tailWord_3539765 prefixEnd_3539765 605866949654149462286141 := by
  unfold tailWord_3539765
  simp only [CollatzResearch.WordTrace]
  refine ⟨129105836021043423576924749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86070557347362282384616499 129105836021043423576924749)
  ·
    refine ⟨48414688507891283841346781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129105836021043423576924749 48414688507891283841346781)
    ·
      refine ⟨18155508190459231440505043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48414688507891283841346781 18155508190459231440505043)
      ·
        refine ⟨27233262285688847160757565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18155508190459231440505043 27233262285688847160757565)
        ·
          refine ⟨10212473357133317685284087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27233262285688847160757565 10212473357133317685284087)
          ·
            refine ⟨15318710035699976527926131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10212473357133317685284087 15318710035699976527926131)
            ·
              refine ⟨22978065053549964791889197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15318710035699976527926131 22978065053549964791889197)
              ·
                refine ⟨8616774395081236796958449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22978065053549964791889197 8616774395081236796958449)
                ·
                  refine ⟨6462580796310927597718837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8616774395081236796958449 6462580796310927597718837)
                  ·
                    refine ⟨605866949654149462286141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6462580796310927597718837 605866949654149462286141)
                    ·
                      rfl

theorem cell23_3539765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_3539765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539765 prefixEnd_3539765 := by exact prefixLift 3539765
  have htrace : WordTrace (prefixWord ++ tailWord_3539765) baseStart_3539765 baseEnd_3539765 := by
    simpa [prefixWord, tailWord_3539765, baseEnd_3539765] using wordTrace_append hprefix tailTrace_3539765
  have hstable : (prefixWord ++ tailWord_3539765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539765).length < 2 ^ (prefixWord ++ tailWord_3539765).sum := by decide
  have hdescent : baseEnd_3539765 < baseStart_3539765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539785 : List Nat := [1, 2, 1, 1, 2, 5, 2, 2, 2, 1, 4]
def baseStart_3539785 : Nat := 118140960795 + 3539785 * 2 ^ 59
def prefixEnd_3539785 : Nat := 4983230072969 + 3 ^ 40 * 3539785 * 2
def baseEnd_3539785 : Nat := 1817611118575538308608331

theorem tailTrace_3539785 : CollatzResearch.WordTrace tailWord_3539785 prefixEnd_3539785 1817611118575538308608331 := by
  unfold tailWord_3539785
  simp only [CollatzResearch.WordTrace]
  refine ⟨129106565480970966992652809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86071043653980644661768539 129106565480970966992652809)
  ·
    refine ⟨96829924110728225244489607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129106565480970966992652809 96829924110728225244489607)
    ·
      refine ⟨145244886166092337866734411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96829924110728225244489607 145244886166092337866734411)
      ·
        refine ⟨217867329249138506800101617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145244886166092337866734411 217867329249138506800101617)
        ·
          refine ⟨163400496936853880100076213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217867329249138506800101617 163400496936853880100076213)
          ·
            refine ⟨15318796587830051259382145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163400496936853880100076213 15318796587830051259382145)
            ·
              refine ⟨11489097440872538444536609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15318796587830051259382145 11489097440872538444536609)
              ·
                refine ⟨8616823080654403833402457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11489097440872538444536609 8616823080654403833402457)
                ·
                  refine ⟨6462617310490802875051843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8616823080654403833402457 6462617310490802875051843)
                  ·
                    refine ⟨9693925965736204312577765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6462617310490802875051843 9693925965736204312577765)
                    ·
                      refine ⟨1817611118575538308608331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9693925965736204312577765 1817611118575538308608331)
                      ·
                        rfl

theorem cell23_3539785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 1, 4].length) (baseStart_3539785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539785 prefixEnd_3539785 := by exact prefixLift 3539785
  have htrace : WordTrace (prefixWord ++ tailWord_3539785) baseStart_3539785 baseEnd_3539785 := by
    simpa [prefixWord, tailWord_3539785, baseEnd_3539785] using wordTrace_append hprefix tailTrace_3539785
  have hstable : (prefixWord ++ tailWord_3539785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539785).length < 2 ^ (prefixWord ++ tailWord_3539785).sum := by decide
  have hdescent : baseEnd_3539785 < baseStart_3539785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539802 : List Nat := [3, 1, 1, 2, 1, 5, 1, 1, 2, 4, 2]
def baseStart_3539802 : Nat := 118140960795 + 3539802 * 2 ^ 59
def prefixEnd_3539802 : Nat := 4983230072969 + 3 ^ 40 * 3539802 * 2
def baseEnd_3539802 : Nat := 1817619847746664742095753

theorem tailTrace_3539802 : CollatzResearch.WordTrace tailWord_3539802 prefixEnd_3539802 1817619847746664742095753 := by
  unfold tailWord_3539802
  simp only [CollatzResearch.WordTrace]
  refine ⟨32276796380477344724005415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86071457014606252597347773 32276796380477344724005415)
  ·
    refine ⟨48415194570716017086008123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32276796380477344724005415 48415194570716017086008123)
    ·
      refine ⟨72622791856074025629012185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48415194570716017086008123 72622791856074025629012185)
      ·
        refine ⟨54467093892055519221759139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72622791856074025629012185 54467093892055519221759139)
        ·
          refine ⟨81700640838083278832638709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54467093892055519221759139 81700640838083278832638709)
          ·
            refine ⟨7659435078570307390559879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81700640838083278832638709 7659435078570307390559879)
            ·
              refine ⟨11489152617855461085839819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7659435078570307390559879 11489152617855461085839819)
              ·
                refine ⟨17233728926783191628759729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11489152617855461085839819 17233728926783191628759729)
                ·
                  refine ⟨12925296695087393721569797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17233728926783191628759729 12925296695087393721569797)
                  ·
                    refine ⟨2423493130328886322794337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12925296695087393721569797 2423493130328886322794337)
                    ·
                      refine ⟨1817619847746664742095753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2423493130328886322794337 1817619847746664742095753)
                      ·
                        rfl

theorem cell23_3539802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 2, 4, 2].length) (baseStart_3539802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539802 prefixEnd_3539802 := by exact prefixLift 3539802
  have htrace : WordTrace (prefixWord ++ tailWord_3539802) baseStart_3539802 baseEnd_3539802 := by
    simpa [prefixWord, tailWord_3539802, baseEnd_3539802] using wordTrace_append hprefix tailTrace_3539802
  have hstable : (prefixWord ++ tailWord_3539802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539802).length < 2 ^ (prefixWord ++ tailWord_3539802).sum := by decide
  have hdescent : baseEnd_3539802 < baseStart_3539802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539812 : List Nat := [2, 3, 1, 1, 4, 2, 1, 2, 3, 4]
def baseStart_3539812 : Nat := 118140960795 + 3539812 * 2 ^ 59
def prefixEnd_3539812 : Nat := 4983230072969 + 3 ^ 40 * 3539812 * 2
def baseEnd_3539812 : Nat := 605874994184403234323569

theorem tailTrace_3539812 : CollatzResearch.WordTrace tailWord_3539812 prefixEnd_3539812 605874994184403234323569 := by
  unfold tailWord_3539812
  simp only [CollatzResearch.WordTrace]
  refine ⟨64553775125936575301942845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86071700167915433735923793 64553775125936575301942845)
  ·
    refine ⟨24207665672226215738228567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64553775125936575301942845 24207665672226215738228567)
    ·
      refine ⟨36311498508339323607342851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24207665672226215738228567 36311498508339323607342851)
      ·
        refine ⟨54467247762508985411014277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36311498508339323607342851 54467247762508985411014277)
        ·
          refine ⟨10212608955470434764565177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54467247762508985411014277 10212608955470434764565177)
          ·
            refine ⟨7659456716602826073423883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10212608955470434764565177 7659456716602826073423883)
            ·
              refine ⟨11489185074904239110135825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7659456716602826073423883 11489185074904239110135825)
              ·
                refine ⟨8616888806178179332601869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11489185074904239110135825 8616888806178179332601869)
                ·
                  refine ⟨3231333302316817249725701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8616888806178179332601869 3231333302316817249725701)
                  ·
                    refine ⟨605874994184403234323569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3231333302316817249725701 605874994184403234323569)
                    ·
                      rfl

theorem cell23_3539812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_3539812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539812 prefixEnd_3539812 := by exact prefixLift 3539812
  have htrace : WordTrace (prefixWord ++ tailWord_3539812) baseStart_3539812 baseEnd_3539812 := by
    simpa [prefixWord, tailWord_3539812, baseEnd_3539812] using wordTrace_append hprefix tailTrace_3539812
  have hstable : (prefixWord ++ tailWord_3539812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539812).length < 2 ^ (prefixWord ++ tailWord_3539812).sum := by decide
  have hdescent : baseEnd_3539812 < baseStart_3539812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539829 : List Nat := [1, 3, 4, 1, 1, 2, 1, 5, 1, 4]
def baseStart_3539829 : Nat := 118140960795 + 3539829 * 2 ^ 59
def prefixEnd_3539829 : Nat := 4983230072969 + 3 ^ 40 * 3539829 * 2
def baseEnd_3539829 : Nat := 605877903908112045486043

theorem tailTrace_3539829 : CollatzResearch.WordTrace tailWord_3539829 prefixEnd_3539829 605877903908112045486043 := by
  unfold tailWord_3539829
  simp only [CollatzResearch.WordTrace]
  refine ⟨129108170292811562507254541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86072113528541041671503027 129108170292811562507254541)
  ·
    refine ⟨48415563859804335940220453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129108170292811562507254541 48415563859804335940220453)
    ·
      refine ⟨9077918223713312988791335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48415563859804335940220453 9077918223713312988791335)
      ·
        refine ⟨13616877335569969483187003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9077918223713312988791335 13616877335569969483187003)
        ·
          refine ⟨20425316003354954224780505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13616877335569969483187003 20425316003354954224780505)
          ·
            refine ⟨15318987002516215668585379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20425316003354954224780505 15318987002516215668585379)
            ·
              refine ⟨22978480503774323502878069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15318987002516215668585379 22978480503774323502878069)
              ·
                refine ⟨2154232547228842828394819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22978480503774323502878069 2154232547228842828394819)
                ·
                  refine ⟨3231348820843264242592229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2154232547228842828394819 3231348820843264242592229)
                  ·
                    refine ⟨605877903908112045486043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3231348820843264242592229 605877903908112045486043)
                    ·
                      rfl

theorem cell23_3539829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_3539829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539829 prefixEnd_3539829 := by exact prefixLift 3539829
  have htrace : WordTrace (prefixWord ++ tailWord_3539829) baseStart_3539829 baseEnd_3539829 := by
    simpa [prefixWord, tailWord_3539829, baseEnd_3539829] using wordTrace_append hprefix tailTrace_3539829
  have hstable : (prefixWord ++ tailWord_3539829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539829).length < 2 ^ (prefixWord ++ tailWord_3539829).sum := by decide
  have hdescent : baseEnd_3539829 < baseStart_3539829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539852 : List Nat := [2, 2, 1, 2, 1, 2, 3, 3, 3, 1, 3]
def baseStart_3539852 : Nat := 118140960795 + 3539852 * 2 ^ 59
def prefixEnd_3539852 : Nat := 4983230072969 + 3 ^ 40 * 3539852 * 2
def baseEnd_3539852 : Nat := 1817645521779389546470523

theorem tailTrace_3539852 : CollatzResearch.WordTrace tailWord_3539852 prefixEnd_3539852 1817645521779389546470523 := by
  unfold tailWord_3539852
  simp only [CollatzResearch.WordTrace]
  refine ⟨64554504585864118717670905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86072672781152158290227873 64554504585864118717670905)
  ·
    refine ⟨48415878439398089038253179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64554504585864118717670905 48415878439398089038253179)
    ·
      refine ⟨72623817659097133557379769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48415878439398089038253179 72623817659097133557379769)
      ·
        refine ⟨54467863244322850168034827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72623817659097133557379769 54467863244322850168034827)
        ·
          refine ⟨81701794866484275252052241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54467863244322850168034827 81701794866484275252052241)
          ·
            refine ⟨61276346149863206439039181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81701794866484275252052241 61276346149863206439039181)
            ·
              refine ⟨22978629806198702414639693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61276346149863206439039181 22978629806198702414639693)
              ·
                refine ⟨8616986177324513405489885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22978629806198702414639693 8616986177324513405489885)
                ·
                  refine ⟨3231369816496692527058707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8616986177324513405489885 3231369816496692527058707)
                  ·
                    refine ⟨4847054724745038790588061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3231369816496692527058707 4847054724745038790588061)
                    ·
                      refine ⟨1817645521779389546470523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4847054724745038790588061 1817645521779389546470523)
                      ·
                        rfl

theorem cell23_3539852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_3539852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539852 prefixEnd_3539852 := by exact prefixLift 3539852
  have htrace : WordTrace (prefixWord ++ tailWord_3539852) baseStart_3539852 baseEnd_3539852 := by
    simpa [prefixWord, tailWord_3539852, baseEnd_3539852] using wordTrace_append hprefix tailTrace_3539852
  have hstable : (prefixWord ++ tailWord_3539852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539852).length < 2 ^ (prefixWord ++ tailWord_3539852).sum := by decide
  have hdescent : baseEnd_3539852 < baseStart_3539852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539875 : List Nat := [1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 4]
def baseStart_3539875 : Nat := 118140960795 + 3539875 * 2 ^ 59
def prefixEnd_3539875 : Nat := 4983230072969 + 3 ^ 40 * 3539875 * 2
def baseEnd_3539875 : Nat := 1817657331834442956482917

theorem tailTrace_3539875 : CollatzResearch.WordTrace tailWord_3539875 prefixEnd_3539875 1817657331834442956482917 := by
  unfold tailWord_3539875
  simp only [CollatzResearch.WordTrace]
  refine ⟨129109848050644912363429079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86073232033763274908952719 129109848050644912363429079)
  ·
    refine ⟨193664772075967368545143619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129109848050644912363429079 193664772075967368545143619)
    ·
      refine ⟨290497158113951052817715429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193664772075967368545143619 290497158113951052817715429)
      ·
        refine ⟨54468217146365822403321643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 290497158113951052817715429 54468217146365822403321643)
        ·
          refine ⟨81702325719548733604982465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54468217146365822403321643 81702325719548733604982465)
          ·
            refine ⟨61276744289661550203736849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81702325719548733604982465 61276744289661550203736849)
            ·
              refine ⟨45957558217246162652802637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61276744289661550203736849 45957558217246162652802637)
              ·
                refine ⟨17234084331467310994800989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45957558217246162652802637 17234084331467310994800989)
                ·
                  refine ⟨6462781624300241623050371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17234084331467310994800989 6462781624300241623050371)
                  ·
                    refine ⟨9694172436450362434575557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6462781624300241623050371 9694172436450362434575557)
                    ·
                      refine ⟨1817657331834442956482917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9694172436450362434575557 1817657331834442956482917)
                      ·
                        rfl

theorem cell23_3539875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_3539875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539875 prefixEnd_3539875 := by exact prefixLift 3539875
  have htrace : WordTrace (prefixWord ++ tailWord_3539875) baseStart_3539875 baseEnd_3539875 := by
    simpa [prefixWord, tailWord_3539875, baseEnd_3539875] using wordTrace_append hprefix tailTrace_3539875
  have hstable : (prefixWord ++ tailWord_3539875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539875).length < 2 ^ (prefixWord ++ tailWord_3539875).sum := by decide
  have hdescent : baseEnd_3539875 < baseStart_3539875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539895 : List Nat := [1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 5]
def baseStart_3539895 : Nat := 118140960795 + 3539895 * 2 ^ 59
def prefixEnd_3539895 : Nat := 4983230072969 + 3 ^ 40 * 3539895 * 2
def baseEnd_3539895 : Nat := 1817667601447532878232825

theorem tailTrace_3539895 : CollatzResearch.WordTrace tailWord_3539895 prefixEnd_3539895 1817667601447532878232825 := by
  unfold tailWord_3539895
  simp only [CollatzResearch.WordTrace]
  refine ⟨129110577510572455779157139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86073718340381637186104759 129110577510572455779157139)
  ·
    refine ⟨193665866265858683668735709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129110577510572455779157139 193665866265858683668735709)
    ·
      refine ⟨72624699849697006375775891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193665866265858683668735709 72624699849697006375775891)
      ·
        refine ⟨108937049774545509563663837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72624699849697006375775891 108937049774545509563663837)
        ·
          refine ⟨40851393665454566086373939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108937049774545509563663837 40851393665454566086373939)
          ·
            refine ⟨61277090498181849129560909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40851393665454566086373939 61277090498181849129560909)
            ·
              refine ⟨22978908936818193423585341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61277090498181849129560909 22978908936818193423585341)
              ·
                refine ⟨8617090851306822533844503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22978908936818193423585341 8617090851306822533844503)
                ·
                  refine ⟨12925636276960233800766755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8617090851306822533844503 12925636276960233800766755)
                  ·
                    refine ⟨19388454415440350701150133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12925636276960233800766755 19388454415440350701150133)
                    ·
                      refine ⟨1817667601447532878232825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19388454415440350701150133 1817667601447532878232825)
                      ·
                        rfl

theorem cell23_3539895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_3539895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539895 prefixEnd_3539895 := by exact prefixLift 3539895
  have htrace : WordTrace (prefixWord ++ tailWord_3539895) baseStart_3539895 baseEnd_3539895 := by
    simpa [prefixWord, tailWord_3539895, baseEnd_3539895] using wordTrace_append hprefix tailTrace_3539895
  have hstable : (prefixWord ++ tailWord_3539895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539895).length < 2 ^ (prefixWord ++ tailWord_3539895).sum := by decide
  have hdescent : baseEnd_3539895 < baseStart_3539895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539902 : List Nat := [4, 2, 1, 1, 1, 2, 1, 3, 4, 4]
def baseStart_3539902 : Nat := 118140960795 + 3539902 * 2 ^ 59
def prefixEnd_3539902 : Nat := 4983230072969 + 3 ^ 40 * 3539902 * 2
def baseEnd_3539902 : Nat := 605890398604038116948431

theorem tailTrace_3539902 : CollatzResearch.WordTrace tailWord_3539902 prefixEnd_3539902 605890398604038116948431 := by
  unfold tailWord_3539902
  simp only [CollatzResearch.WordTrace]
  refine ⟨16138854102693386996832745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86073888547698063983107973 16138854102693386996832745)
  ·
    refine ⟨12104140577020040247624559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16138854102693386996832745 12104140577020040247624559)
    ·
      refine ⟨18156210865530060371436839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12104140577020040247624559 18156210865530060371436839)
      ·
        refine ⟨27234316298295090557155259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18156210865530060371436839 27234316298295090557155259)
        ·
          refine ⟨40851474447442635835732889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27234316298295090557155259 40851474447442635835732889)
          ·
            refine ⟨30638605835581976876799667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40851474447442635835732889 30638605835581976876799667)
            ·
              refine ⟨45957908753372965315199501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30638605835581976876799667 45957908753372965315199501)
              ·
                refine ⟨17234215782514861993199813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45957908753372965315199501 17234215782514861993199813)
                ·
                  refine ⟨3231415459221536623724965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17234215782514861993199813 3231415459221536623724965)
                  ·
                    refine ⟨605890398604038116948431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3231415459221536623724965 605890398604038116948431)
                    ·
                      rfl

theorem cell23_3539902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_3539902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539902 prefixEnd_3539902 := by exact prefixLift 3539902
  have htrace : WordTrace (prefixWord ++ tailWord_3539902) baseStart_3539902 baseEnd_3539902 := by
    simpa [prefixWord, tailWord_3539902, baseEnd_3539902] using wordTrace_append hprefix tailTrace_3539902
  have hstable : (prefixWord ++ tailWord_3539902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539902).length < 2 ^ (prefixWord ++ tailWord_3539902).sum := by decide
  have hdescent : baseEnd_3539902 < baseStart_3539902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539915 : List Nat := [1, 1, 1, 1, 3, 6, 2, 8]
def baseStart_3539915 : Nat := 118140960795 + 3539915 * 2 ^ 59
def prefixEnd_3539915 : Nat := 4983230072969 + 3 ^ 40 * 3539915 * 2
def baseEnd_3539915 : Nat := 67321402631874918517879

theorem tailTrace_3539915 : CollatzResearch.WordTrace tailWord_3539915 prefixEnd_3539915 67321402631874918517879 := by
  unfold tailWord_3539915
  simp only [CollatzResearch.WordTrace]
  refine ⟨129111306970499999194885199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86074204646999999463256799 129111306970499999194885199)
  ·
    refine ⟨193666960455749998792327799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129111306970499999194885199 193666960455749998792327799)
    ·
      refine ⟨290500440683624998188491699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193666960455749998792327799 290500440683624998188491699)
      ·
        refine ⟨435750661025437497282737549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290500440683624998188491699 435750661025437497282737549)
        ·
          refine ⟨163406497884539061481026581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 435750661025437497282737549 163406497884539061481026581)
          ·
            refine ⟨7659679588337768506923121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 163406497884539061481026581 7659679588337768506923121)
            ·
              refine ⟨5744759691253326380192341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7659679588337768506923121 5744759691253326380192341)
              ·
                refine ⟨67321402631874918517879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5744759691253326380192341 67321402631874918517879)
                ·
                  rfl

theorem cell23_3539915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 8].length) (baseStart_3539915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539915 prefixEnd_3539915 := by exact prefixLift 3539915
  have htrace : WordTrace (prefixWord ++ tailWord_3539915) baseStart_3539915 baseEnd_3539915 := by
    simpa [prefixWord, tailWord_3539915, baseEnd_3539915] using wordTrace_append hprefix tailTrace_3539915
  have hstable : (prefixWord ++ tailWord_3539915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539915).length < 2 ^ (prefixWord ++ tailWord_3539915).sum := by decide
  have hdescent : baseEnd_3539915 < baseStart_3539915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539919 : List Nat := [1, 1, 2, 1, 1, 6, 4, 1, 2, 4]
def baseStart_3539919 : Nat := 118140960795 + 3539919 * 2 ^ 59
def prefixEnd_3539919 : Nat := 4983230072969 + 3 ^ 40 * 3539919 * 2
def baseEnd_3539919 : Nat := 605893308327746928110905

theorem tailTrace_3539919 : CollatzResearch.WordTrace tailWord_3539919 prefixEnd_3539919 605893308327746928110905 := by
  unfold tailWord_3539919
  simp only [CollatzResearch.WordTrace]
  refine ⟨129111452862485507878030811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86074301908323671918687207 129111452862485507878030811)
  ·
    refine ⟨193667179293728261817046217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129111452862485507878030811 193667179293728261817046217)
    ·
      refine ⟨145250384470296196362784663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193667179293728261817046217 145250384470296196362784663)
      ·
        refine ⟨217875576705444294544176995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145250384470296196362784663 217875576705444294544176995)
        ·
          refine ⟨326813365058166441816265493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217875576705444294544176995 326813365058166441816265493)
          ·
            refine ⟨15319376487101551960137445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 326813365058166441816265493 15319376487101551960137445)
            ·
              refine ⟨2872383091331540992525771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15319376487101551960137445 2872383091331540992525771)
              ·
                refine ⟨4308574636997311488788657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2872383091331540992525771 4308574636997311488788657)
                ·
                  refine ⟨3231430977747983616591493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4308574636997311488788657 3231430977747983616591493)
                  ·
                    refine ⟨605893308327746928110905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3231430977747983616591493 605893308327746928110905)
                    ·
                      rfl

theorem cell23_3539919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 2, 4].length) (baseStart_3539919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539919 prefixEnd_3539919 := by exact prefixLift 3539919
  have htrace : WordTrace (prefixWord ++ tailWord_3539919) baseStart_3539919 baseEnd_3539919 := by
    simpa [prefixWord, tailWord_3539919, baseEnd_3539919] using wordTrace_append hprefix tailTrace_3539919
  have hstable : (prefixWord ++ tailWord_3539919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539919).length < 2 ^ (prefixWord ++ tailWord_3539919).sum := by decide
  have hdescent : baseEnd_3539919 < baseStart_3539919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539922 : List Nat := [3, 2, 2, 3, 1, 1, 2, 1, 1, 1, 6]
def baseStart_3539922 : Nat := 118140960795 + 3539922 * 2 ^ 59
def prefixEnd_3539922 : Nat := 4983230072969 + 3 ^ 40 * 3539922 * 2
def baseEnd_3539922 : Nat := 1817681465425204272595201

theorem tailTrace_3539922 : CollatzResearch.WordTrace tailWord_3539922 prefixEnd_3539922 1817681465425204272595201 := by
  unfold tailWord_3539922
  simp only [CollatzResearch.WordTrace]
  refine ⟨32277890570368659847597505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86074374854316426260260013 32277890570368659847597505)
  ·
    refine ⟨24208417927776494885698129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32277890570368659847597505 24208417927776494885698129)
    ·
      refine ⟨18156313445832371164273597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24208417927776494885698129 18156313445832371164273597)
      ·
        refine ⟨6808617542187139186602599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18156313445832371164273597 6808617542187139186602599)
        ·
          refine ⟨10212926313280708779903899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6808617542187139186602599 10212926313280708779903899)
          ·
            refine ⟨15319389469921063169855849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10212926313280708779903899 15319389469921063169855849)
            ·
              refine ⟨11489542102440797377391887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15319389469921063169855849 11489542102440797377391887)
              ·
                refine ⟨17234313153661196066087831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11489542102440797377391887 17234313153661196066087831)
                ·
                  refine ⟨25851469730491794099131747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17234313153661196066087831 25851469730491794099131747)
                  ·
                    refine ⟨38777204595737691148697621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25851469730491794099131747 38777204595737691148697621)
                    ·
                      refine ⟨1817681465425204272595201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38777204595737691148697621 1817681465425204272595201)
                      ·
                        rfl

theorem cell23_3539922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_3539922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539922 prefixEnd_3539922 := by exact prefixLift 3539922
  have htrace : WordTrace (prefixWord ++ tailWord_3539922) baseStart_3539922 baseEnd_3539922 := by
    simpa [prefixWord, tailWord_3539922, baseEnd_3539922] using wordTrace_append hprefix tailTrace_3539922
  have hstable : (prefixWord ++ tailWord_3539922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539922).length < 2 ^ (prefixWord ++ tailWord_3539922).sum := by decide
  have hdescent : baseEnd_3539922 < baseStart_3539922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539926 : List Nat := [5, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4]
def baseStart_3539926 : Nat := 118140960795 + 3539926 * 2 ^ 59
def prefixEnd_3539926 : Nat := 4983230072969 + 3 ^ 40 * 3539926 * 2
def baseEnd_3539926 : Nat := 1817683519347822256945183

theorem tailTrace_3539926 : CollatzResearch.WordTrace tailWord_3539926 prefixEnd_3539926 1817683519347822256945183 := by
  unfold tailWord_3539926
  simp only [CollatzResearch.WordTrace]
  refine ⟨8069481760841259254595977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86074472115640098715690421 8069481760841259254595977)
  ·
    refine ⟨6052111320630944440946983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8069481760841259254595977 6052111320630944440946983)
    ·
      refine ⟨9078166980946416661420475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6052111320630944440946983 9078166980946416661420475)
      ·
        refine ⟨13617250471419624992130713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9078166980946416661420475 13617250471419624992130713)
        ·
          refine ⟨10212937853564718744098035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13617250471419624992130713 10212937853564718744098035)
          ·
            refine ⟨15319406780347078116147053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10212937853564718744098035 15319406780347078116147053)
            ·
              refine ⟨5744777542630154293555145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15319406780347078116147053 5744777542630154293555145)
              ·
                refine ⟨4308583156972615720166359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5744777542630154293555145 4308583156972615720166359)
                ·
                  refine ⟨6462874735458923580249539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4308583156972615720166359 6462874735458923580249539)
                  ·
                    refine ⟨9694312103188385370374309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6462874735458923580249539 9694312103188385370374309)
                    ·
                      refine ⟨1817683519347822256945183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9694312103188385370374309 1817683519347822256945183)
                      ·
                        rfl

theorem cell23_3539926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_3539926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539926 prefixEnd_3539926 := by exact prefixLift 3539926
  have htrace : WordTrace (prefixWord ++ tailWord_3539926) baseStart_3539926 baseEnd_3539926 := by
    simpa [prefixWord, tailWord_3539926, baseEnd_3539926] using wordTrace_append hprefix tailTrace_3539926
  have hstable : (prefixWord ++ tailWord_3539926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539926).length < 2 ^ (prefixWord ++ tailWord_3539926).sum := by decide
  have hdescent : baseEnd_3539926 < baseStart_3539926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539929 : List Nat := [1, 2, 1, 2, 5, 1, 3, 2, 1, 2, 3]
def baseStart_3539929 : Nat := 118140960795 + 3539929 * 2 ^ 59
def prefixEnd_3539929 : Nat := 4983230072969 + 3 ^ 40 * 3539929 * 2
def baseEnd_3539929 : Nat := 1817685059789785745207669

theorem tailTrace_3539929 : CollatzResearch.WordTrace tailWord_3539929 prefixEnd_3539929 1817685059789785745207669 := by
  unfold tailWord_3539929
  simp only [CollatzResearch.WordTrace]
  refine ⟨129111817592449279585894841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86074545061632853057263227 129111817592449279585894841)
  ·
    refine ⟨96833863194336959689421131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129111817592449279585894841 96833863194336959689421131)
    ·
      refine ⟨145250794791505439534131697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96833863194336959689421131 145250794791505439534131697)
      ·
        refine ⟨108938096093629079650598773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145250794791505439534131697 108938096093629079650598773)
        ·
          refine ⟨10212946508777726217243635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108938096093629079650598773 10212946508777726217243635)
          ·
            refine ⟨15319419763166589325865453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10212946508777726217243635 15319419763166589325865453)
            ·
              refine ⟨5744782411187470997199545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15319419763166589325865453 5744782411187470997199545)
              ·
                refine ⟨4308586808390603247899659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5744782411187470997199545 4308586808390603247899659)
                ·
                  refine ⟨6462880212585904871849489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4308586808390603247899659 6462880212585904871849489)
                  ·
                    refine ⟨4847160159439428653887117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6462880212585904871849489 4847160159439428653887117)
                    ·
                      refine ⟨1817685059789785745207669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4847160159439428653887117 1817685059789785745207669)
                      ·
                        rfl

theorem cell23_3539929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 2, 3].length) (baseStart_3539929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539929 prefixEnd_3539929 := by exact prefixLift 3539929
  have htrace : WordTrace (prefixWord ++ tailWord_3539929) baseStart_3539929 baseEnd_3539929 := by
    simpa [prefixWord, tailWord_3539929, baseEnd_3539929] using wordTrace_append hprefix tailTrace_3539929
  have hstable : (prefixWord ++ tailWord_3539929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539929).length < 2 ^ (prefixWord ++ tailWord_3539929).sum := by decide
  have hdescent : baseEnd_3539929 < baseStart_3539929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539946 : List Nat := [3, 1, 3, 1, 2, 3, 3, 1, 1, 2, 3]
def baseStart_3539946 : Nat := 118140960795 + 3539946 * 2 ^ 59
def prefixEnd_3539946 : Nat := 4983230072969 + 3 ^ 40 * 3539946 * 2
def baseEnd_3539946 : Nat := 1817693788960912178695091

theorem tailTrace_3539946 : CollatzResearch.WordTrace tailWord_3539946 prefixEnd_3539946 1817693788960912178695091 := by
  unfold tailWord_3539946
  simp only [CollatzResearch.WordTrace]
  refine ⟨32278109408346922872315923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86074958422258460992842461 32278109408346922872315923)
  ·
    refine ⟨48417164112520384308473885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32278109408346922872315923 48417164112520384308473885)
    ·
      refine ⟨18156436542195144115677707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48417164112520384308473885 18156436542195144115677707)
      ·
        refine ⟨27234654813292716173516561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18156436542195144115677707 27234654813292716173516561)
        ·
          refine ⟨20425991109969537130137421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27234654813292716173516561 20425991109969537130137421)
          ·
            refine ⟨7659746666238576423801533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20425991109969537130137421 7659746666238576423801533)
            ·
              refine ⟨2872404999839466158925575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7659746666238576423801533 2872404999839466158925575)
              ·
                refine ⟨4308607499759199238388363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2872404999839466158925575 4308607499759199238388363)
                ·
                  refine ⟨6462911249638798857582545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4308607499759199238388363 6462911249638798857582545)
                  ·
                    refine ⟨4847183437229099143186909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6462911249638798857582545 4847183437229099143186909)
                    ·
                      refine ⟨1817693788960912178695091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4847183437229099143186909 1817693788960912178695091)
                      ·
                        rfl

theorem cell23_3539946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_3539946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539946 prefixEnd_3539946 := by exact prefixLift 3539946
  have htrace : WordTrace (prefixWord ++ tailWord_3539946) baseStart_3539946 baseEnd_3539946 := by
    simpa [prefixWord, tailWord_3539946, baseEnd_3539946] using wordTrace_append hprefix tailTrace_3539946
  have hstable : (prefixWord ++ tailWord_3539946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539946).length < 2 ^ (prefixWord ++ tailWord_3539946).sum := by decide
  have hdescent : baseEnd_3539946 < baseStart_3539946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539966 : List Nat := [4, 2, 2, 2, 3, 1, 1, 8]
def baseStart_3539966 : Nat := 118140960795 + 3539966 * 2 ^ 59
def prefixEnd_3539966 : Nat := 4983230072969 + 3 ^ 40 * 3539966 * 2
def baseEnd_3539966 : Nat := 67322372539777855572037

theorem tailTrace_3539966 : CollatzResearch.WordTrace tailWord_3539966 prefixEnd_3539966 67322372539777855572037 := by
  unfold tailWord_3539966
  simp only [CollatzResearch.WordTrace]
  refine ⟨16139145886664404363123969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86075444728876823269994501 16139145886664404363123969)
  ·
    refine ⟨12104359414998303272342977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16139145886664404363123969 12104359414998303272342977)
    ·
      refine ⟨9078269561248727454257233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12104359414998303272342977 9078269561248727454257233)
      ·
        refine ⟨6808702170936545590692925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9078269561248727454257233 6808702170936545590692925)
        ·
          refine ⟨2553263314101204596509847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6808702170936545590692925 2553263314101204596509847)
          ·
            refine ⟨3829894971151806894764771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2553263314101204596509847 3829894971151806894764771)
            ·
              refine ⟨5744842456727710342147157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3829894971151806894764771 5744842456727710342147157)
              ·
                refine ⟨67322372539777855572037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5744842456727710342147157 67322372539777855572037)
                ·
                  rfl

theorem cell23_3539966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 8].length) (baseStart_3539966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539966 prefixEnd_3539966 := by exact prefixLift 3539966
  have htrace : WordTrace (prefixWord ++ tailWord_3539966) baseStart_3539966 baseEnd_3539966 := by
    simpa [prefixWord, tailWord_3539966, baseEnd_3539966] using wordTrace_append hprefix tailTrace_3539966
  have hstable : (prefixWord ++ tailWord_3539966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539966).length < 2 ^ (prefixWord ++ tailWord_3539966).sum := by decide
  have hdescent : baseEnd_3539966 < baseStart_3539966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539969 : List Nat := [1, 2, 4, 1, 2, 2, 1, 2, 3, 3, 2]
def baseStart_3539969 : Nat := 118140960795 + 3539969 * 2 ^ 59
def prefixEnd_3539969 : Nat := 4983230072969 + 3 ^ 40 * 3539969 * 2
def baseEnd_3539969 : Nat := 1817705599015965588707485

theorem tailTrace_3539969 : CollatzResearch.WordTrace tailWord_3539969 prefixEnd_3539969 1817705599015965588707485 := by
  unfold tailWord_3539969
  simp only [CollatzResearch.WordTrace]
  refine ⟨129113276512304366417350961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86075517674869577611567307 129113276512304366417350961)
  ·
    refine ⟨96834957384228274813013221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129113276512304366417350961 96834957384228274813013221)
    ·
      refine ⟨18156554509542801527439979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96834957384228274813013221 18156554509542801527439979)
      ·
        refine ⟨27234831764314202291159969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18156554509542801527439979 27234831764314202291159969)
        ·
          refine ⟨20426123823235651718369977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27234831764314202291159969 20426123823235651718369977)
          ·
            refine ⟨15319592867426738788777483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20426123823235651718369977 15319592867426738788777483)
            ·
              refine ⟨22979389301140108183166225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15319592867426738788777483 22979389301140108183166225)
              ·
                refine ⟨17234541975855081137374669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22979389301140108183166225 17234541975855081137374669)
                ·
                  refine ⟨6462953240945655426515501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17234541975855081137374669 6462953240945655426515501)
                  ·
                    refine ⟨2423607465354620784943313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6462953240945655426515501 2423607465354620784943313)
                    ·
                      refine ⟨1817705599015965588707485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2423607465354620784943313 1817705599015965588707485)
                      ·
                        rfl

theorem cell23_3539969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_3539969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539969 prefixEnd_3539969 := by exact prefixLift 3539969
  have htrace : WordTrace (prefixWord ++ tailWord_3539969) baseStart_3539969 baseEnd_3539969 := by
    simpa [prefixWord, tailWord_3539969, baseEnd_3539969] using wordTrace_append hprefix tailTrace_3539969
  have hstable : (prefixWord ++ tailWord_3539969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539969).length < 2 ^ (prefixWord ++ tailWord_3539969).sum := by decide
  have hdescent : baseEnd_3539969 < baseStart_3539969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539985 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 5]
def baseStart_3539985 : Nat := 118140960795 + 3539985 * 2 ^ 59
def prefixEnd_3539985 : Nat := 4983230072969 + 3 ^ 40 * 3539985 * 2
def baseEnd_3539985 : Nat := 1817713814706437526107411

theorem tailTrace_3539985 : CollatzResearch.WordTrace tailWord_3539985 prefixEnd_3539985 1817713814706437526107411 := by
  unfold tailWord_3539985
  simp only [CollatzResearch.WordTrace]
  refine ⟨129113860080246401149933409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86075906720164267433288939 129113860080246401149933409)
  ·
    refine ⟨96835395060184800862450057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129113860080246401149933409 96835395060184800862450057)
    ·
      refine ⟨72626546295138600646837543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96835395060184800862450057 72626546295138600646837543)
      ·
        refine ⟨108939819442707900970256315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72626546295138600646837543 108939819442707900970256315)
        ·
          refine ⟨163409729164061851455384473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108939819442707900970256315 163409729164061851455384473)
          ·
            refine ⟨122557296873046388591538355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163409729164061851455384473 122557296873046388591538355)
            ·
              refine ⟨183835945309569582887307533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122557296873046388591538355 183835945309569582887307533)
              ·
                refine ⟨68938479491088593582740325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183835945309569582887307533 68938479491088593582740325)
                ·
                  refine ⟨12925964904579111296763811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68938479491088593582740325 12925964904579111296763811)
                  ·
                    refine ⟨19388947356868666945145717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12925964904579111296763811 19388947356868666945145717)
                    ·
                      refine ⟨1817713814706437526107411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19388947356868666945145717 1817713814706437526107411)
                      ·
                        rfl

theorem cell23_3539985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_3539985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539985 prefixEnd_3539985 := by exact prefixLift 3539985
  have htrace : WordTrace (prefixWord ++ tailWord_3539985) baseStart_3539985 baseEnd_3539985 := by
    simpa [prefixWord, tailWord_3539985, baseEnd_3539985] using wordTrace_append hprefix tailTrace_3539985
  have hstable : (prefixWord ++ tailWord_3539985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539985).length < 2 ^ (prefixWord ++ tailWord_3539985).sum := by decide
  have hdescent : baseEnd_3539985 < baseStart_3539985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539999 : List Nat := [1, 1, 2, 4, 1, 3, 2, 2, 1, 4, 2]
def baseStart_3539999 : Nat := 118140960795 + 3539999 * 2 ^ 59
def prefixEnd_3539999 : Nat := 4983230072969 + 3 ^ 40 * 3539999 * 2
def baseEnd_3539999 : Nat := 1817721003435600471332347

theorem tailTrace_3539999 : CollatzResearch.WordTrace tailWord_3539999 prefixEnd_3539999 1817721003435600471332347 := by
  unfold tailWord_3539999
  simp only [CollatzResearch.WordTrace]
  refine ⟨129114370702195681540943051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86076247134797121027295367 129114370702195681540943051)
  ·
    refine ⟨193671556053293522311414577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129114370702195681540943051 193671556053293522311414577)
    ·
      refine ⟨145253667039970141733560933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193671556053293522311414577 145253667039970141733560933)
      ·
        refine ⟨27235062569994401575042675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145253667039970141733560933 27235062569994401575042675)
        ·
          refine ⟨40852593854991602362564013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27235062569994401575042675 40852593854991602362564013)
          ·
            refine ⟨15319722695621850885961505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40852593854991602362564013 15319722695621850885961505)
            ·
              refine ⟨11489792021716388164471129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15319722695621850885961505 11489792021716388164471129)
              ·
                refine ⟨8617344016287291123353347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11489792021716388164471129 8617344016287291123353347)
                ·
                  refine ⟨12926016024430936685030021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8617344016287291123353347 12926016024430936685030021)
                  ·
                    refine ⟨2423628004580800628443129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12926016024430936685030021 2423628004580800628443129)
                    ·
                      refine ⟨1817721003435600471332347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2423628004580800628443129 1817721003435600471332347)
                      ·
                        rfl

theorem cell23_3539999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_3539999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3539999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3539999 prefixEnd_3539999 := by exact prefixLift 3539999
  have htrace : WordTrace (prefixWord ++ tailWord_3539999) baseStart_3539999 baseEnd_3539999 := by
    simpa [prefixWord, tailWord_3539999, baseEnd_3539999] using wordTrace_append hprefix tailTrace_3539999
  have hstable : (prefixWord ++ tailWord_3539999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539999).length < 2 ^ (prefixWord ++ tailWord_3539999).sum := by decide
  have hdescent : baseEnd_3539999 < baseStart_3539999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540003 : List Nat := [1, 1, 1, 4, 3, 4, 2, 1, 1, 3, 2]
def baseStart_3540003 : Nat := 118140960795 + 3540003 * 2 ^ 59
def prefixEnd_3540003 : Nat := 4983230072969 + 3 ^ 40 * 3540003 * 2
def baseEnd_3540003 : Nat := 1817723057358218455682329

theorem tailTrace_3540003 : CollatzResearch.WordTrace tailWord_3540003 prefixEnd_3540003 1817723057358218455682329 := by
  unfold tailWord_3540003
  simp only [CollatzResearch.WordTrace]
  refine ⟨129114516594181190224088663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86076344396120793482725775 129114516594181190224088663)
  ·
    refine ⟨193671774891271785336132995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129114516594181190224088663 193671774891271785336132995)
    ·
      refine ⟨290507662336907678004199493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193671774891271785336132995 290507662336907678004199493)
      ·
        refine ⟨54470186688170189625787405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 290507662336907678004199493 54470186688170189625787405)
        ·
          refine ⟨20426320008063821109670277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54470186688170189625787405 20426320008063821109670277)
          ·
            refine ⟨3829935001511966458063177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20426320008063821109670277 3829935001511966458063177)
            ·
              refine ⟨2872451251133974843547383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3829935001511966458063177 2872451251133974843547383)
              ·
                refine ⟨4308676876700962265321075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2872451251133974843547383 4308676876700962265321075)
                ·
                  refine ⟨6463015315051443397981613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4308676876700962265321075 6463015315051443397981613)
                  ·
                    refine ⟨2423630743144291274243105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6463015315051443397981613 2423630743144291274243105)
                    ·
                      refine ⟨1817723057358218455682329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2423630743144291274243105 1817723057358218455682329)
                      ·
                        rfl

theorem cell23_3540003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 1, 3, 2].length) (baseStart_3540003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540003 prefixEnd_3540003 := by exact prefixLift 3540003
  have htrace : WordTrace (prefixWord ++ tailWord_3540003) baseStart_3540003 baseEnd_3540003 := by
    simpa [prefixWord, tailWord_3540003, baseEnd_3540003] using wordTrace_append hprefix tailTrace_3540003
  have hstable : (prefixWord ++ tailWord_3540003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540003).length < 2 ^ (prefixWord ++ tailWord_3540003).sum := by decide
  have hdescent : baseEnd_3540003 < baseStart_3540003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540005 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 9]
def baseStart_3540005 : Nat := 118140960795 + 3540005 * 2 ^ 59
def prefixEnd_3540005 : Nat := 4983230072969 + 3 ^ 40 * 3540005 * 2
def baseEnd_3540005 : Nat := 201969342702169716428591

theorem tailTrace_3540005 : CollatzResearch.WordTrace tailWord_3540005 prefixEnd_3540005 201969342702169716428591 := by
  unfold tailWord_3540005
  simp only [CollatzResearch.WordTrace]
  refine ⟨129114589540173944565661469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86076393026782629710440979 129114589540173944565661469)
  ·
    refine ⟨48417971077565229212123051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129114589540173944565661469 48417971077565229212123051)
    ·
      refine ⟨72626956616347843818184577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48417971077565229212123051 72626956616347843818184577)
      ·
        refine ⟨54470217462260882863638433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72626956616347843818184577 54470217462260882863638433)
        ·
          refine ⟨40852663096695662147728825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54470217462260882863638433 40852663096695662147728825)
          ·
            refine ⟨30639497322521746610796619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40852663096695662147728825 30639497322521746610796619)
            ·
              refine ⟨45959245983782619916194929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30639497322521746610796619 45959245983782619916194929)
              ·
                refine ⟨34469434487836964937146197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45959245983782619916194929 34469434487836964937146197)
                ·
                  refine ⟨201969342702169716428591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34469434487836964937146197 201969342702169716428591)
                  ·
                    rfl

theorem cell23_3540005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 9].length) (baseStart_3540005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540005 prefixEnd_3540005 := by exact prefixLift 3540005
  have htrace : WordTrace (prefixWord ++ tailWord_3540005) baseStart_3540005 baseEnd_3540005 := by
    simpa [prefixWord, tailWord_3540005, baseEnd_3540005] using wordTrace_append hprefix tailTrace_3540005
  have hstable : (prefixWord ++ tailWord_3540005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540005).length < 2 ^ (prefixWord ++ tailWord_3540005).sum := by decide
  have hdescent : baseEnd_3540005 < baseStart_3540005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540010 : List Nat := [3, 1, 4, 1, 4, 1, 1, 2, 2, 1, 3]
def baseStart_3540010 : Nat := 118140960795 + 3540010 * 2 ^ 59
def prefixEnd_3540010 : Nat := 4983230072969 + 3 ^ 40 * 3540010 * 2
def baseEnd_3540010 : Nat := 1817726651722799928294797

theorem tailTrace_3540010 : CollatzResearch.WordTrace tailWord_3540010 prefixEnd_3540010 1817726651722799928294797 := by
  unfold tailWord_3540010
  simp only [CollatzResearch.WordTrace]
  refine ⟨32278692976288957604898371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86076514603437220279728989 32278692976288957604898371)
  ·
    refine ⟨48418039464433436407347557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32278692976288957604898371 48418039464433436407347557)
    ·
      refine ⟨9078382399581269326377667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48418039464433436407347557 9078382399581269326377667)
      ·
        refine ⟨13617573599371903989566501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9078382399581269326377667 13617573599371903989566501)
        ·
          refine ⟨2553295049882231998043719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13617573599371903989566501 2553295049882231998043719)
          ·
            refine ⟨3829942574823347997065579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2553295049882231998043719 3829942574823347997065579)
            ·
              refine ⟨5744913862235021995598369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3829942574823347997065579 5744913862235021995598369)
              ·
                refine ⟨4308685396676266496698777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5744913862235021995598369 4308685396676266496698777)
                ·
                  refine ⟨3231514047507199872524083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4308685396676266496698777 3231514047507199872524083)
                  ·
                    refine ⟨4847271071260799808786125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3231514047507199872524083 4847271071260799808786125)
                    ·
                      refine ⟨1817726651722799928294797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4847271071260799808786125 1817726651722799928294797)
                      ·
                        rfl

theorem cell23_3540010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_3540010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540010 prefixEnd_3540010 := by exact prefixLift 3540010
  have htrace : WordTrace (prefixWord ++ tailWord_3540010) baseStart_3540010 baseEnd_3540010 := by
    simpa [prefixWord, tailWord_3540010, baseEnd_3540010] using wordTrace_append hprefix tailTrace_3540010
  have hstable : (prefixWord ++ tailWord_3540010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540010).length < 2 ^ (prefixWord ++ tailWord_3540010).sum := by decide
  have hdescent : baseEnd_3540010 < baseStart_3540010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540032 : List Nat := [2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 3]
def baseStart_3540032 : Nat := 118140960795 + 3540032 * 2 ^ 59
def prefixEnd_3540032 : Nat := 4983230072969 + 3 ^ 40 * 3540032 * 2
def baseEnd_3540032 : Nat := 1817737948297198842219695

theorem tailTrace_3540032 : CollatzResearch.WordTrace tailWord_3540032 prefixEnd_3540032 1817737948297198842219695 := by
  unfold tailWord_3540032
  simp only [CollatzResearch.WordTrace]
  refine ⟨64557787155538064088447175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86077049540717418784596233 64557787155538064088447175)
  ·
    refine ⟨96836680733307096132670763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64557787155538064088447175 96836680733307096132670763)
    ·
      refine ⟨145255021099960644199006145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96836680733307096132670763 145255021099960644199006145)
      ·
        refine ⟨108941265824970483149254609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145255021099960644199006145 108941265824970483149254609)
        ·
          refine ⟨81705949368727862361940957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108941265824970483149254609 81705949368727862361940957)
          ·
            refine ⟨30639731013272948385727859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81705949368727862361940957 30639731013272948385727859)
            ·
              refine ⟨45959596519909422578591789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30639731013272948385727859 45959596519909422578591789)
              ·
                refine ⟨17234848694966033466971921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45959596519909422578591789 17234848694966033466971921)
                ·
                  refine ⟨12926136521224525100228941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17234848694966033466971921 12926136521224525100228941)
                  ·
                    refine ⟨4847301195459196912585853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12926136521224525100228941 4847301195459196912585853)
                    ·
                      refine ⟨1817737948297198842219695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4847301195459196912585853 1817737948297198842219695)
                      ·
                        rfl

theorem cell23_3540032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 3].length) (baseStart_3540032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540032 prefixEnd_3540032 := by exact prefixLift 3540032
  have htrace : WordTrace (prefixWord ++ tailWord_3540032) baseStart_3540032 baseEnd_3540032 := by
    simpa [prefixWord, tailWord_3540032, baseEnd_3540032] using wordTrace_append hprefix tailTrace_3540032
  have hstable : (prefixWord ++ tailWord_3540032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540032).length < 2 ^ (prefixWord ++ tailWord_3540032).sum := by decide
  have hdescent : baseEnd_3540032 < baseStart_3540032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540033 : List Nat := [1, 2, 5, 1, 3, 2, 1, 1, 1, 4, 2]
def baseStart_3540033 : Nat := 118140960795 + 3540033 * 2 ^ 59
def prefixEnd_3540033 : Nat := 4983230072969 + 3 ^ 40 * 3540033 * 2
def baseEnd_3540033 : Nat := 1817738461777853338307191

theorem tailTrace_3540033 : CollatzResearch.WordTrace tailWord_3540033 prefixEnd_3540033 1817738461777853338307191 := by
  unfold tailWord_3540033
  simp only [CollatzResearch.WordTrace]
  refine ⟨129115610784072505347680753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86077073856048336898453835 129115610784072505347680753)
  ·
    refine ⟨96836708088054379010760565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129115610784072505347680753 96836708088054379010760565)
    ·
      refine ⟨9078441383255098032258803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96836708088054379010760565 9078441383255098032258803)
      ·
        refine ⟨13617662074882647048388205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9078441383255098032258803 13617662074882647048388205)
        ·
          refine ⟨5106623278080992643145577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13617662074882647048388205 5106623278080992643145577)
          ·
            refine ⟨3829967458560744482359183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5106623278080992643145577 3829967458560744482359183)
            ·
              refine ⟨5744951187841116723538775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3829967458560744482359183 5744951187841116723538775)
              ·
                refine ⟨8617426781761675085308163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5744951187841116723538775 8617426781761675085308163)
                ·
                  refine ⟨12926140172642512627962245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8617426781761675085308163 12926140172642512627962245)
                  ·
                    refine ⟨2423651282370471117742921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12926140172642512627962245 2423651282370471117742921)
                    ·
                      refine ⟨1817738461777853338307191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2423651282370471117742921 1817738461777853338307191)
                      ·
                        rfl

theorem cell23_3540033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_3540033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540033 prefixEnd_3540033 := by exact prefixLift 3540033
  have htrace : WordTrace (prefixWord ++ tailWord_3540033) baseStart_3540033 baseEnd_3540033 := by
    simpa [prefixWord, tailWord_3540033, baseEnd_3540033] using wordTrace_append hprefix tailTrace_3540033
  have hstable : (prefixWord ++ tailWord_3540033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540033).length < 2 ^ (prefixWord ++ tailWord_3540033).sum := by decide
  have hdescent : baseEnd_3540033 < baseStart_3540033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540035 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 3, 7]
def baseStart_3540035 : Nat := 118140960795 + 3540035 * 2 ^ 59
def prefixEnd_3540035 : Nat := 4983230072969 + 3 ^ 40 * 3540035 * 2
def baseEnd_3540035 : Nat := 605913162913054110160727

theorem tailTrace_3540035 : CollatzResearch.WordTrace tailWord_3540035 prefixEnd_3540035 605913162913054110160727 := by
  unfold tailWord_3540035
  simp only [CollatzResearch.WordTrace]
  refine ⟨129115683730065259689253559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86077122486710173126169039 129115683730065259689253559)
  ·
    refine ⟨193673525595097889533880339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129115683730065259689253559 193673525595097889533880339)
    ·
      refine ⟨290510288392646834300820509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193673525595097889533880339 290510288392646834300820509)
      ·
        refine ⟨108941358147242562862807691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290510288392646834300820509 108941358147242562862807691)
        ·
          refine ⟨163412037220863844294211537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108941358147242562862807691 163412037220863844294211537)
          ·
            refine ⟨122559027915647883220658653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163412037220863844294211537 122559027915647883220658653)
            ·
              refine ⟨45959635468367956207746995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122559027915647883220658653 45959635468367956207746995)
              ·
                refine ⟨68939453202551934311620493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45959635468367956207746995 68939453202551934311620493)
                ·
                  refine ⟨25852294950956975366857685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68939453202551934311620493 25852294950956975366857685)
                  ·
                    refine ⟨605913162913054110160727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25852294950956975366857685 605913162913054110160727)
                    ·
                      rfl

theorem cell23_3540035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 7].length) (baseStart_3540035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540035 prefixEnd_3540035 := by exact prefixLift 3540035
  have htrace : WordTrace (prefixWord ++ tailWord_3540035) baseStart_3540035 baseEnd_3540035 := by
    simpa [prefixWord, tailWord_3540035, baseEnd_3540035] using wordTrace_append hprefix tailTrace_3540035
  have hstable : (prefixWord ++ tailWord_3540035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540035).length < 2 ^ (prefixWord ++ tailWord_3540035).sum := by decide
  have hdescent : baseEnd_3540035 < baseStart_3540035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540052 : List Nat := [2, 4, 1, 1, 1, 1, 4, 1, 1, 7]
def baseStart_3540052 : Nat := 118140960795 + 3540052 * 2 ^ 59
def prefixEnd_3540052 : Nat := 4983230072969 + 3 ^ 40 * 3540052 * 2
def baseEnd_3540052 : Nat := 605916072636762921323201

theorem tailTrace_3540052 : CollatzResearch.WordTrace tailWord_3540052 prefixEnd_3540052 605916072636762921323201 := by
  unfold tailWord_3540052
  simp only [CollatzResearch.WordTrace]
  refine ⟨64558151885501835796311205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86077535847335781061748273 64558151885501835796311205)
  ·
    refine ⟨12104653478531594211808351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64558151885501835796311205 12104653478531594211808351)
    ·
      refine ⟨18156980217797391317712527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12104653478531594211808351 18156980217797391317712527)
      ·
        refine ⟨27235470326696086976568791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18156980217797391317712527 27235470326696086976568791)
        ·
          refine ⟨40853205490044130464853187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27235470326696086976568791 40853205490044130464853187)
          ·
            refine ⟨61279808235066195697279781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40853205490044130464853187 61279808235066195697279781)
            ·
              refine ⟨11489964044074911693239959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61279808235066195697279781 11489964044074911693239959)
              ·
                refine ⟨17234946066112367539859939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11489964044074911693239959 17234946066112367539859939)
                ·
                  refine ⟨25852419099168551309789909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17234946066112367539859939 25852419099168551309789909)
                  ·
                    refine ⟨605916072636762921323201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25852419099168551309789909 605916072636762921323201)
                    ·
                      rfl

theorem cell23_3540052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_3540052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540052 prefixEnd_3540052 := by exact prefixLift 3540052
  have htrace : WordTrace (prefixWord ++ tailWord_3540052) baseStart_3540052 baseEnd_3540052 := by
    simpa [prefixWord, tailWord_3540052, baseEnd_3540052] using wordTrace_append hprefix tailTrace_3540052
  have hstable : (prefixWord ++ tailWord_3540052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540052).length < 2 ^ (prefixWord ++ tailWord_3540052).sum := by decide
  have hdescent : baseEnd_3540052 < baseStart_3540052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540129 : List Nat := [1, 2, 3, 3, 1, 1, 4, 2, 6]
def baseStart_3540129 : Nat := 118140960795 + 3540129 * 2 ^ 59
def prefixEnd_3540129 : Nat := 4983230072969 + 3 ^ 40 * 3540129 * 2
def baseEnd_3540129 : Nat := 201976417324520551411861

theorem tailTrace_3540129 : CollatzResearch.WordTrace tailWord_3540129 prefixEnd_3540129 201976417324520551411861 := by
  unfold tailWord_3540129
  simp only [CollatzResearch.WordTrace]
  refine ⟨129119112191724713743175441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86079408127816475828783627 129119112191724713743175441)
  ·
    refine ⟨96839334143793535307381581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129119112191724713743175441 96839334143793535307381581)
    ·
      refine ⟨36314750303922575740268093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96839334143793535307381581 36314750303922575740268093)
      ·
        refine ⟨13618031363970965902600535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36314750303922575740268093 13618031363970965902600535)
        ·
          refine ⟨20427047045956448853900803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13618031363970965902600535 20427047045956448853900803)
          ·
            refine ⟨30640570568934673280851205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20427047045956448853900803 30640570568934673280851205)
            ·
              refine ⟨5745106981675251240159601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30640570568934673280851205 5745106981675251240159601)
              ·
                refine ⟨4308830236256438430119701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5745106981675251240159601 4308830236256438430119701)
                ·
                  refine ⟨201976417324520551411861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4308830236256438430119701 201976417324520551411861)
                  ·
                    rfl

theorem cell23_3540129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 6].length) (baseStart_3540129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540129 prefixEnd_3540129 := by exact prefixLift 3540129
  have htrace : WordTrace (prefixWord ++ tailWord_3540129) baseStart_3540129 baseEnd_3540129 := by
    simpa [prefixWord, tailWord_3540129, baseEnd_3540129] using wordTrace_append hprefix tailTrace_3540129
  have hstable : (prefixWord ++ tailWord_3540129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540129).length < 2 ^ (prefixWord ++ tailWord_3540129).sum := by decide
  have hdescent : baseEnd_3540129 < baseStart_3540129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540133 : List Nat := [1, 3, 1, 2, 1, 4, 4, 2, 1, 4]
def baseStart_3540133 : Nat := 118140960795 + 3540133 * 2 ^ 59
def prefixEnd_3540133 : Nat := 4983230072969 + 3 ^ 40 * 3540133 * 2
def baseEnd_3540133 : Nat := 605929936614434315685577

theorem tailTrace_3540133 : CollatzResearch.WordTrace tailWord_3540133 prefixEnd_3540133 605929936614434315685577 := by
  unfold tailWord_3540133
  simp only [CollatzResearch.WordTrace]
  refine ⟨129119258083710222426321053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86079505389140148284214035 129119258083710222426321053)
  ·
    refine ⟨48419721781391333409870395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129119258083710222426321053 48419721781391333409870395)
    ·
      refine ⟨72629582672087000114805593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48419721781391333409870395 72629582672087000114805593)
      ·
        refine ⟨54472187004065250086104195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72629582672087000114805593 54472187004065250086104195)
        ·
          refine ⟨81708280506097875129156293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54472187004065250086104195 81708280506097875129156293)
          ·
            refine ⟨15320302594893351586716805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81708280506097875129156293 15320302594893351586716805)
            ·
              refine ⟨2872556736542503422509401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15320302594893351586716805 2872556736542503422509401)
              ·
                refine ⟨2154417552406877566882051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2872556736542503422509401 2154417552406877566882051)
                ·
                  refine ⟨3231626328610316350323077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2154417552406877566882051 3231626328610316350323077)
                  ·
                    refine ⟨605929936614434315685577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3231626328610316350323077 605929936614434315685577)
                    ·
                      rfl

theorem cell23_3540133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 2, 1, 4].length) (baseStart_3540133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540133 prefixEnd_3540133 := by exact prefixLift 3540133
  have htrace : WordTrace (prefixWord ++ tailWord_3540133) baseStart_3540133 baseEnd_3540133 := by
    simpa [prefixWord, tailWord_3540133, baseEnd_3540133] using wordTrace_append hprefix tailTrace_3540133
  have hstable : (prefixWord ++ tailWord_3540133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540133).length < 2 ^ (prefixWord ++ tailWord_3540133).sum := by decide
  have hdescent : baseEnd_3540133 < baseStart_3540133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540150 : List Nat := [5, 1, 3, 2, 1, 1, 1, 2, 3, 4]
def baseStart_3540150 : Nat := 118140960795 + 3540150 * 2 ^ 59
def prefixEnd_3540150 : Nat := 4983230072969 + 3 ^ 40 * 3540150 * 2
def baseEnd_3540150 : Nat := 605932846338143126848051

theorem tailTrace_3540150 : CollatzResearch.WordTrace tailWord_3540150 prefixEnd_3540150 605932846338143126848051 := by
  unfold tailWord_3540150
  simp only [CollatzResearch.WordTrace]
  refine ⟨8069992382790539645605619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86079918749765756219793269 8069992382790539645605619)
  ·
    refine ⟨12104988574185809468408429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8069992382790539645605619 12104988574185809468408429)
    ·
      refine ⟨4539370715319678550653161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12104988574185809468408429 4539370715319678550653161)
      ·
        refine ⟨3404528036489758912989871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4539370715319678550653161 3404528036489758912989871)
        ·
          refine ⟨5106792054734638369484807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3404528036489758912989871 5106792054734638369484807)
          ·
            refine ⟨7660188082101957554227211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5106792054734638369484807 7660188082101957554227211)
            ·
              refine ⟨11490282123152936331340817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7660188082101957554227211 11490282123152936331340817)
              ·
                refine ⟨8617711592364702248505613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11490282123152936331340817 8617711592364702248505613)
                ·
                  refine ⟨3231641847136763343189605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8617711592364702248505613 3231641847136763343189605)
                  ·
                    refine ⟨605932846338143126848051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3231641847136763343189605 605932846338143126848051)
                    ·
                      rfl

theorem cell23_3540150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_3540150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540150 prefixEnd_3540150 := by exact prefixLift 3540150
  have htrace : WordTrace (prefixWord ++ tailWord_3540150) baseStart_3540150 baseEnd_3540150 := by
    simpa [prefixWord, tailWord_3540150, baseEnd_3540150] using wordTrace_append hprefix tailTrace_3540150
  have hstable : (prefixWord ++ tailWord_3540150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540150).length < 2 ^ (prefixWord ++ tailWord_3540150).sum := by decide
  have hdescent : baseEnd_3540150 < baseStart_3540150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540156 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 5, 1, 3]
def baseStart_3540156 : Nat := 118140960795 + 3540156 * 2 ^ 59
def prefixEnd_3540156 : Nat := 4983230072969 + 3 ^ 40 * 3540156 * 2
def baseEnd_3540156 : Nat := 1817801619898356357069125

theorem tailTrace_3540156 : CollatzResearch.WordTrace tailWord_3540156 prefixEnd_3540156 1817801619898356357069125 := by
  unfold tailWord_3540156
  simp only [CollatzResearch.WordTrace]
  refine ⟨64560048481313448677204161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86080064641751264902938881 64560048481313448677204161)
  ·
    refine ⟨48420036360985086507903121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64560048481313448677204161 48420036360985086507903121)
    ·
      refine ⟨36315027270738814880927341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48420036360985086507903121 36315027270738814880927341)
      ·
        refine ⟨13618135226527055580347753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36315027270738814880927341 13618135226527055580347753)
        ·
          refine ⟨10213601419895291685260815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13618135226527055580347753 10213601419895291685260815)
          ·
            refine ⟨15320402129842937527891223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10213601419895291685260815 15320402129842937527891223)
            ·
              refine ⟨22980603194764406291836835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15320402129842937527891223 22980603194764406291836835)
              ·
                refine ⟨34470904792146609437755253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22980603194764406291836835 34470904792146609437755253)
                ·
                  refine ⟨3231647324263744634789555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34470904792146609437755253 3231647324263744634789555)
                  ·
                    refine ⟨4847470986395616952184333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3231647324263744634789555 4847470986395616952184333)
                    ·
                      refine ⟨1817801619898356357069125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4847470986395616952184333 1817801619898356357069125)
                      ·
                        rfl

theorem cell23_3540156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_3540156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540156 prefixEnd_3540156 := by exact prefixLift 3540156
  have htrace : WordTrace (prefixWord ++ tailWord_3540156) baseStart_3540156 baseEnd_3540156 := by
    simpa [prefixWord, tailWord_3540156, baseEnd_3540156] using wordTrace_append hprefix tailTrace_3540156
  have hstable : (prefixWord ++ tailWord_3540156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540156).length < 2 ^ (prefixWord ++ tailWord_3540156).sum := by decide
  have hdescent : baseEnd_3540156 < baseStart_3540156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540179 : List Nat := [1, 1, 1, 2, 1, 1, 1, 9, 1, 1, 4]
def baseStart_3540179 : Nat := 118140960795 + 3540179 * 2 ^ 59
def prefixEnd_3540179 : Nat := 4983230072969 + 3 ^ 40 * 3540179 * 2
def baseEnd_3540179 : Nat := 1817813429953409767081519

theorem tailTrace_3540179 : CollatzResearch.WordTrace tailWord_3540179 prefixEnd_3540179 1817813429953409767081519 := by
  unfold tailWord_3540179
  simp only [CollatzResearch.WordTrace]
  refine ⟨129120935841543572282495591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86080623894362381521663727 129120935841543572282495591)
  ·
    refine ⟨193681403762315358423743387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129120935841543572282495591 193681403762315358423743387)
    ·
      refine ⟨290522105643473037635615081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193681403762315358423743387 290522105643473037635615081)
      ·
        refine ⟨217891579232604778226711311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290522105643473037635615081 217891579232604778226711311)
        ·
          refine ⟨326837368848907167340066967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217891579232604778226711311 326837368848907167340066967)
          ·
            refine ⟨490256053273360751010100451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326837368848907167340066967 490256053273360751010100451)
            ·
              refine ⟨735384079910041126515150677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 490256053273360751010100451 735384079910041126515150677)
              ·
                refine ⟨4308891093222897225674711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 735384079910041126515150677 4308891093222897225674711)
                ·
                  refine ⟨6463336639834345838512067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4308891093222897225674711 6463336639834345838512067)
                  ·
                    refine ⟨9695004959751518757768101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6463336639834345838512067 9695004959751518757768101)
                    ·
                      refine ⟨1817813429953409767081519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9695004959751518757768101 1817813429953409767081519)
                      ·
                        rfl

theorem cell23_3540179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 1, 4].length) (baseStart_3540179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540179 prefixEnd_3540179 := by exact prefixLift 3540179
  have htrace : WordTrace (prefixWord ++ tailWord_3540179) baseStart_3540179 baseEnd_3540179 := by
    simpa [prefixWord, tailWord_3540179, baseEnd_3540179] using wordTrace_append hprefix tailTrace_3540179
  have hstable : (prefixWord ++ tailWord_3540179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540179).length < 2 ^ (prefixWord ++ tailWord_3540179).sum := by decide
  have hdescent : baseEnd_3540179 < baseStart_3540179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540180 : List Nat := [2, 4, 1, 4, 2, 1, 1, 2, 6]
def baseStart_3540180 : Nat := 118140960795 + 3540180 * 2 ^ 59
def prefixEnd_3540180 : Nat := 4983230072969 + 3 ^ 40 * 3540180 * 2
def baseEnd_3540180 : Nat := 201979327048229362574335

theorem tailTrace_3540180 : CollatzResearch.WordTrace tailWord_3540180 prefixEnd_3540180 201979327048229362574335 := by
  unfold tailWord_3540180
  simp only [CollatzResearch.WordTrace]
  refine ⟨64560486157269974726640997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86080648209693299635521329 64560486157269974726640997)
  ·
    refine ⟨12105091154488120261245187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64560486157269974726640997 12105091154488120261245187)
    ·
      refine ⟨18157636731732180391867781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12105091154488120261245187 18157636731732180391867781)
      ·
        refine ⟨3404556887199783823475209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18157636731732180391867781 3404556887199783823475209)
        ·
          refine ⟨2553417665399837867606407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3404556887199783823475209 2553417665399837867606407)
          ·
            refine ⟨3830126498099756801409611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2553417665399837867606407 3830126498099756801409611)
            ·
              refine ⟨5745189747149635202114417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3830126498099756801409611 5745189747149635202114417)
              ·
                refine ⟨4308892310362226401585813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5745189747149635202114417 4308892310362226401585813)
                ·
                  refine ⟨201979327048229362574335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4308892310362226401585813 201979327048229362574335)
                  ·
                    rfl

theorem cell23_3540180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_3540180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540180 prefixEnd_3540180 := by exact prefixLift 3540180
  have htrace : WordTrace (prefixWord ++ tailWord_3540180) baseStart_3540180 baseEnd_3540180 := by
    simpa [prefixWord, tailWord_3540180, baseEnd_3540180] using wordTrace_append hprefix tailTrace_3540180
  have hstable : (prefixWord ++ tailWord_3540180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540180).length < 2 ^ (prefixWord ++ tailWord_3540180).sum := by decide
  have hdescent : baseEnd_3540180 < baseStart_3540180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540206 : List Nat := [4, 1, 2, 1, 1, 1, 2, 5, 2, 4]
def baseStart_3540206 : Nat := 118140960795 + 3540206 * 2 ^ 59
def prefixEnd_3540206 : Nat := 4983230072969 + 3 ^ 40 * 3540206 * 2
def baseEnd_3540206 : Nat := 605942431310360387147965

theorem tailTrace_3540206 : CollatzResearch.WordTrace tailWord_3540206 prefixEnd_3540206 605942431310360387147965 := by
  unfold tailWord_3540206
  simp only [CollatzResearch.WordTrace]
  refine ⟨16140240076555719486716059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86081280408297170595818981 16140240076555719486716059)
  ·
    refine ⟨24210360114833579230074089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16140240076555719486716059 24210360114833579230074089)
    ·
      refine ⟨18157770086125184422555567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24210360114833579230074089 18157770086125184422555567)
      ·
        refine ⟨27236655129187776633833351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18157770086125184422555567 27236655129187776633833351)
        ·
          refine ⟨40854982693781664950750027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27236655129187776633833351 40854982693781664950750027)
          ·
            refine ⟨61282474040672497426125041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40854982693781664950750027 61282474040672497426125041)
            ·
              refine ⟨45961855530504373069593781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61282474040672497426125041 45961855530504373069593781)
              ·
                refine ⟨4308923955984784975274417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45961855530504373069593781 4308923955984784975274417)
                ·
                  refine ⟨3231692966988588731455813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4308923955984784975274417 3231692966988588731455813)
                  ·
                    refine ⟨605942431310360387147965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3231692966988588731455813 605942431310360387147965)
                    ·
                      rfl

theorem cell23_3540206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_3540206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540206 prefixEnd_3540206 := by exact prefixLift 3540206
  have htrace : WordTrace (prefixWord ++ tailWord_3540206) baseStart_3540206 baseEnd_3540206 := by
    simpa [prefixWord, tailWord_3540206, baseEnd_3540206] using wordTrace_append hprefix tailTrace_3540206
  have hstable : (prefixWord ++ tailWord_3540206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540206).length < 2 ^ (prefixWord ++ tailWord_3540206).sum := by decide
  have hdescent : baseEnd_3540206 < baseStart_3540206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540229 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 3, 3, 3]
def baseStart_3540229 : Nat := 118140960795 + 3540229 * 2 ^ 59
def prefixEnd_3540229 : Nat := 4983230072969 + 3 ^ 40 * 3540229 * 2
def baseEnd_3540229 : Nat := 1817839103986134571456289

theorem tailTrace_3540229 : CollatzResearch.WordTrace tailWord_3540229 prefixEnd_3540229 1817839103986134571456289 := by
  unfold tailWord_3540229
  simp only [CollatzResearch.WordTrace]
  refine ⟨129122759491362430821815741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86081839660908287214543827 129122759491362430821815741)
  ·
    refine ⟨48421034809260911558180903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129122759491362430821815741 48421034809260911558180903)
    ·
      refine ⟨72631552213891367337271355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48421034809260911558180903 72631552213891367337271355)
      ·
        refine ⟨108947328320837051005907033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72631552213891367337271355 108947328320837051005907033)
        ·
          refine ⟨81710496240627788254430275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108947328320837051005907033 81710496240627788254430275)
          ·
            refine ⟨122565744360941682381645413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81710496240627788254430275 122565744360941682381645413)
            ·
              refine ⟨22981077067676565446558515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122565744360941682381645413 22981077067676565446558515)
              ·
                refine ⟨34471615601514848169837773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22981077067676565446558515 34471615601514848169837773)
                ·
                  refine ⟨12926855850568068063689165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34471615601514848169837773 12926855850568068063689165)
                  ·
                    refine ⟨4847570943963025523883437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12926855850568068063689165 4847570943963025523883437)
                    ·
                      refine ⟨1817839103986134571456289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4847570943963025523883437 1817839103986134571456289)
                      ·
                        rfl

theorem cell23_3540229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 3, 3].length) (baseStart_3540229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540229 prefixEnd_3540229 := by exact prefixLift 3540229
  have htrace : WordTrace (prefixWord ++ tailWord_3540229) baseStart_3540229 baseEnd_3540229 := by
    simpa [prefixWord, tailWord_3540229, baseEnd_3540229] using wordTrace_append hprefix tailTrace_3540229
  have hstable : (prefixWord ++ tailWord_3540229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540229).length < 2 ^ (prefixWord ++ tailWord_3540229).sum := by decide
  have hdescent : baseEnd_3540229 < baseStart_3540229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540247 : List Nat := [1, 1, 3, 4, 1, 1, 5, 2, 1, 2, 2]
def baseStart_3540247 : Nat := 118140960795 + 3540247 * 2 ^ 59
def prefixEnd_3540247 : Nat := 4983230072969 + 3 ^ 40 * 3540247 * 2
def baseEnd_3540247 : Nat := 1817848346637915501031207

theorem tailTrace_3540247 : CollatzResearch.WordTrace tailWord_3540247 prefixEnd_3540247 1817848346637915501031207 := by
  unfold tailWord_3540247
  simp only [CollatzResearch.WordTrace]
  refine ⟨129123416005297219895970995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86082277336864813263980663 129123416005297219895970995)
  ·
    refine ⟨193685124007945829843956493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129123416005297219895970995 193685124007945829843956493)
    ·
      refine ⟨72631921502979686191483685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193685124007945829843956493 72631921502979686191483685)
      ·
        refine ⟨13618485281808691160903191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72631921502979686191483685 13618485281808691160903191)
        ·
          refine ⟨20427727922713036741354787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13618485281808691160903191 20427727922713036741354787)
          ·
            refine ⟨30641591884069555112032181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20427727922713036741354787 30641591884069555112032181)
            ·
              refine ⟨2872649239131520791753017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30641591884069555112032181 2872649239131520791753017)
              ·
                refine ⟨2154486929348640593814763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2872649239131520791753017 2154486929348640593814763)
                ·
                  refine ⟨3231730394022960890722145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2154486929348640593814763 3231730394022960890722145)
                  ·
                    refine ⟨2423797795517220668041609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3231730394022960890722145 2423797795517220668041609)
                    ·
                      refine ⟨1817848346637915501031207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2423797795517220668041609 1817848346637915501031207)
                      ·
                        rfl

theorem cell23_3540247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_3540247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540247 prefixEnd_3540247 := by exact prefixLift 3540247
  have htrace : WordTrace (prefixWord ++ tailWord_3540247) baseStart_3540247 baseEnd_3540247 := by
    simpa [prefixWord, tailWord_3540247, baseEnd_3540247] using wordTrace_append hprefix tailTrace_3540247
  have hstable : (prefixWord ++ tailWord_3540247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540247).length < 2 ^ (prefixWord ++ tailWord_3540247).sum := by decide
  have hdescent : baseEnd_3540247 < baseStart_3540247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540273 : List Nat := [1, 2, 2, 3, 3, 2, 1, 1, 3, 3, 2]
def baseStart_3540273 : Nat := 118140960795 + 3540273 * 2 ^ 59
def prefixEnd_3540273 : Nat := 4983230072969 + 3 ^ 40 * 3540273 * 2
def baseEnd_3540273 : Nat := 1817861697134932399306087

theorem tailTrace_3540273 : CollatzResearch.WordTrace tailWord_3540273 prefixEnd_3540273 1817861697134932399306087 := by
  unfold tailWord_3540273
  simp only [CollatzResearch.WordTrace]
  refine ⟨129124364303203026336417473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86082909535468684224278315 129124364303203026336417473)
  ·
    refine ⟨96843273227402269752313105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129124364303203026336417473 96843273227402269752313105)
    ·
      refine ⟨72632454920551702314234829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96843273227402269752313105 72632454920551702314234829)
      ·
        refine ⟨27237170595206888367838061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72632454920551702314234829 27237170595206888367838061)
        ·
          refine ⟨10213938973202583137939273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27237170595206888367838061 10213938973202583137939273)
          ·
            refine ⟨7660454229901937353454455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10213938973202583137939273 7660454229901937353454455)
            ·
              refine ⟨11490681344852906030181683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7660454229901937353454455 11490681344852906030181683)
              ·
                refine ⟨17236022017279359045272525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11490681344852906030181683 17236022017279359045272525)
                ·
                  refine ⟨6463508256479759641977197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17236022017279359045272525 6463508256479759641977197)
                  ·
                    refine ⟨2423815596179909865741449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6463508256479759641977197 2423815596179909865741449)
                    ·
                      refine ⟨1817861697134932399306087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2423815596179909865741449 1817861697134932399306087)
                      ·
                        rfl

theorem cell23_3540273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_3540273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540273 prefixEnd_3540273 := by exact prefixLift 3540273
  have htrace : WordTrace (prefixWord ++ tailWord_3540273) baseStart_3540273 baseEnd_3540273 := by
    simpa [prefixWord, tailWord_3540273, baseEnd_3540273] using wordTrace_append hprefix tailTrace_3540273
  have hstable : (prefixWord ++ tailWord_3540273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540273).length < 2 ^ (prefixWord ++ tailWord_3540273).sum := by decide
  have hdescent : baseEnd_3540273 < baseStart_3540273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540320 : List Nat := [2, 1, 1, 3, 4, 1, 2, 3, 2, 2, 2]
def baseStart_3540320 : Nat := 118140960795 + 3540320 * 2 ^ 59
def prefixEnd_3540320 : Nat := 4983230072969 + 3 ^ 40 * 3540320 * 2
def baseEnd_3540320 : Nat := 1817885830725693715418371

theorem tailTrace_3540320 : CollatzResearch.WordTrace tailWord_3540320 prefixEnd_3540320 1817885830725693715418371 := by
  unfold tailWord_3540320
  simp only [CollatzResearch.WordTrace]
  refine ⟨64563039267016376681689207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86084052356021835575585609 64563039267016376681689207)
  ·
    refine ⟨96844558900524565022533811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64563039267016376681689207 96844558900524565022533811)
    ·
      refine ⟨145266838350786847533800717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96844558900524565022533811 145266838350786847533800717)
      ·
        refine ⟨54475064381545067825175269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145266838350786847533800717 54475064381545067825175269)
        ·
          refine ⟨10214074571539700217220363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54475064381545067825175269 10214074571539700217220363)
          ·
            refine ⟨15321111857309550325830545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10214074571539700217220363 15321111857309550325830545)
            ·
              refine ⟨11490833892982162744372909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15321111857309550325830545 11490833892982162744372909)
              ·
                refine ⟨4309062709868311029139841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11490833892982162744372909 4309062709868311029139841)
                ·
                  refine ⟨3231797032401233271854881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4309062709868311029139841 3231797032401233271854881)
                  ·
                    refine ⟨2423847774300924953891161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3231797032401233271854881 2423847774300924953891161)
                    ·
                      refine ⟨1817885830725693715418371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2423847774300924953891161 1817885830725693715418371)
                      ·
                        rfl

theorem cell23_3540320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 2, 2, 2].length) (baseStart_3540320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540320 prefixEnd_3540320 := by exact prefixLift 3540320
  have htrace : WordTrace (prefixWord ++ tailWord_3540320) baseStart_3540320 baseEnd_3540320 := by
    simpa [prefixWord, tailWord_3540320, baseEnd_3540320] using wordTrace_append hprefix tailTrace_3540320
  have hstable : (prefixWord ++ tailWord_3540320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540320).length < 2 ^ (prefixWord ++ tailWord_3540320).sum := by decide
  have hdescent : baseEnd_3540320 < baseStart_3540320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540346 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 4, 5, 2]
def baseStart_3540346 : Nat := 118140960795 + 3540346 * 2 ^ 59
def prefixEnd_3540346 : Nat := 4983230072969 + 3 ^ 40 * 3540346 * 2
def baseEnd_3540346 : Nat := 1817899181222710613693251

theorem tailTrace_3540346 : CollatzResearch.WordTrace tailWord_3540346 prefixEnd_3540346 1817899181222710613693251 := by
  unfold tailWord_3540346
  simp only [CollatzResearch.WordTrace]
  refine ⟨32281756707984639950956223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86084684554625706535883261 32281756707984639950956223)
  ·
    refine ⟨48422635061976959926434335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32281756707984639950956223 48422635061976959926434335)
    ·
      refine ⟨72633952592965439889651503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48422635061976959926434335 72633952592965439889651503)
      ·
        refine ⟨108950928889448159834477255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72633952592965439889651503 108950928889448159834477255)
        ·
          refine ⟨163426393334172239751715883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108950928889448159834477255 163426393334172239751715883)
          ·
            refine ⟨245139590001258359627573825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163426393334172239751715883 245139590001258359627573825)
            ·
              refine ⟨183854692500943769720680369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245139590001258359627573825 183854692500943769720680369)
              ·
                refine ⟨137891019375707827290510277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183854692500943769720680369 137891019375707827290510277)
                ·
                  refine ⟨25854566132945217616970677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137891019375707827290510277 25854566132945217616970677)
                  ·
                    refine ⟨2423865574963614151591001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25854566132945217616970677 2423865574963614151591001)
                    ·
                      refine ⟨1817899181222710613693251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2423865574963614151591001 1817899181222710613693251)
                      ·
                        rfl

theorem cell23_3540346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 4, 5, 2].length) (baseStart_3540346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540346 prefixEnd_3540346 := by exact prefixLift 3540346
  have htrace : WordTrace (prefixWord ++ tailWord_3540346) baseStart_3540346 baseEnd_3540346 := by
    simpa [prefixWord, tailWord_3540346, baseEnd_3540346] using wordTrace_append hprefix tailTrace_3540346
  have hstable : (prefixWord ++ tailWord_3540346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540346).length < 2 ^ (prefixWord ++ tailWord_3540346).sum := by decide
  have hdescent : baseEnd_3540346 < baseStart_3540346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540354 : List Nat := [3, 4, 2, 1, 1, 1, 3, 2, 2, 2, 2]
def baseStart_3540354 : Nat := 118140960795 + 3540354 * 2 ^ 59
def prefixEnd_3540354 : Nat := 4983230072969 + 3 ^ 40 * 3540354 * 2
def baseEnd_3540354 : Nat := 1817903289067946582393215

theorem tailTrace_3540354 : CollatzResearch.WordTrace tailWord_3540354 prefixEnd_3540354 1817903289067946582393215 := by
  unfold tailWord_3540354
  simp only [CollatzResearch.WordTrace]
  refine ⟨32281829653977394292529029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86084879077273051446744077 32281829653977394292529029)
  ·
    refine ⟨6052843060120761429849193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32281829653977394292529029 6052843060120761429849193)
    ·
      refine ⟨4539632295090571072386895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6052843060120761429849193 4539632295090571072386895)
      ·
        refine ⟨6809448442635856608580343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4539632295090571072386895 6809448442635856608580343)
        ·
          refine ⟨10214172663953784912870515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6809448442635856608580343 10214172663953784912870515)
          ·
            refine ⟨15321258995930677369305773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10214172663953784912870515 15321258995930677369305773)
            ·
              refine ⟨5745472123474004013489665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15321258995930677369305773 5745472123474004013489665)
              ·
                refine ⟨4309104092605503010117249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5745472123474004013489665 4309104092605503010117249)
                ·
                  refine ⟨3231828069454127257587937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4309104092605503010117249 3231828069454127257587937)
                  ·
                    refine ⟨2423871052090595443190953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3231828069454127257587937 2423871052090595443190953)
                    ·
                      refine ⟨1817903289067946582393215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2423871052090595443190953 1817903289067946582393215)
                      ·
                        rfl

theorem cell23_3540354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_3540354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540354 prefixEnd_3540354 := by exact prefixLift 3540354
  have htrace : WordTrace (prefixWord ++ tailWord_3540354) baseStart_3540354 baseEnd_3540354 := by
    simpa [prefixWord, tailWord_3540354, baseEnd_3540354] using wordTrace_append hprefix tailTrace_3540354
  have hstable : (prefixWord ++ tailWord_3540354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540354).length < 2 ^ (prefixWord ++ tailWord_3540354).sum := by decide
  have hdescent : baseEnd_3540354 < baseStart_3540354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540389 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 1, 3, 6]
def baseStart_3540389 : Nat := 118140960795 + 3540389 * 2 ^ 59
def prefixEnd_3540389 : Nat := 4983230072969 + 3 ^ 40 * 3540389 * 2
def baseEnd_3540389 : Nat := 1817921260890853945455553

theorem tailTrace_3540389 : CollatzResearch.WordTrace tailWord_3540389 prefixEnd_3540389 1817921260890853945455553 := by
  unfold tailWord_3540389
  simp only [CollatzResearch.WordTrace]
  refine ⟨129128595170782778147640221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86085730113855185431760147 129128595170782778147640221)
  ·
    refine ⟨48423223189043541805365083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129128595170782778147640221 48423223189043541805365083)
    ·
      refine ⟨72634834783565312708047625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48423223189043541805365083 72634834783565312708047625)
      ·
        refine ⟨54476126087673984531035719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72634834783565312708047625 54476126087673984531035719)
        ·
          refine ⟨81714189131510976796553579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54476126087673984531035719 81714189131510976796553579)
          ·
            refine ⟨122571283697266465194830369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81714189131510976796553579 122571283697266465194830369)
            ·
              refine ⟨91928462772949848896122777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122571283697266465194830369 91928462772949848896122777)
              ·
                refine ⟨68946347079712386672092083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91928462772949848896122777 68946347079712386672092083)
                ·
                  refine ⟨103419520619568580008138125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68946347079712386672092083 103419520619568580008138125)
                  ·
                    refine ⟨38782320232338217503051797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103419520619568580008138125 38782320232338217503051797)
                    ·
                      refine ⟨1817921260890853945455553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38782320232338217503051797 1817921260890853945455553)
                      ·
                        rfl

theorem cell23_3540389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_3540389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540389 prefixEnd_3540389 := by exact prefixLift 3540389
  have htrace : WordTrace (prefixWord ++ tailWord_3540389) baseStart_3540389 baseEnd_3540389 := by
    simpa [prefixWord, tailWord_3540389, baseEnd_3540389] using wordTrace_append hprefix tailTrace_3540389
  have hstable : (prefixWord ++ tailWord_3540389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540389).length < 2 ^ (prefixWord ++ tailWord_3540389).sum := by decide
  have hdescent : baseEnd_3540389 < baseStart_3540389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540396 : List Nat := [2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 3]
def baseStart_3540396 : Nat := 118140960795 + 3540396 * 2 ^ 59
def prefixEnd_3540396 : Nat := 4983230072969 + 3 ^ 40 * 3540396 * 2
def baseEnd_3540396 : Nat := 1817924855255435418068021

theorem tailTrace_3540396 : CollatzResearch.WordTrace tailWord_3540396 prefixEnd_3540396 1817924855255435418068021 := by
  unfold tailWord_3540396
  simp only [CollatzResearch.WordTrace]
  refine ⟨64564425240878709171572521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86085900321171612228763361 64564425240878709171572521)
  ·
    refine ⟨48423318930659031878679391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64564425240878709171572521 48423318930659031878679391)
    ·
      refine ⟨72634978395988547818019087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48423318930659031878679391 72634978395988547818019087)
      ·
        refine ⟨108952467593982821727028631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72634978395988547818019087 108952467593982821727028631)
        ·
          refine ⟨163428701390974232590542947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108952467593982821727028631 163428701390974232590542947)
          ·
            refine ⟨245143052086461348885814421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163428701390974232590542947 245143052086461348885814421)
            ·
              refine ⟨11491080566552875729022551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 245143052086461348885814421 11491080566552875729022551)
              ·
                refine ⟨17236620849829313593533827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11491080566552875729022551 17236620849829313593533827)
                ·
                  refine ⟨25854931274743970390300741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17236620849829313593533827 25854931274743970390300741)
                  ·
                    refine ⟨4847799614014494448181389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25854931274743970390300741 4847799614014494448181389)
                    ·
                      refine ⟨1817924855255435418068021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4847799614014494448181389 1817924855255435418068021)
                      ·
                        rfl

theorem cell23_3540396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 3].length) (baseStart_3540396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540396 prefixEnd_3540396 := by exact prefixLift 3540396
  have htrace : WordTrace (prefixWord ++ tailWord_3540396) baseStart_3540396 baseEnd_3540396 := by
    simpa [prefixWord, tailWord_3540396, baseEnd_3540396] using wordTrace_append hprefix tailTrace_3540396
  have hstable : (prefixWord ++ tailWord_3540396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540396).length < 2 ^ (prefixWord ++ tailWord_3540396).sum := by decide
  have hdescent : baseEnd_3540396 < baseStart_3540396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540413 : List Nat := [1, 4, 1, 2, 2, 1, 3, 2, 2, 2, 3]
def baseStart_3540413 : Nat := 118140960795 + 3540413 * 2 ^ 59
def prefixEnd_3540413 : Nat := 4983230072969 + 3 ^ 40 * 3540413 * 2
def baseEnd_3540413 : Nat := 1817933584426561851555443

theorem tailTrace_3540413 : CollatzResearch.WordTrace tailWord_3540413 prefixEnd_3540413 1817933584426561851555443 := by
  unfold tailWord_3540413
  simp only [CollatzResearch.WordTrace]
  refine ⟨129129470522695830246513893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86086313681797220164342595 129129470522695830246513893)
  ·
    refine ⟨24211775723005468171221355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129129470522695830246513893 24211775723005468171221355)
    ·
      refine ⟨36317663584508202256832033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24211775723005468171221355 36317663584508202256832033)
      ·
        refine ⟨27238247688381151692624025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36317663584508202256832033 27238247688381151692624025)
        ·
          refine ⟨20428685766285863769468019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27238247688381151692624025 20428685766285863769468019)
          ·
            refine ⟨30643028649428795654202029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20428685766285863769468019 30643028649428795654202029)
            ·
              refine ⟨11491135743535798370325761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30643028649428795654202029 11491135743535798370325761)
              ·
                refine ⟨8618351807651848777744321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11491135743535798370325761 8618351807651848777744321)
                ·
                  refine ⟨6463763855738886583308241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8618351807651848777744321 6463763855738886583308241)
                  ·
                    refine ⟨4847822891804164937481181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6463763855738886583308241 4847822891804164937481181)
                    ·
                      refine ⟨1817933584426561851555443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4847822891804164937481181 1817933584426561851555443)
                      ·
                        rfl

theorem cell23_3540413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_3540413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540413 prefixEnd_3540413 := by exact prefixLift 3540413
  have htrace : WordTrace (prefixWord ++ tailWord_3540413) baseStart_3540413 baseEnd_3540413 := by
    simpa [prefixWord, tailWord_3540413, baseEnd_3540413] using wordTrace_append hprefix tailTrace_3540413
  have hstable : (prefixWord ++ tailWord_3540413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540413).length < 2 ^ (prefixWord ++ tailWord_3540413).sum := by decide
  have hdescent : baseEnd_3540413 < baseStart_3540413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540419 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 8]
def baseStart_3540419 : Nat := 118140960795 + 3540419 * 2 ^ 59
def prefixEnd_3540419 : Nat := 4983230072969 + 3 ^ 40 * 3540419 * 2
def baseEnd_3540419 : Nat := 1817936665310488828080415

theorem tailTrace_3540419 : CollatzResearch.WordTrace tailWord_3540419 prefixEnd_3540419 1817936665310488828080415 := by
  unfold tailWord_3540419
  simp only [CollatzResearch.WordTrace]
  refine ⟨129129689360674093271232311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86086459573782728847488207 129129689360674093271232311)
  ·
    refine ⟨193694534041011139906848467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129129689360674093271232311 193694534041011139906848467)
    ·
      refine ⟨290541801061516709860272701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193694534041011139906848467 290541801061516709860272701)
      ·
        refine ⟨108953175398068766197602263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290541801061516709860272701 108953175398068766197602263)
        ·
          refine ⟨163429763097103149296403395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108953175398068766197602263 163429763097103149296403395)
          ·
            refine ⟨245144644645654723944605093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163429763097103149296403395 245144644645654723944605093)
            ·
              refine ⟨45964620871060260739613455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 245144644645654723944605093 45964620871060260739613455)
              ·
                refine ⟨68946931306590391109420183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45964620871060260739613455 68946931306590391109420183)
                ·
                  refine ⟨103420396959885586664130275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68946931306590391109420183 103420396959885586664130275)
                  ·
                    refine ⟨155130595439828379996195413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103420396959885586664130275 155130595439828379996195413)
                    ·
                      refine ⟨1817936665310488828080415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 155130595439828379996195413 1817936665310488828080415)
                      ·
                        rfl

theorem cell23_3540419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_3540419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540419 prefixEnd_3540419 := by exact prefixLift 3540419
  have htrace : WordTrace (prefixWord ++ tailWord_3540419) baseStart_3540419 baseEnd_3540419 := by
    simpa [prefixWord, tailWord_3540419, baseEnd_3540419] using wordTrace_append hprefix tailTrace_3540419
  have hstable : (prefixWord ++ tailWord_3540419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540419).length < 2 ^ (prefixWord ++ tailWord_3540419).sum := by decide
  have hdescent : baseEnd_3540419 < baseStart_3540419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540420 : List Nat := [2, 3, 3, 2, 1, 1, 3, 1, 3, 4]
def baseStart_3540420 : Nat := 118140960795 + 3540420 * 2 ^ 59
def prefixEnd_3540420 : Nat := 4983230072969 + 3 ^ 40 * 3540420 * 2
def baseEnd_3540420 : Nat := 605979059597047774722637

theorem tailTrace_3540420 : CollatzResearch.WordTrace tailWord_3540420 prefixEnd_3540420 605979059597047774722637 := by
  unfold tailWord_3540420
  simp only [CollatzResearch.WordTrace]
  refine ⟨64564862916835235221009357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86086483889113646961345809 64564862916835235221009357)
  ·
    refine ⟨24211823593813213207878509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64564862916835235221009357 24211823593813213207878509)
    ·
      refine ⟨9079433847679954952954441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24211823593813213207878509 9079433847679954952954441)
      ·
        refine ⟨6809575385759966214715831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9079433847679954952954441 6809575385759966214715831)
        ·
          refine ⟨10214363078639949322073747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6809575385759966214715831 10214363078639949322073747)
          ·
            refine ⟨15321544617959923983110621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10214363078639949322073747 15321544617959923983110621)
            ·
              refine ⟨5745579231734971493666483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15321544617959923983110621 5745579231734971493666483)
              ·
                refine ⟨8618368847602457240499725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5745579231734971493666483 8618368847602457240499725)
                ·
                  refine ⟨3231888317850921465187397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8618368847602457240499725 3231888317850921465187397)
                  ·
                    refine ⟨605979059597047774722637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3231888317850921465187397 605979059597047774722637)
                    ·
                      rfl

theorem cell23_3540420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_3540420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540420 prefixEnd_3540420 := by exact prefixLift 3540420
  have htrace : WordTrace (prefixWord ++ tailWord_3540420) baseStart_3540420 baseEnd_3540420 := by
    simpa [prefixWord, tailWord_3540420, baseEnd_3540420] using wordTrace_append hprefix tailTrace_3540420
  have hstable : (prefixWord ++ tailWord_3540420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540420).length < 2 ^ (prefixWord ++ tailWord_3540420).sum := by decide
  have hdescent : baseEnd_3540420 < baseStart_3540420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540477 : List Nat := [1, 4, 1, 1, 1, 5, 1, 4, 1, 1, 3]
def baseStart_3540477 : Nat := 118140960795 + 3540477 * 2 ^ 59
def prefixEnd_3540477 : Nat := 4983230072969 + 3 ^ 40 * 3540477 * 2
def baseEnd_3540477 : Nat := 1817966447188449601155149

theorem tailTrace_3540477 : CollatzResearch.WordTrace tailWord_3540477 prefixEnd_3540477 1817966447188449601155149 := by
  unfold tailWord_3540477
  simp only [CollatzResearch.WordTrace]
  refine ⟨129131804794463969176843685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86087869862975979451229123 129131804794463969176843685)
  ·
    refine ⟨24212213398961994220658191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129131804794463969176843685 24212213398961994220658191)
    ·
      refine ⟨36318320098442991330987287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24212213398961994220658191 36318320098442991330987287)
      ·
        refine ⟨54477480147664486996480931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36318320098442991330987287 54477480147664486996480931)
        ·
          refine ⟨81716220221496730494721397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54477480147664486996480931 81716220221496730494721397)
          ·
            refine ⟨7660895645765318483880131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81716220221496730494721397 7660895645765318483880131)
            ·
              refine ⟨11491343468647977725820197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7660895645765318483880131 11491343468647977725820197)
              ·
                refine ⟨2154626900371495823591287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11491343468647977725820197 2154626900371495823591287)
                ·
                  refine ⟨3231940350557243735386931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2154626900371495823591287 3231940350557243735386931)
                  ·
                    refine ⟨4847910525835865603080397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3231940350557243735386931 4847910525835865603080397)
                    ·
                      refine ⟨1817966447188449601155149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4847910525835865603080397 1817966447188449601155149)
                      ·
                        rfl

theorem cell23_3540477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 4, 1, 1, 3].length) (baseStart_3540477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540477 prefixEnd_3540477 := by exact prefixLift 3540477
  have htrace : WordTrace (prefixWord ++ tailWord_3540477) baseStart_3540477 baseEnd_3540477 := by
    simpa [prefixWord, tailWord_3540477, baseEnd_3540477] using wordTrace_append hprefix tailTrace_3540477
  have hstable : (prefixWord ++ tailWord_3540477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540477).length < 2 ^ (prefixWord ++ tailWord_3540477).sum := by decide
  have hdescent : baseEnd_3540477 < baseStart_3540477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540504 : List Nat := [2, 1, 2, 3, 5, 1, 1, 1, 2, 3, 2]
def baseStart_3540504 : Nat := 118140960795 + 3540504 * 2 ^ 59
def prefixEnd_3540504 : Nat := 4983230072969 + 3 ^ 40 * 3540504 * 2
def baseEnd_3540504 : Nat := 1817980311166120995517525

theorem tailTrace_3540504 : CollatzResearch.WordTrace tailWord_3540504 prefixEnd_3540504 1817980311166120995517525 := by
  unfold tailWord_3540504
  simp only [CollatzResearch.WordTrace]
  refine ⟨64566394782683076394038283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86088526376910768525384377 64566394782683076394038283)
  ·
    refine ⟨96849592174024614591057425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64566394782683076394038283 96849592174024614591057425)
    ·
      refine ⟨72637194130518460943293069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96849592174024614591057425 72637194130518460943293069)
      ·
        refine ⟨27238947798944422853734901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72637194130518460943293069 27238947798944422853734901)
        ·
          refine ⟨2553651356151039642537647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27238947798944422853734901 2553651356151039642537647)
          ·
            refine ⟨3830477034226559463806471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2553651356151039642537647 3830477034226559463806471)
            ·
              refine ⟨5745715551339839195709707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3830477034226559463806471 5745715551339839195709707)
              ·
                refine ⟨8618573327009758793564561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5745715551339839195709707 8618573327009758793564561)
                ·
                  refine ⟨6463929995257319095173421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8618573327009758793564561 6463929995257319095173421)
                  ·
                    refine ⟨2423973748221494660690033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6463929995257319095173421 2423973748221494660690033)
                    ·
                      refine ⟨1817980311166120995517525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2423973748221494660690033 1817980311166120995517525)
                      ·
                        rfl

theorem cell23_3540504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_3540504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540504 prefixEnd_3540504 := by exact prefixLift 3540504
  have htrace : WordTrace (prefixWord ++ tailWord_3540504) baseStart_3540504 baseEnd_3540504 := by
    simpa [prefixWord, tailWord_3540504, baseEnd_3540504] using wordTrace_append hprefix tailTrace_3540504
  have hstable : (prefixWord ++ tailWord_3540504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540504).length < 2 ^ (prefixWord ++ tailWord_3540504).sum := by decide
  have hdescent : baseEnd_3540504 < baseStart_3540504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540513 : List Nat := [1, 2, 3, 2, 2, 2, 2, 2, 1, 2, 4]
def baseStart_3540513 : Nat := 118140960795 + 3540513 * 2 ^ 59
def prefixEnd_3540513 : Nat := 4983230072969 + 3 ^ 40 * 3540513 * 2
def baseEnd_3540513 : Nat := 1817984932492011460304983

theorem tailTrace_3540513 : CollatzResearch.WordTrace tailWord_3540513 prefixEnd_3540513 1817984932492011460304983 := by
  unfold tailWord_3540513
  simp only [CollatzResearch.WordTrace]
  refine ⟨129133117822333547325154193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86088745214889031550102795 129133117822333547325154193)
  ·
    refine ⟨96849838366750160493865645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129133117822333547325154193 96849838366750160493865645)
    ·
      refine ⟨36318689387531310185199617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96849838366750160493865645 36318689387531310185199617)
      ·
        refine ⟨27239017040648482638899713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36318689387531310185199617 27239017040648482638899713)
        ·
          refine ⟨20429262780486361979174785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27239017040648482638899713 20429262780486361979174785)
          ·
            refine ⟨15321947085364771484381089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20429262780486361979174785 15321947085364771484381089)
            ·
              refine ⟨11491460314023578613285817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15321947085364771484381089 11491460314023578613285817)
              ·
                refine ⟨8618595235517683959964363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11491460314023578613285817 8618595235517683959964363)
                ·
                  refine ⟨12927892853276525939946545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8618595235517683959964363 12927892853276525939946545)
                  ·
                    refine ⟨9695919639957394454959909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12927892853276525939946545 9695919639957394454959909)
                    ·
                      refine ⟨1817984932492011460304983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9695919639957394454959909 1817984932492011460304983)
                      ·
                        rfl

theorem cell23_3540513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_3540513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540513 prefixEnd_3540513 := by exact prefixLift 3540513
  have htrace : WordTrace (prefixWord ++ tailWord_3540513) baseStart_3540513 baseEnd_3540513 := by
    simpa [prefixWord, tailWord_3540513, baseEnd_3540513] using wordTrace_append hprefix tailTrace_3540513
  have hstable : (prefixWord ++ tailWord_3540513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540513).length < 2 ^ (prefixWord ++ tailWord_3540513).sum := by decide
  have hdescent : baseEnd_3540513 < baseStart_3540513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540557 : List Nat := [1, 6, 1, 1, 3, 2, 2, 7]
def baseStart_3540557 : Nat := 118140960795 + 3540557 * 2 ^ 59
def prefixEnd_3540557 : Nat := 4983230072969 + 3 ^ 40 * 3540557 * 2
def baseEnd_3540557 : Nat := 67333612060770714376103

theorem tailTrace_3540557 : CollatzResearch.WordTrace tailWord_3540557 prefixEnd_3540557 67333612060770714376103 := by
  unfold tailWord_3540557
  simp only [CollatzResearch.WordTrace]
  refine ⟨129134722634174142839755925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86089815089449428559837283 129134722634174142839755925)
  ·
    refine ⟨6053190123476912945613559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 129134722634174142839755925 6053190123476912945613559)
    ·
      refine ⟨9079785185215369418420339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6053190123476912945613559 9079785185215369418420339)
      ·
        refine ⟨13619677777823054127630509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9079785185215369418420339 13619677777823054127630509)
        ·
          refine ⟨5107379166683645297861441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13619677777823054127630509 5107379166683645297861441)
          ·
            refine ⟨3830534375012733973396081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5107379166683645297861441 3830534375012733973396081)
            ·
              refine ⟨2872900781259550480047061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3830534375012733973396081 2872900781259550480047061)
              ·
                refine ⟨67333612060770714376103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2872900781259550480047061 67333612060770714376103)
                ·
                  rfl

theorem cell23_3540557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 7].length) (baseStart_3540557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540557 prefixEnd_3540557 := by exact prefixLift 3540557
  have htrace : WordTrace (prefixWord ++ tailWord_3540557) baseStart_3540557 baseEnd_3540557 := by
    simpa [prefixWord, tailWord_3540557, baseEnd_3540557] using wordTrace_append hprefix tailTrace_3540557
  have hstable : (prefixWord ++ tailWord_3540557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540557).length < 2 ^ (prefixWord ++ tailWord_3540557).sum := by decide
  have hdescent : baseEnd_3540557 < baseStart_3540557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540643 : List Nat := [1, 1, 1, 4, 1, 1, 3, 4, 2, 5]
def baseStart_3540643 : Nat := 118140960795 + 3540643 * 2 ^ 59
def prefixEnd_3540643 : Nat := 4983230072969 + 3 ^ 40 * 3540643 * 2
def baseEnd_3540643 : Nat := 606017228325698650559795

theorem tailTrace_3540643 : CollatzResearch.WordTrace tailWord_3540643 prefixEnd_3540643 606017228325698650559795 := by
  unfold tailWord_3540643
  simp only [CollatzResearch.WordTrace]
  refine ⟨129137859311862579527386583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86091906207908386351591055 129137859311862579527386583)
  ·
    refine ⟨193706788967793869291079875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129137859311862579527386583 193706788967793869291079875)
    ·
      refine ⟨290560183451690803936619813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193706788967793869291079875 290560183451690803936619813)
      ·
        refine ⟨54480034397192025738116215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 290560183451690803936619813 54480034397192025738116215)
        ·
          refine ⟨81720051595788038607174323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54480034397192025738116215 81720051595788038607174323)
          ·
            refine ⟨122580077393682057910761485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81720051595788038607174323 122580077393682057910761485)
            ·
              refine ⟨45967529022630771716535557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122580077393682057910761485 45967529022630771716535557)
              ·
                refine ⟨8618911691743269696850417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45967529022630771716535557 8618911691743269696850417)
                ·
                  refine ⟨6464183768807452272637813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8618911691743269696850417 6464183768807452272637813)
                  ·
                    refine ⟨606017228325698650559795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6464183768807452272637813 606017228325698650559795)
                    ·
                      rfl

theorem cell23_3540643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 5].length) (baseStart_3540643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540643 prefixEnd_3540643 := by exact prefixLift 3540643
  have htrace : WordTrace (prefixWord ++ tailWord_3540643) baseStart_3540643 baseEnd_3540643 := by
    simpa [prefixWord, tailWord_3540643, baseEnd_3540643] using wordTrace_append hprefix tailTrace_3540643
  have hstable : (prefixWord ++ tailWord_3540643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540643).length < 2 ^ (prefixWord ++ tailWord_3540643).sum := by decide
  have hdescent : baseEnd_3540643 < baseStart_3540643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540680 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 1, 6, 2]
def baseStart_3540680 : Nat := 118140960795 + 3540680 * 2 ^ 59
def prefixEnd_3540680 : Nat := 4983230072969 + 3 ^ 40 * 3540680 * 2
def baseEnd_3540680 : Nat := 1818070683761312306916715

theorem tailTrace_3540680 : CollatzResearch.WordTrace tailWord_3540680 prefixEnd_3540680 1818070683761312306916715 := by
  unfold tailWord_3540680
  simp only [CollatzResearch.WordTrace]
  refine ⟨64569604406364267423241747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86092805875152356564322329 64569604406364267423241747)
  ·
    refine ⟨96854406609546401134862621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64569604406364267423241747 96854406609546401134862621)
    ·
      refine ⟨36320402478579900425573483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96854406609546401134862621 36320402478579900425573483)
      ·
        refine ⟨54480603717869850638360225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36320402478579900425573483 54480603717869850638360225)
        ·
          refine ⟨40860452788402387978770169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54480603717869850638360225 40860452788402387978770169)
          ·
            refine ⟨30645339591301790984077627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40860452788402387978770169 30645339591301790984077627)
            ·
              refine ⟨45968009386952686476116441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30645339591301790984077627 45968009386952686476116441)
              ·
                refine ⟨34476007040214514857087331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45968009386952686476116441 34476007040214514857087331)
                ·
                  refine ⟨51714010560321772285630997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34476007040214514857087331 51714010560321772285630997)
                  ·
                    refine ⟨2424094245015083075888953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51714010560321772285630997 2424094245015083075888953)
                    ·
                      refine ⟨1818070683761312306916715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2424094245015083075888953 1818070683761312306916715)
                      ·
                        rfl

theorem cell23_3540680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 1, 6, 2].length) (baseStart_3540680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3540680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3540680 prefixEnd_3540680 := by exact prefixLift 3540680
  have htrace : WordTrace (prefixWord ++ tailWord_3540680) baseStart_3540680 baseEnd_3540680 := by
    simpa [prefixWord, tailWord_3540680, baseEnd_3540680] using wordTrace_append hprefix tailTrace_3540680
  have hstable : (prefixWord ++ tailWord_3540680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540680).length < 2 ^ (prefixWord ++ tailWord_3540680).sum := by decide
  have hdescent : baseEnd_3540680 < baseStart_3540680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
