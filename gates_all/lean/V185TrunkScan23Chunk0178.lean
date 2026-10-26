import V185TrunkScan23Chunk0177

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1053229 : List Nat := [1, 5, 4, 1, 1, 2, 2, 1, 2, 1, 3]
def baseStart_1053229 : Nat := 118140960795 + 1053229 * 2 ^ 59
def prefixEnd_1053229 : Nat := 4983230072969 + 3 ^ 40 * 1053229 * 2
def baseEnd_1053229 : Nat := 540812716254364970393795

theorem tailTrace_1053229 : CollatzResearch.WordTrace tailWord_1053229 prefixEnd_1053229 540812716254364970393795 := by
  unfold tailWord_1053229
  simp only [CollatzResearch.WordTrace]
  refine ⟨38414417501338685037554741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25609611667559123358369827 38414417501338685037554741)
  ·
    refine ⟨3601351640750501722270757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38414417501338685037554741 3601351640750501722270757)
    ·
      refine ⟨675253432640719072925767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3601351640750501722270757 675253432640719072925767)
      ·
        refine ⟨1012880148961078609388651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675253432640719072925767 1012880148961078609388651)
        ·
          refine ⟨1519320223441617914082977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1012880148961078609388651 1519320223441617914082977)
          ·
            refine ⟨1139490167581213435562233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1519320223441617914082977 1139490167581213435562233)
            ·
              refine ⟨854617625685910076671675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1139490167581213435562233 854617625685910076671675)
              ·
                refine ⟨1281926438528865115007513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 854617625685910076671675 1281926438528865115007513)
                ·
                  refine ⟨961444828896648836255635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1281926438528865115007513 961444828896648836255635)
                  ·
                    refine ⟨1442167243344973254383453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 961444828896648836255635 1442167243344973254383453)
                    ·
                      refine ⟨540812716254364970393795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1442167243344973254383453 540812716254364970393795)
                      ·
                        rfl

theorem cell23_1053229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_1053229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053229 prefixEnd_1053229 := by exact prefixLift 1053229
  have htrace : WordTrace (prefixWord ++ tailWord_1053229) baseStart_1053229 baseEnd_1053229 := by
    simpa [prefixWord, tailWord_1053229, baseEnd_1053229] using wordTrace_append hprefix tailTrace_1053229
  have hstable : (prefixWord ++ tailWord_1053229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053229).length < 2 ^ (prefixWord ++ tailWord_1053229).sum := by decide
  have hdescent : baseEnd_1053229 < baseStart_1053229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053237 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 4, 5]
def baseStart_1053237 : Nat := 118140960795 + 1053237 * 2 ^ 59
def prefixEnd_1053237 : Nat := 4983230072969 + 3 ^ 40 * 1053237 * 2
def baseEnd_1053237 : Nat := 180272274699866979697919

theorem tailTrace_1053237 : CollatzResearch.WordTrace tailWord_1053237 prefixEnd_1053237 180272274699866979697919 := by
  unfold tailWord_1053237
  simp only [CollatzResearch.WordTrace]
  refine ⟨38414709285309702403845965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25609806190206468269230643 38414709285309702403845965)
  ·
    refine ⟨14405515981991138401442237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38414709285309702403845965 14405515981991138401442237)
    ·
      refine ⟨5402068493246676900540839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14405515981991138401442237 5402068493246676900540839)
      ·
        refine ⟨8103102739870015350811259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5402068493246676900540839 8103102739870015350811259)
        ·
          refine ⟨12154654109805023026216889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8103102739870015350811259 12154654109805023026216889)
          ·
            refine ⟨9115990582353767269662667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12154654109805023026216889 9115990582353767269662667)
            ·
              refine ⟨13673985873530650904494001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9115990582353767269662667 13673985873530650904494001)
              ·
                refine ⟨10255489405147988178370501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13673985873530650904494001 10255489405147988178370501)
                ·
                  refine ⟨1922904263465247783444469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10255489405147988178370501 1922904263465247783444469)
                  ·
                    refine ⟨180272274699866979697919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1922904263465247783444469 180272274699866979697919)
                    ·
                      rfl

theorem cell23_1053237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_1053237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053237 prefixEnd_1053237 := by exact prefixLift 1053237
  have htrace : WordTrace (prefixWord ++ tailWord_1053237) baseStart_1053237 baseEnd_1053237 := by
    simpa [prefixWord, tailWord_1053237, baseEnd_1053237] using wordTrace_append hprefix tailTrace_1053237
  have hstable : (prefixWord ++ tailWord_1053237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053237).length < 2 ^ (prefixWord ++ tailWord_1053237).sum := by decide
  have hdescent : baseEnd_1053237 < baseStart_1053237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053284 : List Nat := [2, 3, 1, 1, 2, 2, 2, 3, 3, 4]
def baseStart_1053284 : Nat := 118140960795 + 1053284 * 2 ^ 59
def prefixEnd_1053284 : Nat := 4983230072969 + 3 ^ 40 * 1053284 * 2
def baseEnd_1053284 : Nat := 180280319230120751735347

theorem tailTrace_1053284 : CollatzResearch.WordTrace tailWord_1053284 prefixEnd_1053284 180280319230120751735347 := by
  unfold tailWord_1053284
  simp only [CollatzResearch.WordTrace]
  refine ⟨19208211758069714715403453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25610949010759619620537937 19208211758069714715403453)
  ·
    refine ⟨7203079409276143018276295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19208211758069714715403453 7203079409276143018276295)
    ·
      refine ⟨10804619113914214527414443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7203079409276143018276295 10804619113914214527414443)
      ·
        refine ⟨16206928670871321791121665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10804619113914214527414443 16206928670871321791121665)
        ·
          refine ⟨12155196503153491343341249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16206928670871321791121665 12155196503153491343341249)
          ·
            refine ⟨9116397377365118507505937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12155196503153491343341249 9116397377365118507505937)
            ·
              refine ⟨6837298033023838880629453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9116397377365118507505937 6837298033023838880629453)
              ·
                refine ⟨2563986762383939580236045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6837298033023838880629453 2563986762383939580236045)
                ·
                  refine ⟨961495035893977342588517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2563986762383939580236045 961495035893977342588517)
                  ·
                    refine ⟨180280319230120751735347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 961495035893977342588517 180280319230120751735347)
                    ·
                      rfl

theorem cell23_1053284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_1053284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053284 prefixEnd_1053284 := by exact prefixLift 1053284
  have htrace : WordTrace (prefixWord ++ tailWord_1053284) baseStart_1053284 baseEnd_1053284 := by
    simpa [prefixWord, tailWord_1053284, baseEnd_1053284] using wordTrace_append hprefix tailTrace_1053284
  have hstable : (prefixWord ++ tailWord_1053284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053284).length < 2 ^ (prefixWord ++ tailWord_1053284).sum := by decide
  have hdescent : baseEnd_1053284 < baseStart_1053284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053287 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 4]
def baseStart_1053287 : Nat := 118140960795 + 1053287 * 2 ^ 59
def prefixEnd_1053287 : Nat := 4983230072969 + 3 ^ 40 * 1053287 * 2
def baseEnd_1053287 : Nat := 540842498132325743468527

theorem tailTrace_1053287 : CollatzResearch.WordTrace tailWord_1053287 prefixEnd_1053287 540842498132325743468527 := by
  unfold tailWord_1053287
  simp only [CollatzResearch.WordTrace]
  refine ⟨38416532935128560943166115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25611021956752373962110743 38416532935128560943166115)
  ·
    refine ⟨57624799402692841414749173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38416532935128560943166115 57624799402692841414749173)
    ·
      refine ⟨5402324944002453882632735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57624799402692841414749173 5402324944002453882632735)
      ·
        refine ⟨8103487416003680823949103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5402324944002453882632735 8103487416003680823949103)
        ·
          refine ⟨12155231124005521235923655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8103487416003680823949103 12155231124005521235923655)
          ·
            refine ⟨18232846686008281853885483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12155231124005521235923655 18232846686008281853885483)
            ·
              refine ⟨27349270029012422780828225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18232846686008281853885483 27349270029012422780828225)
              ·
                refine ⟨20511952521759317085621169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27349270029012422780828225 20511952521759317085621169)
                ·
                  refine ⟨15383964391319487814215877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20511952521759317085621169 15383964391319487814215877)
                  ·
                    refine ⟨2884493323372403965165477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15383964391319487814215877 2884493323372403965165477)
                    ·
                      refine ⟨540842498132325743468527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2884493323372403965165477 540842498132325743468527)
                      ·
                        rfl

theorem cell23_1053287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_1053287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053287 prefixEnd_1053287 := by exact prefixLift 1053287
  have htrace : WordTrace (prefixWord ++ tailWord_1053287) baseStart_1053287 baseEnd_1053287 := by
    simpa [prefixWord, tailWord_1053287, baseEnd_1053287] using wordTrace_append hprefix tailTrace_1053287
  have hstable : (prefixWord ++ tailWord_1053287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053287).length < 2 ^ (prefixWord ++ tailWord_1053287).sum := by decide
  have hdescent : baseEnd_1053287 < baseStart_1053287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053307 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 1, 7, 3]
def baseStart_1053307 : Nat := 118140960795 + 1053307 * 2 ^ 59
def prefixEnd_1053307 : Nat := 4983230072969 + 3 ^ 40 * 1053307 * 2
def baseEnd_1053307 : Nat := 540852767745415665218435

theorem tailTrace_1053307 : CollatzResearch.WordTrace tailWord_1053307 prefixEnd_1053307 540852767745415665218435 := by
  unfold tailWord_1053307
  simp only [CollatzResearch.WordTrace]
  refine ⟨38417262395056104358894175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25611508263370736239262783 38417262395056104358894175)
  ·
    refine ⟨57625893592584156538341263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38417262395056104358894175 57625893592584156538341263)
    ·
      refine ⟨86438840388876234807511895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57625893592584156538341263 86438840388876234807511895)
      ·
        refine ⟨129658260583314352211267843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86438840388876234807511895 129658260583314352211267843)
        ·
          refine ⟨194487390874971528316901765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129658260583314352211267843 194487390874971528316901765)
          ·
            refine ⟨36466385789057161559419081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 194487390874971528316901765 36466385789057161559419081)
            ·
              refine ⟨27349789341792871169564311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36466385789057161559419081 27349789341792871169564311)
              ·
                refine ⟨41024684012689306754346467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27349789341792871169564311 41024684012689306754346467)
                ·
                  refine ⟨61537026019033960131519701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41024684012689306754346467 61537026019033960131519701)
                  ·
                    refine ⟨1442274047321108440582493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61537026019033960131519701 1442274047321108440582493)
                    ·
                      refine ⟨540852767745415665218435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1442274047321108440582493 540852767745415665218435)
                      ·
                        rfl

theorem cell23_1053307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 7, 3].length) (baseStart_1053307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053307 prefixEnd_1053307 := by exact prefixLift 1053307
  have htrace : WordTrace (prefixWord ++ tailWord_1053307) baseStart_1053307 baseEnd_1053307 := by
    simpa [prefixWord, tailWord_1053307, baseEnd_1053307] using wordTrace_append hprefix tailTrace_1053307
  have hstable : (prefixWord ++ tailWord_1053307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053307).length < 2 ^ (prefixWord ++ tailWord_1053307).sum := by decide
  have hdescent : baseEnd_1053307 < baseStart_1053307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053341 : List Nat := [1, 4, 2, 1, 1, 1, 3, 3, 3, 1, 3]
def baseStart_1053341 : Nat := 118140960795 + 1053341 * 2 ^ 59
def prefixEnd_1053341 : Nat := 4983230072969 + 3 ^ 40 * 1053341 * 2
def baseEnd_1053341 : Nat := 540870226087668532193279

theorem tailTrace_1053341 : CollatzResearch.WordTrace tailWord_1053341 prefixEnd_1053341 540870226087668532193279 := by
  unfold tailWord_1053341
  simp only [CollatzResearch.WordTrace]
  refine ⟨38418502476932928165631877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25612334984621952110421251 38418502476932928165631877)
  ·
    refine ⟨7203469214424924031055977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38418502476932928165631877 7203469214424924031055977)
    ·
      refine ⟨5402601910818693023291983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7203469214424924031055977 5402601910818693023291983)
      ·
        refine ⟨8103902866228039534937975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5402601910818693023291983 8103902866228039534937975)
        ·
          refine ⟨12155854299342059302406963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8103902866228039534937975 12155854299342059302406963)
          ·
            refine ⟨18233781449013088953610445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12155854299342059302406963 18233781449013088953610445)
            ·
              refine ⟨6837668043379908357603917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18233781449013088953610445 6837668043379908357603917)
              ·
                refine ⟨2564125516267465634101469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6837668043379908357603917 2564125516267465634101469)
                ·
                  refine ⟨961547068600299612788051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2564125516267465634101469 961547068600299612788051)
                  ·
                    refine ⟨1442320602900449419182077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 961547068600299612788051 1442320602900449419182077)
                    ·
                      refine ⟨540870226087668532193279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1442320602900449419182077 540870226087668532193279)
                      ·
                        rfl

theorem cell23_1053341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_1053341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053341 prefixEnd_1053341 := by exact prefixLift 1053341
  have htrace : WordTrace (prefixWord ++ tailWord_1053341) baseStart_1053341 baseEnd_1053341 := by
    simpa [prefixWord, tailWord_1053341, baseEnd_1053341] using wordTrace_append hprefix tailTrace_1053341
  have hstable : (prefixWord ++ tailWord_1053341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053341).length < 2 ^ (prefixWord ++ tailWord_1053341).sum := by decide
  have hdescent : baseEnd_1053341 < baseStart_1053341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053347 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 4]
def baseStart_1053347 : Nat := 118140960795 + 1053347 * 2 ^ 59
def prefixEnd_1053347 : Nat := 4983230072969 + 3 ^ 40 * 1053347 * 2
def baseEnd_1053347 : Nat := 540873306971595508718251

theorem tailTrace_1053347 : CollatzResearch.WordTrace tailWord_1053347 prefixEnd_1053347 540873306971595508718251 := by
  unfold tailWord_1053347
  simp only [CollatzResearch.WordTrace]
  refine ⟨38418721314911191190350295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25612480876607460793566863 38418721314911191190350295)
  ·
    refine ⟨57628081972366786785525443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38418721314911191190350295 57628081972366786785525443)
    ·
      refine ⟨86442122958550180178288165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57628081972366786785525443 86442122958550180178288165)
      ·
        refine ⟨16207898054728158783429031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86442122958550180178288165 16207898054728158783429031)
        ·
          refine ⟨24311847082092238175143547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16207898054728158783429031 24311847082092238175143547)
          ·
            refine ⟨36467770623138357262715321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24311847082092238175143547 36467770623138357262715321)
            ·
              refine ⟨27350827967353767947036491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36467770623138357262715321 27350827967353767947036491)
              ·
                refine ⟨41026241951030651920554737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27350827967353767947036491 41026241951030651920554737)
                ·
                  refine ⟨30769681463272988940416053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41026241951030651920554737 30769681463272988940416053)
                  ·
                    refine ⟨2884657637181842713164005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30769681463272988940416053 2884657637181842713164005)
                    ·
                      refine ⟨540873306971595508718251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2884657637181842713164005 540873306971595508718251)
                      ·
                        rfl

theorem cell23_1053347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_1053347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053347 prefixEnd_1053347 := by exact prefixLift 1053347
  have htrace : WordTrace (prefixWord ++ tailWord_1053347) baseStart_1053347 baseEnd_1053347 := by
    simpa [prefixWord, tailWord_1053347, baseEnd_1053347] using wordTrace_append hprefix tailTrace_1053347
  have hstable : (prefixWord ++ tailWord_1053347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053347).length < 2 ^ (prefixWord ++ tailWord_1053347).sum := by decide
  have hdescent : baseEnd_1053347 < baseStart_1053347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053374 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 3, 6]
def baseStart_1053374 : Nat := 118140960795 + 1053374 * 2 ^ 59
def prefixEnd_1053374 : Nat := 4983230072969 + 3 ^ 40 * 1053374 * 2
def baseEnd_1053374 : Nat := 180295723649755634360209

theorem tailTrace_1053374 : CollatzResearch.WordTrace tailWord_1053374 prefixEnd_1053374 180295723649755634360209 := by
  unfold tailWord_1053374
  simp only [CollatzResearch.WordTrace]
  refine ⟨4802463260726671850197897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25613137390542249867722117 4802463260726671850197897)
  ·
    refine ⟨3601847445545003887648423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4802463260726671850197897 3601847445545003887648423)
    ·
      refine ⟨5402771168317505831472635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3601847445545003887648423 5402771168317505831472635)
      ·
        refine ⟨8104156752476258747208953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5402771168317505831472635 8104156752476258747208953)
        ·
          refine ⟨6078117564357194060406715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8104156752476258747208953 6078117564357194060406715)
          ·
            refine ⟨9117176346535791090610073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6078117564357194060406715 9117176346535791090610073)
            ·
              refine ⟨6837882259901843317957555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9117176346535791090610073 6837882259901843317957555)
              ·
                refine ⟨10256823389852764976936333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6837882259901843317957555 10256823389852764976936333)
                ·
                  refine ⟨3846308771194786866351125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10256823389852764976936333 3846308771194786866351125)
                  ·
                    refine ⟨180295723649755634360209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3846308771194786866351125 180295723649755634360209)
                    ·
                      rfl

theorem cell23_1053374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_1053374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053374 prefixEnd_1053374 := by exact prefixLift 1053374
  have htrace : WordTrace (prefixWord ++ tailWord_1053374) baseStart_1053374 baseEnd_1053374 := by
    simpa [prefixWord, tailWord_1053374, baseEnd_1053374] using wordTrace_append hprefix tailTrace_1053374
  have hstable : (prefixWord ++ tailWord_1053374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053374).length < 2 ^ (prefixWord ++ tailWord_1053374).sum := by decide
  have hdescent : baseEnd_1053374 < baseStart_1053374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053375 : List Nat := [1, 1, 2, 2, 2, 6, 1, 3, 1, 1, 3]
def baseStart_1053375 : Nat := 118140960795 + 1053375 * 2 ^ 59
def prefixEnd_1053375 : Nat := 4983230072969 + 3 ^ 40 * 1053375 * 2
def baseEnd_1053375 : Nat := 540887684429921399168123

theorem tailTrace_1053375 : CollatzResearch.WordTrace tailWord_1053375 prefixEnd_1053375 540887684429921399168123 := by
  unfold tailWord_1053375
  simp only [CollatzResearch.WordTrace]
  refine ⟨38419742558809751972369579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25613161705873167981579719 38419742558809751972369579)
  ·
    refine ⟨57629613838214627958554369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38419742558809751972369579 57629613838214627958554369)
    ·
      refine ⟨43222210378660970968915777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57629613838214627958554369 43222210378660970968915777)
      ·
        refine ⟨32416657783995728226686833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43222210378660970968915777 32416657783995728226686833)
        ·
          refine ⟨24312493337996796170015125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32416657783995728226686833 24312493337996796170015125)
          ·
            refine ⟨1139648125218599820469459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24312493337996796170015125 1139648125218599820469459)
            ·
              refine ⟨1709472187827899730704189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1139648125218599820469459 1709472187827899730704189)
              ·
                refine ⟨641052070435462399014071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1709472187827899730704189 641052070435462399014071)
                ·
                  refine ⟨961578105653193598521107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 641052070435462399014071 961578105653193598521107)
                  ·
                    refine ⟨1442367158479790397781661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 961578105653193598521107 1442367158479790397781661)
                    ·
                      refine ⟨540887684429921399168123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1442367158479790397781661 540887684429921399168123)
                      ·
                        rfl

theorem cell23_1053375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 3, 1, 1, 3].length) (baseStart_1053375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053375 prefixEnd_1053375 := by exact prefixLift 1053375
  have htrace : WordTrace (prefixWord ++ tailWord_1053375) baseStart_1053375 baseEnd_1053375 := by
    simpa [prefixWord, tailWord_1053375, baseEnd_1053375] using wordTrace_append hprefix tailTrace_1053375
  have hstable : (prefixWord ++ tailWord_1053375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053375).length < 2 ^ (prefixWord ++ tailWord_1053375).sum := by decide
  have hdescent : baseEnd_1053375 < baseStart_1053375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053384 : List Nat := [2, 1, 3, 1, 2, 3, 1, 3, 1, 1, 5]
def baseStart_1053384 : Nat := 118140960795 + 1053384 * 2 ^ 59
def prefixEnd_1053384 : Nat := 4983230072969 + 3 ^ 40 * 1053384 * 2
def baseEnd_1053384 : Nat := 540892305755811863955581

theorem tailTrace_1053384 : CollatzResearch.WordTrace tailWord_1053384 prefixEnd_1053384 540892305755811863955581 := by
  unfold tailWord_1053384
  simp only [CollatzResearch.WordTrace]
  refine ⟨19210035407888573254723603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25613380543851431006298137 19210035407888573254723603)
  ·
    refine ⟨28815053111832859882085405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19210035407888573254723603 28815053111832859882085405)
    ·
      refine ⟨10805644916937322455782027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28815053111832859882085405 10805644916937322455782027)
      ·
        refine ⟨16208467375405983683673041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10805644916937322455782027 16208467375405983683673041)
        ·
          refine ⟨12156350531554487762754781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16208467375405983683673041 12156350531554487762754781)
          ·
            refine ⟨4558631449332932911033043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12156350531554487762754781 4558631449332932911033043)
            ·
              refine ⟨6837947173999399366549565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4558631449332932911033043 6837947173999399366549565)
              ·
                refine ⟨2564230190249774762456087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6837947173999399366549565 2564230190249774762456087)
                ·
                  refine ⟨3846345285374662143684131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2564230190249774762456087 3846345285374662143684131)
                  ·
                    refine ⟨5769517928061993215526197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3846345285374662143684131 5769517928061993215526197)
                    ·
                      refine ⟨540892305755811863955581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5769517928061993215526197 540892305755811863955581)
                      ·
                        rfl

theorem cell23_1053384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_1053384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053384 prefixEnd_1053384 := by exact prefixLift 1053384
  have htrace : WordTrace (prefixWord ++ tailWord_1053384) baseStart_1053384 baseEnd_1053384 := by
    simpa [prefixWord, tailWord_1053384, baseEnd_1053384] using wordTrace_append hprefix tailTrace_1053384
  have hstable : (prefixWord ++ tailWord_1053384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053384).length < 2 ^ (prefixWord ++ tailWord_1053384).sum := by decide
  have hdescent : baseEnd_1053384 < baseStart_1053384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053448 : List Nat := [2, 1, 3, 2, 2, 2, 1, 4, 2, 1, 3]
def baseStart_1053448 : Nat := 118140960795 + 1053448 * 2 ^ 59
def prefixEnd_1053448 : Nat := 4983230072969 + 3 ^ 40 * 1053448 * 2
def baseEnd_1053448 : Nat := 540925168517699613555287

theorem tailTrace_1053448 : CollatzResearch.WordTrace tailWord_1053448 prefixEnd_1053448 540925168517699613555287 := by
  unfold tailWord_1053448
  simp only [CollatzResearch.WordTrace]
  refine ⟨19211202543772642719888499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25614936725030190293184665 19211202543772642719888499)
  ·
    refine ⟨28816803815658964079832749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19211202543772642719888499 28816803815658964079832749)
    ·
      refine ⟨10806301430872111529937281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28816803815658964079832749 10806301430872111529937281)
      ·
        refine ⟨8104726073154083647452961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10806301430872111529937281 8104726073154083647452961)
        ·
          refine ⟨6078544554865562735589721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8104726073154083647452961 6078544554865562735589721)
          ·
            refine ⟨4558908416149172051692291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6078544554865562735589721 4558908416149172051692291)
            ·
              refine ⟨6838362624223758077538437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4558908416149172051692291 6838362624223758077538437)
              ·
                refine ⟨1282192992041954639538457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6838362624223758077538437 1282192992041954639538457)
                ·
                  refine ⟨961644744031465979653843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1282192992041954639538457 961644744031465979653843)
                  ·
                    refine ⟨1442467116047198969480765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 961644744031465979653843 1442467116047198969480765)
                    ·
                      refine ⟨540925168517699613555287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1442467116047198969480765 540925168517699613555287)
                      ·
                        rfl

theorem cell23_1053448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_1053448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053448 prefixEnd_1053448 := by exact prefixLift 1053448
  have htrace : WordTrace (prefixWord ++ tailWord_1053448) baseStart_1053448 baseEnd_1053448 := by
    simpa [prefixWord, tailWord_1053448, baseEnd_1053448] using wordTrace_append hprefix tailTrace_1053448
  have hstable : (prefixWord ++ tailWord_1053448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053448).length < 2 ^ (prefixWord ++ tailWord_1053448).sum := by decide
  have hdescent : baseEnd_1053448 < baseStart_1053448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053484 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 4]
def baseStart_1053484 : Nat := 118140960795 + 1053484 * 2 ^ 59
def prefixEnd_1053484 : Nat := 4983230072969 + 3 ^ 40 * 1053484 * 2
def baseEnd_1053484 : Nat := 540943653821261472705121

theorem tailTrace_1053484 : CollatzResearch.WordTrace tailWord_1053484 prefixEnd_1053484 540943653821261472705121 := by
  unfold tailWord_1053484
  simp only [CollatzResearch.WordTrace]
  refine ⟨19211859057707431794043753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25615812076943242392058337 19211859057707431794043753)
  ·
    refine ⟨14408894293280573845532815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19211859057707431794043753 14408894293280573845532815)
    ·
      refine ⟨21613341439920860768299223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14408894293280573845532815 21613341439920860768299223)
      ·
        refine ⟨32420012159881291152448835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21613341439920860768299223 32420012159881291152448835)
        ·
          refine ⟨48630018239821936728673253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32420012159881291152448835 48630018239821936728673253)
          ·
            refine ⟨9118128419966613136626235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48630018239821936728673253 9118128419966613136626235)
            ·
              refine ⟨13677192629949919704939353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9118128419966613136626235 13677192629949919704939353)
              ·
                refine ⟨10257894472462439778704515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13677192629949919704939353 10257894472462439778704515)
                ·
                  refine ⟨15386841708693659668056773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10257894472462439778704515 15386841708693659668056773)
                  ·
                    refine ⟨2885032820380061187760645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15386841708693659668056773 2885032820380061187760645)
                    ·
                      refine ⟨540943653821261472705121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2885032820380061187760645 540943653821261472705121)
                      ·
                        rfl

theorem cell23_1053484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_1053484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053484 prefixEnd_1053484 := by exact prefixLift 1053484
  have htrace : WordTrace (prefixWord ++ tailWord_1053484) baseStart_1053484 baseEnd_1053484 := by
    simpa [prefixWord, tailWord_1053484, baseEnd_1053484] using wordTrace_append hprefix tailTrace_1053484
  have hstable : (prefixWord ++ tailWord_1053484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053484).length < 2 ^ (prefixWord ++ tailWord_1053484).sum := by decide
  have hdescent : baseEnd_1053484 < baseStart_1053484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053492 : List Nat := [2, 5, 1, 1, 3, 1, 1, 3, 1, 3, 2]
def baseStart_1053492 : Nat := 118140960795 + 1053492 * 2 ^ 59
def prefixEnd_1053492 : Nat := 4983230072969 + 3 ^ 40 * 1053492 * 2
def baseEnd_1053492 : Nat := 540947761666497441405085

theorem tailTrace_1053492 : CollatzResearch.WordTrace tailWord_1053492 prefixEnd_1053492 540947761666497441405085 := by
  unfold tailWord_1053492
  simp only [CollatzResearch.WordTrace]
  refine ⟨19212004949692940477189365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25616006599590587302919153 19212004949692940477189365)
  ·
    refine ⟨1801125464033713169736503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19212004949692940477189365 1801125464033713169736503)
    ·
      refine ⟨2701688196050569754604755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1801125464033713169736503 2701688196050569754604755)
      ·
        refine ⟨4052532294075854631907133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2701688196050569754604755 4052532294075854631907133)
        ·
          refine ⟨1519699610278445486965175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4052532294075854631907133 1519699610278445486965175)
          ·
            refine ⟨2279549415417668230447763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1519699610278445486965175 2279549415417668230447763)
            ·
              refine ⟨3419324123126502345671645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2279549415417668230447763 3419324123126502345671645)
              ·
                refine ⟨1282246546172438379626867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3419324123126502345671645 1282246546172438379626867)
                ·
                  refine ⟨1923369819258657569440301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1282246546172438379626867 1923369819258657569440301)
                  ·
                    refine ⟨721263682221996588540113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1923369819258657569440301 721263682221996588540113)
                    ·
                      refine ⟨540947761666497441405085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 721263682221996588540113 540947761666497441405085)
                      ·
                        rfl

theorem cell23_1053492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_1053492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053492 prefixEnd_1053492 := by exact prefixLift 1053492
  have htrace : WordTrace (prefixWord ++ tailWord_1053492) baseStart_1053492 baseEnd_1053492 := by
    simpa [prefixWord, tailWord_1053492, baseEnd_1053492] using wordTrace_append hprefix tailTrace_1053492
  have hstable : (prefixWord ++ tailWord_1053492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053492).length < 2 ^ (prefixWord ++ tailWord_1053492).sum := by decide
  have hdescent : baseEnd_1053492 < baseStart_1053492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053522 : List Nat := [3, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2]
def baseStart_1053522 : Nat := 118140960795 + 1053522 * 2 ^ 59
def prefixEnd_1053522 : Nat := 4983230072969 + 3 ^ 40 * 1053522 * 2
def baseEnd_1053522 : Nat := 540963166086132324029947

theorem tailTrace_1053522 : CollatzResearch.WordTrace tailWord_1053522 prefixEnd_1053522 540963166086132324029947 := by
  unfold tailWord_1053522
  simp only [CollatzResearch.WordTrace]
  refine ⟨9606276022319299019492705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25616736059518130718647213 9606276022319299019492705)
  ·
    refine ⟨7204707016739474264619529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9606276022319299019492705 7204707016739474264619529)
    ·
      refine ⟨5403530262554605698464647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7204707016739474264619529 5403530262554605698464647)
      ·
        refine ⟨8105295393831908547696971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5403530262554605698464647 8105295393831908547696971)
        ·
          refine ⟨12157943090747862821545457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8105295393831908547696971 12157943090747862821545457)
          ·
            refine ⟨9118457318060897116159093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12157943090747862821545457 9118457318060897116159093)
            ·
              refine ⟨854855373568209104639915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9118457318060897116159093 854855373568209104639915)
              ·
                refine ⟨1282283060352313656959873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 854855373568209104639915 1282283060352313656959873)
                ·
                  refine ⟨961712295264235242719905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1282283060352313656959873 961712295264235242719905)
                  ·
                    refine ⟨721284221448176432039929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 961712295264235242719905 721284221448176432039929)
                    ·
                      refine ⟨540963166086132324029947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 721284221448176432039929 540963166086132324029947)
                      ·
                        rfl

theorem cell23_1053522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_1053522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053522 prefixEnd_1053522 := by exact prefixLift 1053522
  have htrace : WordTrace (prefixWord ++ tailWord_1053522) baseStart_1053522 baseEnd_1053522 := by
    simpa [prefixWord, tailWord_1053522, baseEnd_1053522] using wordTrace_append hprefix tailTrace_1053522
  have hstable : (prefixWord ++ tailWord_1053522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053522).length < 2 ^ (prefixWord ++ tailWord_1053522).sum := by decide
  have hdescent : baseEnd_1053522 < baseStart_1053522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053558 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 4, 5]
def baseStart_1053558 : Nat := 118140960795 + 1053558 * 2 ^ 59
def prefixEnd_1053558 : Nat := 4983230072969 + 3 ^ 40 * 1053558 * 2
def baseEnd_1053558 : Nat := 180327217129898061059927

theorem tailTrace_1053558 : CollatzResearch.WordTrace tailWord_1053558 prefixEnd_1053558 180327217129898061059927 := by
  unfold tailWord_1053558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2401651069821673389142583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25617611411431182817520885 2401651069821673389142583)
  ·
    refine ⟨3602476604732510083713875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2401651069821673389142583 3602476604732510083713875)
    ·
      refine ⟨5403714907098765125570813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3602476604732510083713875 5403714907098765125570813)
      ·
        refine ⟨2026393090162036922089055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5403714907098765125570813 2026393090162036922089055)
        ·
          refine ⟨3039589635243055383133583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2026393090162036922089055 3039589635243055383133583)
          ·
            refine ⟨4559384452864583074700375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3039589635243055383133583 4559384452864583074700375)
            ·
              refine ⟨6839076679296874612050563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4559384452864583074700375 6839076679296874612050563)
              ·
                refine ⟨10258615018945311918075845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6839076679296874612050563 10258615018945311918075845)
                ·
                  refine ⟨1923490316052245984639221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10258615018945311918075845 1923490316052245984639221)
                  ·
                    refine ⟨180327217129898061059927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1923490316052245984639221 180327217129898061059927)
                    ·
                      rfl

theorem cell23_1053558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_1053558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053558 prefixEnd_1053558 := by exact prefixLift 1053558
  have htrace : WordTrace (prefixWord ++ tailWord_1053558) baseStart_1053558 baseEnd_1053558 := by
    simpa [prefixWord, tailWord_1053558, baseEnd_1053558] using wordTrace_append hprefix tailTrace_1053558
  have hstable : (prefixWord ++ tailWord_1053558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053558).length < 2 ^ (prefixWord ++ tailWord_1053558).sum := by decide
  have hdescent : baseEnd_1053558 < baseStart_1053558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053561 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 4, 1, 4]
def baseStart_1053561 : Nat := 118140960795 + 1053561 * 2 ^ 59
def prefixEnd_1053561 : Nat := 4983230072969 + 3 ^ 40 * 1053561 * 2
def baseEnd_1053561 : Nat := 540983191831657671442267

theorem tailTrace_1053561 : CollatzResearch.WordTrace tailWord_1053561 prefixEnd_1053561 540983191831657671442267 := by
  unfold tailWord_1053561
  simp only [CollatzResearch.WordTrace]
  refine ⟨38426526536135905738640537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25617684357423937159093691 38426526536135905738640537)
  ·
    refine ⟨28819894902101929303980403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38426526536135905738640537 28819894902101929303980403)
    ·
      refine ⟨43229842353152893955970605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28819894902101929303980403 43229842353152893955970605)
      ·
        refine ⟨16211190882432335233488977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43229842353152893955970605 16211190882432335233488977)
        ·
          refine ⟨12158393161824251425116733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16211190882432335233488977 12158393161824251425116733)
          ·
            refine ⟨4559397435684094284418775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12158393161824251425116733 4559397435684094284418775)
            ·
              refine ⟨6839096153526141426628163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4559397435684094284418775 6839096153526141426628163)
              ·
                refine ⟨10258644230289212139942245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6839096153526141426628163 10258644230289212139942245)
                ·
                  refine ⟨1923495793179227276239171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10258644230289212139942245 1923495793179227276239171)
                  ·
                    refine ⟨2885243689768840914358757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1923495793179227276239171 2885243689768840914358757)
                    ·
                      refine ⟨540983191831657671442267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2885243689768840914358757 540983191831657671442267)
                      ·
                        rfl

theorem cell23_1053561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_1053561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053561 prefixEnd_1053561 := by exact prefixLift 1053561
  have htrace : WordTrace (prefixWord ++ tailWord_1053561) baseStart_1053561 baseEnd_1053561 := by
    simpa [prefixWord, tailWord_1053561, baseEnd_1053561] using wordTrace_append hprefix tailTrace_1053561
  have hstable : (prefixWord ++ tailWord_1053561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053561).length < 2 ^ (prefixWord ++ tailWord_1053561).sum := by decide
  have hdescent : baseEnd_1053561 < baseStart_1053561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053588 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 5, 4]
def baseStart_1053588 : Nat := 118140960795 + 1053588 * 2 ^ 59
def prefixEnd_1053588 : Nat := 4983230072969 + 3 ^ 40 * 1053588 * 2
def baseEnd_1053588 : Nat := 180332351936443021934881

theorem tailTrace_1053588 : CollatzResearch.WordTrace tailWord_1053588 prefixEnd_1053588 180332351936443021934881 := by
  unfold tailWord_1053588
  simp only [CollatzResearch.WordTrace]
  refine ⟨19213755653519044674936709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25618340871358726233248945 19213755653519044674936709)
  ·
    refine ⟨3602579185034820876550633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19213755653519044674936709 3602579185034820876550633)
    ·
      refine ⟨2701934388776115657412975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3602579185034820876550633 2701934388776115657412975)
      ·
        refine ⟨4052901583164173486119463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2701934388776115657412975 4052901583164173486119463)
        ·
          refine ⟨6079352374746260229179195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4052901583164173486119463 6079352374746260229179195)
          ·
            refine ⟨9119028562119390343768793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6079352374746260229179195 9119028562119390343768793)
            ·
              refine ⟨6839271421589542757826595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9119028562119390343768793 6839271421589542757826595)
              ·
                refine ⟨10258907132384314136739893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6839271421589542757826595 10258907132384314136739893)
                ·
                  refine ⟨961772543661029450319365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10258907132384314136739893 961772543661029450319365)
                  ·
                    refine ⟨180332351936443021934881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 961772543661029450319365 180332351936443021934881)
                    ·
                      rfl

theorem cell23_1053588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_1053588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053588 prefixEnd_1053588 := by exact prefixLift 1053588
  have htrace : WordTrace (prefixWord ++ tailWord_1053588) baseStart_1053588 baseEnd_1053588 := by
    simpa [prefixWord, tailWord_1053588, baseEnd_1053588] using wordTrace_append hprefix tailTrace_1053588
  have hstable : (prefixWord ++ tailWord_1053588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053588).length < 2 ^ (prefixWord ++ tailWord_1053588).sum := by decide
  have hdescent : baseEnd_1053588 < baseStart_1053588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053621 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 1, 2, 6]
def baseStart_1053621 : Nat := 118140960795 + 1053621 * 2 ^ 59
def prefixEnd_1053621 : Nat := 4983230072969 + 3 ^ 40 * 1053621 * 2
def baseEnd_1053621 : Nat := 541014000670927436691991

theorem tailTrace_1053621 : CollatzResearch.WordTrace tailWord_1053621 prefixEnd_1053621 541014000670927436691991 := by
  unfold tailWord_1053621
  simp only [CollatzResearch.WordTrace]
  refine ⟨38428714915918535985824717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25619143277279023990549811 38428714915918535985824717)
  ·
    refine ⟨14410768093469450994684269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38428714915918535985824717 14410768093469450994684269)
    ·
      refine ⟨5404038035051044123006601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14410768093469450994684269 5404038035051044123006601)
      ·
        refine ⟨4053028526288283092254951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5404038035051044123006601 4053028526288283092254951)
        ·
          refine ⟨6079542789432424638382427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4053028526288283092254951 6079542789432424638382427)
          ·
            refine ⟨9119314184148636957573641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6079542789432424638382427 9119314184148636957573641)
            ·
              refine ⟨6839485638111477718180231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9119314184148636957573641 6839485638111477718180231)
              ·
                refine ⟨10259228457167216577270347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6839485638111477718180231 10259228457167216577270347)
                ·
                  refine ⟨15388842685750824865905521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10259228457167216577270347 15388842685750824865905521)
                  ·
                    refine ⟨11541632014313118649429141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15388842685750824865905521 11541632014313118649429141)
                    ·
                      refine ⟨541014000670927436691991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11541632014313118649429141 541014000670927436691991)
                      ·
                        rfl

theorem cell23_1053621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_1053621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053621 prefixEnd_1053621 := by exact prefixLift 1053621
  have htrace : WordTrace (prefixWord ++ tailWord_1053621) baseStart_1053621 baseEnd_1053621 := by
    simpa [prefixWord, tailWord_1053621, baseEnd_1053621] using wordTrace_append hprefix tailTrace_1053621
  have hstable : (prefixWord ++ tailWord_1053621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053621).length < 2 ^ (prefixWord ++ tailWord_1053621).sum := by decide
  have hdescent : baseEnd_1053621 < baseStart_1053621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053708 : List Nat := [2, 2, 1, 2, 3, 2, 4, 7]
def baseStart_1053708 : Nat := 118140960795 + 1053708 * 2 ^ 59
def prefixEnd_1053708 : Nat := 4983230072969 + 3 ^ 40 * 1053708 * 2
def baseEnd_1053708 : Nat := 20039210129180318381633

theorem tailTrace_1053708 : CollatzResearch.WordTrace tailWord_1053708 prefixEnd_1053708 20039210129180318381633 := by
  unfold tailWord_1053708
  simp only [CollatzResearch.WordTrace]
  refine ⟨19215944033301674922120889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25621258711068899896161185 19215944033301674922120889)
  ·
    refine ⟨14411958024976256191590667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19215944033301674922120889 14411958024976256191590667)
    ·
      refine ⟨21617937037464384287386001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14411958024976256191590667 21617937037464384287386001)
      ·
        refine ⟨16213452778098288215539501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21617937037464384287386001 16213452778098288215539501)
        ·
          refine ⟨6080044791786858080827313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16213452778098288215539501 6080044791786858080827313)
          ·
            refine ⟨4560033593840143560620485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6080044791786858080827313 4560033593840143560620485)
            ·
              refine ⟨855006298845026917616341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4560033593840143560620485 855006298845026917616341)
              ·
                refine ⟨20039210129180318381633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 855006298845026917616341 20039210129180318381633)
                ·
                  rfl

theorem cell23_1053708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 7].length) (baseStart_1053708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053708 prefixEnd_1053708 := by exact prefixLift 1053708
  have htrace : WordTrace (prefixWord ++ tailWord_1053708) baseStart_1053708 baseEnd_1053708 := by
    simpa [prefixWord, tailWord_1053708, baseEnd_1053708] using wordTrace_append hprefix tailTrace_1053708
  have hstable : (prefixWord ++ tailWord_1053708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053708).length < 2 ^ (prefixWord ++ tailWord_1053708).sum := by decide
  have hdescent : baseEnd_1053708 < baseStart_1053708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053725 : List Nat := [1, 4, 2, 2, 4, 1, 9]
def baseStart_1053725 : Nat := 118140960795 + 1053725 * 2 ^ 59
def prefixEnd_1053725 : Nat := 4983230072969 + 3 ^ 40 * 1053725 * 2
def baseEnd_1053725 : Nat := 6679844477271543577673

theorem tailTrace_1053725 : CollatzResearch.WordTrace tailWord_1053725 prefixEnd_1053725 6679844477271543577673 := by
  unfold tailWord_1053725
  simp only [CollatzResearch.WordTrace]
  refine ⟨38432508107541761747610629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25621672071694507831740419 38432508107541761747610629)
  ·
    refine ⟨7206095270164080327676993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38432508107541761747610629 7206095270164080327676993)
    ·
      refine ⟨5404571452623060245757745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7206095270164080327676993 5404571452623060245757745)
      ·
        refine ⟨4053428589467295184318309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5404571452623060245757745 4053428589467295184318309)
        ·
          refine ⟨760017860525117847059683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4053428589467295184318309 760017860525117847059683)
          ·
            refine ⟨1140026790787676770589525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760017860525117847059683 1140026790787676770589525)
            ·
              refine ⟨6679844477271543577673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1140026790787676770589525 6679844477271543577673)
              ·
                rfl

theorem cell23_1053725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 9].length) (baseStart_1053725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053725 prefixEnd_1053725 := by exact prefixLift 1053725
  have htrace : WordTrace (prefixWord ++ tailWord_1053725) baseStart_1053725 baseEnd_1053725 := by
    simpa [prefixWord, tailWord_1053725, baseEnd_1053725] using wordTrace_append hprefix tailTrace_1053725
  have hstable : (prefixWord ++ tailWord_1053725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053725).length < 2 ^ (prefixWord ++ tailWord_1053725).sum := by decide
  have hdescent : baseEnd_1053725 < baseStart_1053725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053745 : List Nat := [1, 2, 2, 3, 1, 2, 2, 2, 3, 3, 2]
def baseStart_1053745 : Nat := 118140960795 + 1053745 * 2 ^ 59
def prefixEnd_1053745 : Nat := 4983230072969 + 3 ^ 40 * 1053745 * 2
def baseEnd_1053745 : Nat := 541077672272084951541421

theorem tailTrace_1053745 : CollatzResearch.WordTrace tailWord_1053745 prefixEnd_1053745 541077672272084951541421 := by
  unfold tailWord_1053745
  simp only [CollatzResearch.WordTrace]
  refine ⟨38433237567469305163338689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25622158378312870108892459 38433237567469305163338689)
  ·
    refine ⟨28824928175601978872504017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38433237567469305163338689 28824928175601978872504017)
    ·
      refine ⟨21618696131701484154378013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28824928175601978872504017 21618696131701484154378013)
      ·
        refine ⟨8107011049388056557891755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21618696131701484154378013 8107011049388056557891755)
        ·
          refine ⟨12160516574082084836837633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8107011049388056557891755 12160516574082084836837633)
          ·
            refine ⟨9120387430561563627628225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12160516574082084836837633 9120387430561563627628225)
            ·
              refine ⟨6840290572921172720721169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9120387430561563627628225 6840290572921172720721169)
              ·
                refine ⟨5130217929690879540540877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6840290572921172720721169 5130217929690879540540877)
                ·
                  refine ⟨1923831723634079827702829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5130217929690879540540877 1923831723634079827702829)
                  ·
                    refine ⟨721436896362779935388561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1923831723634079827702829 721436896362779935388561)
                    ·
                      refine ⟨541077672272084951541421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 721436896362779935388561 541077672272084951541421)
                      ·
                        rfl

theorem cell23_1053745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_1053745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053745 prefixEnd_1053745 := by exact prefixLift 1053745
  have htrace : WordTrace (prefixWord ++ tailWord_1053745) baseStart_1053745 baseEnd_1053745 := by
    simpa [prefixWord, tailWord_1053745, baseEnd_1053745] using wordTrace_append hprefix tailTrace_1053745
  have hstable : (prefixWord ++ tailWord_1053745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053745).length < 2 ^ (prefixWord ++ tailWord_1053745).sum := by decide
  have hdescent : baseEnd_1053745 < baseStart_1053745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053751 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 1, 8]
def baseStart_1053751 : Nat := 118140960795 + 1053751 * 2 ^ 59
def prefixEnd_1053751 : Nat := 4983230072969 + 3 ^ 40 * 1053751 * 2
def baseEnd_1053751 : Nat := 180360251052003976022131

theorem tailTrace_1053751 : CollatzResearch.WordTrace tailWord_1053751 prefixEnd_1053751 180360251052003976022131 := by
  unfold tailWord_1053751
  simp only [CollatzResearch.WordTrace]
  refine ⟨38433456405447568188057107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25622304270298378792038071 38433456405447568188057107)
  ·
    refine ⟨57650184608171352282085661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38433456405447568188057107 57650184608171352282085661)
    ·
      refine ⟨21618819228064257105782123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57650184608171352282085661 21618819228064257105782123)
      ·
        refine ⟨32428228842096385658673185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21618819228064257105782123 32428228842096385658673185)
        ·
          refine ⟨24321171631572289244004889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32428228842096385658673185 24321171631572289244004889)
          ·
            refine ⟨18240878723679216933003667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24321171631572289244004889 18240878723679216933003667)
            ·
              refine ⟨27361318085518825399505501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18240878723679216933003667 27361318085518825399505501)
              ·
                refine ⟨10260494282069559524814563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27361318085518825399505501 10260494282069559524814563)
                ·
                  refine ⟨15390741423104339287221845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10260494282069559524814563 15390741423104339287221845)
                  ·
                    refine ⟨180360251052003976022131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15390741423104339287221845 180360251052003976022131)
                    ·
                      rfl

theorem cell23_1053751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 8].length) (baseStart_1053751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053751 prefixEnd_1053751 := by exact prefixLift 1053751
  have htrace : WordTrace (prefixWord ++ tailWord_1053751) baseStart_1053751 baseEnd_1053751 := by
    simpa [prefixWord, tailWord_1053751, baseEnd_1053751] using wordTrace_append hprefix tailTrace_1053751
  have hstable : (prefixWord ++ tailWord_1053751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053751).length < 2 ^ (prefixWord ++ tailWord_1053751).sum := by decide
  have hdescent : baseEnd_1053751 < baseStart_1053751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053752 : List Nat := [2, 1, 2, 1, 5, 2, 1, 3, 2, 1, 3]
def baseStart_1053752 : Nat := 118140960795 + 1053752 * 2 ^ 59
def prefixEnd_1053752 : Nat := 4983230072969 + 3 ^ 40 * 1053752 * 2
def baseEnd_1053752 : Nat := 541081266636666424153889

theorem tailTrace_1053752 : CollatzResearch.WordTrace tailWord_1053752 prefixEnd_1053752 541081266636666424153889 := by
  unfold tailWord_1053752
  simp only [CollatzResearch.WordTrace]
  refine ⟨19216746439221972679421755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25622328585629296905895673 19216746439221972679421755)
  ·
    refine ⟨28825119658832959019132633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19216746439221972679421755 28825119658832959019132633)
    ·
      refine ⟨21618839744124719264349475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28825119658832959019132633 21618839744124719264349475)
      ·
        refine ⟨32428259616187078896524213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21618839744124719264349475 32428259616187078896524213)
        ·
          refine ⟨3040149339017538646549145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32428259616187078896524213 3040149339017538646549145)
          ·
            refine ⟨2280112004263153984911859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3040149339017538646549145 2280112004263153984911859)
            ·
              refine ⟨3420168006394730977367789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2280112004263153984911859 3420168006394730977367789)
              ·
                refine ⟨1282563002398024116512921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3420168006394730977367789 1282563002398024116512921)
                ·
                  refine ⟨961922251798518087384691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1282563002398024116512921 961922251798518087384691)
                  ·
                    refine ⟨1442883377697777131077037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 961922251798518087384691 1442883377697777131077037)
                    ·
                      refine ⟨541081266636666424153889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1442883377697777131077037 541081266636666424153889)
                      ·
                        rfl

theorem cell23_1053752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 2, 1, 3].length) (baseStart_1053752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053752 prefixEnd_1053752 := by exact prefixLift 1053752
  have htrace : WordTrace (prefixWord ++ tailWord_1053752) baseStart_1053752 baseEnd_1053752 := by
    simpa [prefixWord, tailWord_1053752, baseEnd_1053752] using wordTrace_append hprefix tailTrace_1053752
  have hstable : (prefixWord ++ tailWord_1053752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053752).length < 2 ^ (prefixWord ++ tailWord_1053752).sum := by decide
  have hdescent : baseEnd_1053752 < baseStart_1053752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053805 : List Nat := [1, 5, 1, 1, 2, 3, 1, 1, 2, 2, 4]
def baseStart_1053805 : Nat := 118140960795 + 1053805 * 2 ^ 59
def prefixEnd_1053805 : Nat := 4983230072969 + 3 ^ 40 * 1053805 * 2
def baseEnd_1053805 : Nat := 541108481111354716791145

theorem tailTrace_1053805 : CollatzResearch.WordTrace tailWord_1053805 prefixEnd_1053805 541108481111354716791145 := by
  unfold tailWord_1053805
  simp only [CollatzResearch.WordTrace]
  refine ⟨38435425947251935410522869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25623617298167956940348579 38435425947251935410522869)
  ·
    refine ⟨3603321182554868944736519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38435425947251935410522869 3603321182554868944736519)
    ·
      refine ⟨5404981773832303417104779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3603321182554868944736519 5404981773832303417104779)
      ·
        refine ⟨8107472660748455125657169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5404981773832303417104779 8107472660748455125657169)
        ·
          refine ⟨6080604495561341344242877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8107472660748455125657169 6080604495561341344242877)
          ·
            refine ⟨2280226685835503004091079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6080604495561341344242877 2280226685835503004091079)
            ·
              refine ⟨3420340028753254506136619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2280226685835503004091079 3420340028753254506136619)
              ·
                refine ⟨5130510043129881759204929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3420340028753254506136619 5130510043129881759204929)
                ·
                  refine ⟨3847882532347411319403697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5130510043129881759204929 3847882532347411319403697)
                  ·
                    refine ⟨2885911899260558489552773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3847882532347411319403697 2885911899260558489552773)
                    ·
                      refine ⟨541108481111354716791145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2885911899260558489552773 541108481111354716791145)
                      ·
                        rfl

theorem cell23_1053805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_1053805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053805 prefixEnd_1053805 := by exact prefixLift 1053805
  have htrace : WordTrace (prefixWord ++ tailWord_1053805) baseStart_1053805 baseEnd_1053805 := by
    simpa [prefixWord, tailWord_1053805, baseEnd_1053805] using wordTrace_append hprefix tailTrace_1053805
  have hstable : (prefixWord ++ tailWord_1053805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053805).length < 2 ^ (prefixWord ++ tailWord_1053805).sum := by decide
  have hdescent : baseEnd_1053805 < baseStart_1053805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053875 : List Nat := [1, 1, 1, 2, 3, 2, 4, 2, 3, 4]
def baseStart_1053875 : Nat := 118140960795 + 1053875 * 2 ^ 59
def prefixEnd_1053875 : Nat := 4983230072969 + 3 ^ 40 * 1053875 * 2
def baseEnd_1053875 : Nat := 180381474919056480971941

theorem tailTrace_1053875 : CollatzResearch.WordTrace tailWord_1053875 prefixEnd_1053875 180381474919056480971941 := by
  unfold tailWord_1053875
  simp only [CollatzResearch.WordTrace]
  refine ⟨38437979056998337365571079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25625319371332224910380719 38437979056998337365571079)
  ·
    refine ⟨57656968585497506048356619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38437979056998337365571079 57656968585497506048356619)
    ·
      refine ⟨86485452878246259072534929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57656968585497506048356619 86485452878246259072534929)
      ·
        refine ⟨64864089658684694304401197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86485452878246259072534929 64864089658684694304401197)
        ·
          refine ⟨24324033622006760364150449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64864089658684694304401197 24324033622006760364150449)
          ·
            refine ⟨18243025216505070273112837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24324033622006760364150449 18243025216505070273112837)
            ·
              refine ⟨3420567228094700676208657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18243025216505070273112837 3420567228094700676208657)
              ·
                refine ⟨2565425421071025507156493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3420567228094700676208657 2565425421071025507156493)
                ·
                  refine ⟨962034532901634565183685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2565425421071025507156493 962034532901634565183685)
                  ·
                    refine ⟨180381474919056480971941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 962034532901634565183685 180381474919056480971941)
                    ·
                      rfl

theorem cell23_1053875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 3, 4].length) (baseStart_1053875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053875 prefixEnd_1053875 := by exact prefixLift 1053875
  have htrace : WordTrace (prefixWord ++ tailWord_1053875) baseStart_1053875 baseEnd_1053875 := by
    simpa [prefixWord, tailWord_1053875, baseEnd_1053875] using wordTrace_append hprefix tailTrace_1053875
  have hstable : (prefixWord ++ tailWord_1053875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053875).length < 2 ^ (prefixWord ++ tailWord_1053875).sum := by decide
  have hdescent : baseEnd_1053875 < baseStart_1053875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053885 : List Nat := [1, 4, 1, 2, 1, 1, 4, 1, 1, 4, 3]
def baseStart_1053885 : Nat := 118140960795 + 1053885 * 2 ^ 59
def prefixEnd_1053885 : Nat := 4983230072969 + 3 ^ 40 * 1053885 * 2
def baseEnd_1053885 : Nat := 541149559563714403790777

theorem tailTrace_1053885 : CollatzResearch.WordTrace tailWord_1053885 prefixEnd_1053885 541149559563714403790777 := by
  unfold tailWord_1053885
  simp only [CollatzResearch.WordTrace]
  refine ⟨38438343786962109073435109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25625562524641406048956739 38438343786962109073435109)
  ·
    refine ⟨7207189460055395451269083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38438343786962109073435109 7207189460055395451269083)
    ·
      refine ⟨10810784190083093176903625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7207189460055395451269083 10810784190083093176903625)
      ·
        refine ⟨8108088142562319882677719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10810784190083093176903625 8108088142562319882677719)
        ·
          refine ⟨12162132213843479824016579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8108088142562319882677719 12162132213843479824016579)
          ·
            refine ⟨18243198320765219736024869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12162132213843479824016579 18243198320765219736024869)
            ·
              refine ⟨3420599685143478700504663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18243198320765219736024869 3420599685143478700504663)
              ·
                refine ⟨5130899527715218050756995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3420599685143478700504663 5130899527715218050756995)
                ·
                  refine ⟨7696349291572827076135493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5130899527715218050756995 7696349291572827076135493)
                  ·
                    refine ⟨1443065492169905076775405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7696349291572827076135493 1443065492169905076775405)
                    ·
                      refine ⟨541149559563714403790777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1443065492169905076775405 541149559563714403790777)
                      ·
                        rfl

theorem cell23_1053885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_1053885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053885 prefixEnd_1053885 := by exact prefixLift 1053885
  have htrace : WordTrace (prefixWord ++ tailWord_1053885) baseStart_1053885 baseEnd_1053885 := by
    simpa [prefixWord, tailWord_1053885, baseEnd_1053885] using wordTrace_append hprefix tailTrace_1053885
  have hstable : (prefixWord ++ tailWord_1053885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053885).length < 2 ^ (prefixWord ++ tailWord_1053885).sum := by decide
  have hdescent : baseEnd_1053885 < baseStart_1053885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053909 : List Nat := [1, 3, 2, 4, 1, 3, 1, 1, 3, 4]
def baseStart_1053909 : Nat := 118140960795 + 1053909 * 2 ^ 59
def prefixEnd_1053909 : Nat := 4983230072969 + 3 ^ 40 * 1053909 * 2
def baseEnd_1053909 : Nat := 180387294366474103296889

theorem tailTrace_1053909 : CollatzResearch.WordTrace tailWord_1053909 prefixEnd_1053909 180387294366474103296889 := by
  unfold tailWord_1053909
  simp only [CollatzResearch.WordTrace]
  refine ⟨38439219138875161172308781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25626146092583440781539187 38439219138875161172308781)
  ·
    refine ⟨14414707177078185439615793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38439219138875161172308781 14414707177078185439615793)
    ·
      refine ⟨10811030382808639079711845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14414707177078185439615793 10811030382808639079711845)
      ·
        refine ⟨2027068196776619827445971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10811030382808639079711845 2027068196776619827445971)
        ·
          refine ⟨3040602295164929741168957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2027068196776619827445971 3040602295164929741168957)
          ·
            refine ⟨1140225860686848652938359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3040602295164929741168957 1140225860686848652938359)
            ·
              refine ⟨1710338791030272979407539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1140225860686848652938359 1710338791030272979407539)
              ·
                refine ⟨2565508186545409469111309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1710338791030272979407539 2565508186545409469111309)
                ·
                  refine ⟨962065569954528550916741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2565508186545409469111309 962065569954528550916741)
                  ·
                    refine ⟨180387294366474103296889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 962065569954528550916741 180387294366474103296889)
                    ·
                      rfl

theorem cell23_1053909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_1053909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053909 prefixEnd_1053909 := by exact prefixLift 1053909
  have htrace : WordTrace (prefixWord ++ tailWord_1053909) baseStart_1053909 baseEnd_1053909 := by
    simpa [prefixWord, tailWord_1053909, baseEnd_1053909] using wordTrace_append hprefix tailTrace_1053909
  have hstable : (prefixWord ++ tailWord_1053909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053909).length < 2 ^ (prefixWord ++ tailWord_1053909).sum := by decide
  have hdescent : baseEnd_1053909 < baseStart_1053909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053966 : List Nat := [4, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3]
def baseStart_1053966 : Nat := 118140960795 + 1053966 * 2 ^ 59
def prefixEnd_1053966 : Nat := 4983230072969 + 3 ^ 40 * 1053966 * 2
def baseEnd_1053966 : Nat := 541191151496728586877905

theorem tailTrace_1053966 : CollatzResearch.WordTrace tailWord_1053966 prefixEnd_1053966 541191151496728586877905 := by
  unfold tailWord_1053966
  simp only [CollatzResearch.WordTrace]
  refine ⟨4805162262458582488391719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25627532066445773271422501 4805162262458582488391719)
  ·
    refine ⟨7207743393687873732587579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4805162262458582488391719 7207743393687873732587579)
    ·
      refine ⟨10811615090531810598881369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7207743393687873732587579 10811615090531810598881369)
      ·
        refine ⟨8108711317898857949161027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10811615090531810598881369 8108711317898857949161027)
        ·
          refine ⟨12163066976848286923741541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8108711317898857949161027 12163066976848286923741541)
          ·
            refine ⟨2280575058159053798201539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12163066976848286923741541 2280575058159053798201539)
            ·
              refine ⟨3420862587238580697302309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2280575058159053798201539 3420862587238580697302309)
              ·
                refine ⟨641411735107233880744183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3420862587238580697302309 641411735107233880744183)
                ·
                  refine ⟨962117602660850821116275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 641411735107233880744183 962117602660850821116275)
                  ·
                    refine ⟨1443176403991276231674413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 962117602660850821116275 1443176403991276231674413)
                    ·
                      refine ⟨541191151496728586877905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1443176403991276231674413 541191151496728586877905)
                      ·
                        rfl

theorem cell23_1053966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_1053966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053966 prefixEnd_1053966 := by exact prefixLift 1053966
  have htrace : WordTrace (prefixWord ++ tailWord_1053966) baseStart_1053966 baseEnd_1053966 := by
    simpa [prefixWord, tailWord_1053966, baseEnd_1053966] using wordTrace_append hprefix tailTrace_1053966
  have hstable : (prefixWord ++ tailWord_1053966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053966).length < 2 ^ (prefixWord ++ tailWord_1053966).sum := by decide
  have hdescent : baseEnd_1053966 < baseStart_1053966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053975 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 5]
def baseStart_1053975 : Nat := 118140960795 + 1053975 * 2 ^ 59
def prefixEnd_1053975 : Nat := 4983230072969 + 3 ^ 40 * 1053975 * 2
def baseEnd_1053975 : Nat := 541195772822619051665363

theorem tailTrace_1053975 : CollatzResearch.WordTrace tailWord_1053975 prefixEnd_1053975 541195772822619051665363 := by
  unfold tailWord_1053975
  simp only [CollatzResearch.WordTrace]
  refine ⟨38441626356636054444211379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25627750904424036296140919 38441626356636054444211379)
  ·
    refine ⟨57662439534954081666317069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38441626356636054444211379 57662439534954081666317069)
    ·
      refine ⟨21623414825607780624868901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57662439534954081666317069 21623414825607780624868901)
      ·
        refine ⟨4054390279801458867162919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21623414825607780624868901 4054390279801458867162919)
        ·
          refine ⟨6081585419702188300744379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4054390279801458867162919 6081585419702188300744379)
          ·
            refine ⟨9122378129553282451116569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6081585419702188300744379 9122378129553282451116569)
            ·
              refine ⟨6841783597164961838337427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9122378129553282451116569 6841783597164961838337427)
              ·
                refine ⟨10262675395747442757506141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6841783597164961838337427 10262675395747442757506141)
                ·
                  refine ⟨3848503273405291034064803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10262675395747442757506141 3848503273405291034064803)
                  ·
                    refine ⟨5772754910107936551097205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3848503273405291034064803 5772754910107936551097205)
                    ·
                      refine ⟨541195772822619051665363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5772754910107936551097205 541195772822619051665363)
                      ·
                        rfl

theorem cell23_1053975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_1053975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053975 prefixEnd_1053975 := by exact prefixLift 1053975
  have htrace : WordTrace (prefixWord ++ tailWord_1053975) baseStart_1053975 baseEnd_1053975 := by
    simpa [prefixWord, tailWord_1053975, baseEnd_1053975] using wordTrace_append hprefix tailTrace_1053975
  have hstable : (prefixWord ++ tailWord_1053975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053975).length < 2 ^ (prefixWord ++ tailWord_1053975).sum := by decide
  have hdescent : baseEnd_1053975 < baseStart_1053975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053989 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 5, 2, 2]
def baseStart_1053989 : Nat := 118140960795 + 1053989 * 2 ^ 59
def prefixEnd_1053989 : Nat := 4983230072969 + 3 ^ 40 * 1053989 * 2
def baseEnd_1053989 : Nat := 541202961551781996890299

theorem tailTrace_1053989 : CollatzResearch.WordTrace tailWord_1053989 prefixEnd_1053989 541202961551781996890299 := by
  unfold tailWord_1053989
  simp only [CollatzResearch.WordTrace]
  refine ⟨38442136978585334835221021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25628091319056889890147347 38442136978585334835221021)
  ·
    refine ⟨14415801366969500563207883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38442136978585334835221021 14415801366969500563207883)
    ·
      refine ⟨21623702050454250844811825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14415801366969500563207883 21623702050454250844811825)
      ·
        refine ⟨16217776537840688133608869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21623702050454250844811825 16217776537840688133608869)
        ·
          refine ⟨3040833100845129025051663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16217776537840688133608869 3040833100845129025051663)
          ·
            refine ⟨4561249651267693537577495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3040833100845129025051663 4561249651267693537577495)
            ·
              refine ⟨6841874476901540306366243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4561249651267693537577495 6841874476901540306366243)
              ·
                refine ⟨10262811715352310459549365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6841874476901540306366243 10262811715352310459549365)
                ·
                  refine ⟨962138598314279105582753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10262811715352310459549365 962138598314279105582753)
                  ·
                    refine ⟨721603948735709329187065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 962138598314279105582753 721603948735709329187065)
                    ·
                      refine ⟨541202961551781996890299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 721603948735709329187065 541202961551781996890299)
                      ·
                        rfl

theorem cell23_1053989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 5, 2, 2].length) (baseStart_1053989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053989 prefixEnd_1053989 := by exact prefixLift 1053989
  have htrace : WordTrace (prefixWord ++ tailWord_1053989) baseStart_1053989 baseEnd_1053989 := by
    simpa [prefixWord, tailWord_1053989, baseEnd_1053989] using wordTrace_append hprefix tailTrace_1053989
  have hstable : (prefixWord ++ tailWord_1053989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053989).length < 2 ^ (prefixWord ++ tailWord_1053989).sum := by decide
  have hdescent : baseEnd_1053989 < baseStart_1053989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054002 : List Nat := [3, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4]
def baseStart_1054002 : Nat := 118140960795 + 1054002 * 2 ^ 59
def prefixEnd_1054002 : Nat := 4983230072969 + 3 ^ 40 * 1054002 * 2
def baseEnd_1054002 : Nat := 541209636800290446027739

theorem tailTrace_1054002 : CollatzResearch.WordTrace tailWord_1054002 prefixEnd_1054002 541209636800290446027739 := by
  unfold tailWord_1054002
  simp only [CollatzResearch.WordTrace]
  refine ⟨9610652781884559513861065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25628407418358825370296173 9610652781884559513861065)
  ·
    refine ⟨7207989586413419635395799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9610652781884559513861065 7207989586413419635395799)
    ·
      refine ⟨10811984379620129453093699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7207989586413419635395799 10811984379620129453093699)
      ·
        refine ⟨16217976569430194179640549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10811984379620129453093699 16217976569430194179640549)
        ·
          refine ⟨3040870606768161408682603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16217976569430194179640549 3040870606768161408682603)
          ·
            refine ⟨4561305910152242113023905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3040870606768161408682603 4561305910152242113023905)
            ·
              refine ⟨3420979432614181584767929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4561305910152242113023905 3420979432614181584767929)
              ·
                refine ⟨2565734574460636188575947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3420979432614181584767929 2565734574460636188575947)
                ·
                  refine ⟨3848601861690954282863921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2565734574460636188575947 3848601861690954282863921)
                  ·
                    refine ⟨2886451396268215712147941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3848601861690954282863921 2886451396268215712147941)
                    ·
                      refine ⟨541209636800290446027739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2886451396268215712147941 541209636800290446027739)
                      ·
                        rfl

theorem cell23_1054002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_1054002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054002 prefixEnd_1054002 := by exact prefixLift 1054002
  have htrace : WordTrace (prefixWord ++ tailWord_1054002) baseStart_1054002 baseEnd_1054002 := by
    simpa [prefixWord, tailWord_1054002, baseEnd_1054002] using wordTrace_append hprefix tailTrace_1054002
  have hstable : (prefixWord ++ tailWord_1054002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054002).length < 2 ^ (prefixWord ++ tailWord_1054002).sum := by decide
  have hdescent : baseEnd_1054002 < baseStart_1054002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054039 : List Nat := [1, 1, 3, 2, 3, 4, 1, 1, 1, 3, 3]
def baseStart_1054039 : Nat := 118140960795 + 1054039 * 2 ^ 59
def prefixEnd_1054039 : Nat := 4983230072969 + 3 ^ 40 * 1054039 * 2
def baseEnd_1054039 : Nat := 541228635584506801265069

theorem tailTrace_1054039 : CollatzResearch.WordTrace tailWord_1054039 prefixEnd_1054039 541228635584506801265069 := by
  unfold tailWord_1054039
  simp only [CollatzResearch.WordTrace]
  refine ⟨38443960628404193374541171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25629307085602795583027447 38443960628404193374541171)
  ·
    refine ⟨57665940942606290061811757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38443960628404193374541171 57665940942606290061811757)
    ·
      refine ⟨21624727853477358773179409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57665940942606290061811757 21624727853477358773179409)
      ·
        refine ⟨16218545890108019079884557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21624727853477358773179409 16218545890108019079884557)
        ·
          refine ⟨6081954708790507154956709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16218545890108019079884557 6081954708790507154956709)
          ·
            refine ⟨1140366507898220091554383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6081954708790507154956709 1140366507898220091554383)
            ·
              refine ⟨1710549761847330137331575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1140366507898220091554383 1710549761847330137331575)
              ·
                refine ⟨2565824642770995205997363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1710549761847330137331575 2565824642770995205997363)
                ·
                  refine ⟨3848736964156492808996045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2565824642770995205997363 3848736964156492808996045)
                  ·
                    refine ⟨1443276361558684803373517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3848736964156492808996045 1443276361558684803373517)
                    ·
                      refine ⟨541228635584506801265069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1443276361558684803373517 541228635584506801265069)
                      ·
                        rfl

theorem cell23_1054039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_1054039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054039 prefixEnd_1054039 := by exact prefixLift 1054039
  have htrace : WordTrace (prefixWord ++ tailWord_1054039) baseStart_1054039 baseEnd_1054039 := by
    simpa [prefixWord, tailWord_1054039, baseEnd_1054039] using wordTrace_append hprefix tailTrace_1054039
  have hstable : (prefixWord ++ tailWord_1054039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054039).length < 2 ^ (prefixWord ++ tailWord_1054039).sum := by decide
  have hdescent : baseEnd_1054039 < baseStart_1054039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054065 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 1, 3, 5]
def baseStart_1054065 : Nat := 118140960795 + 1054065 * 2 ^ 59
def prefixEnd_1054065 : Nat := 4983230072969 + 3 ^ 40 * 1054065 * 2
def baseEnd_1054065 : Nat := 541241986081523699539949

theorem tailTrace_1054065 : CollatzResearch.WordTrace tailWord_1054065 prefixEnd_1054065 541241986081523699539949 := by
  unfold tailWord_1054065
  simp only [CollatzResearch.WordTrace]
  refine ⟨38444908926309999814987649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25629939284206666543325099 38444908926309999814987649)
  ·
    refine ⟨28833681694732499861240737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38444908926309999814987649 28833681694732499861240737)
    ·
      refine ⟨21625261271049374895930553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28833681694732499861240737 21625261271049374895930553)
      ·
        refine ⟨16218945953287031171947915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21625261271049374895930553 16218945953287031171947915)
        ·
          refine ⟨24328418929930546757921873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16218945953287031171947915 24328418929930546757921873)
          ·
            refine ⟨18246314197447910068441405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24328418929930546757921873 18246314197447910068441405)
            ·
              refine ⟨6842367824042966275665527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18246314197447910068441405 6842367824042966275665527)
              ·
                refine ⟨10263551736064449413498291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6842367824042966275665527 10263551736064449413498291)
                ·
                  refine ⟨15395327604096674120247437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10263551736064449413498291 15395327604096674120247437)
                  ·
                    refine ⟨5773247851536252795092789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15395327604096674120247437 5773247851536252795092789)
                    ·
                      refine ⟨541241986081523699539949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5773247851536252795092789 541241986081523699539949)
                      ·
                        rfl

theorem cell23_1054065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_1054065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054065 prefixEnd_1054065 := by exact prefixLift 1054065
  have htrace : WordTrace (prefixWord ++ tailWord_1054065) baseStart_1054065 baseEnd_1054065 := by
    simpa [prefixWord, tailWord_1054065, baseEnd_1054065] using wordTrace_append hprefix tailTrace_1054065
  have hstable : (prefixWord ++ tailWord_1054065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054065).length < 2 ^ (prefixWord ++ tailWord_1054065).sum := by decide
  have hdescent : baseEnd_1054065 < baseStart_1054065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054119 : List Nat := [1, 1, 6, 1, 1, 1, 2, 5, 5]
def baseStart_1054119 : Nat := 118140960795 + 1054119 * 2 ^ 59
def prefixEnd_1054119 : Nat := 4983230072969 + 3 ^ 40 * 1054119 * 2
def baseEnd_1054119 : Nat := 60141079337429609807189

theorem tailTrace_1054119 : CollatzResearch.WordTrace tailWord_1054119 prefixEnd_1054119 60141079337429609807189 := by
  unfold tailWord_1054119
  simp only [CollatzResearch.WordTrace]
  refine ⟨38446878468114367037453411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25631252312076244691635607 38446878468114367037453411)
  ·
    refine ⟨57670317702171550556180117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38446878468114367037453411 57670317702171550556180117)
    ·
      refine ⟨2703296142289291432320943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 57670317702171550556180117 2703296142289291432320943)
      ·
        refine ⟨4054944213433937148481415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2703296142289291432320943 4054944213433937148481415)
        ·
          refine ⟨6082416320150905722722123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4054944213433937148481415 6082416320150905722722123)
          ·
            refine ⟨9123624480226358584083185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6082416320150905722722123 9123624480226358584083185)
            ·
              refine ⟨6842718360169768938062389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9123624480226358584083185 6842718360169768938062389)
              ·
                refine ⟨641504846265915837943349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6842718360169768938062389 641504846265915837943349)
                ·
                  refine ⟨60141079337429609807189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 641504846265915837943349 60141079337429609807189)
                  ·
                    rfl

theorem cell23_1054119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 5, 5].length) (baseStart_1054119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054119 prefixEnd_1054119 := by exact prefixLift 1054119
  have htrace : WordTrace (prefixWord ++ tailWord_1054119) baseStart_1054119 baseEnd_1054119 := by
    simpa [prefixWord, tailWord_1054119, baseEnd_1054119] using wordTrace_append hprefix tailTrace_1054119
  have hstable : (prefixWord ++ tailWord_1054119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054119).length < 2 ^ (prefixWord ++ tailWord_1054119).sum := by decide
  have hdescent : baseEnd_1054119 < baseStart_1054119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054152 : List Nat := [2, 1, 3, 1, 3, 1, 2, 2, 1, 3, 4]
def baseStart_1054152 : Nat := 118140960795 + 1054152 * 2 ^ 59
def prefixEnd_1054152 : Nat := 4983230072969 + 3 ^ 40 * 1054152 * 2
def baseEnd_1054152 : Nat := 541286658898464859152049

theorem tailTrace_1054152 : CollatzResearch.WordTrace tailWord_1054152 prefixEnd_1054152 541286658898464859152049 := by
  unfold tailWord_1054152
  simp only [CollatzResearch.WordTrace]
  refine ⟨19224041038497406836702355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25632054717996542448936473 19224041038497406836702355)
  ·
    refine ⟨28836061557746110255053533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19224041038497406836702355 28836061557746110255053533)
    ·
      refine ⟨10813523084154791345645075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28836061557746110255053533 10813523084154791345645075)
      ·
        refine ⟨16220284626232187018467613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10813523084154791345645075 16220284626232187018467613)
        ·
          refine ⟨6082606734837070131925355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16220284626232187018467613 6082606734837070131925355)
          ·
            refine ⟨9123910102255605197888033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6082606734837070131925355 9123910102255605197888033)
            ·
              refine ⟨6842932576691703898416025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9123910102255605197888033 6842932576691703898416025)
              ·
                refine ⟨5132199432518777923812019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6842932576691703898416025 5132199432518777923812019)
                ·
                  refine ⟨7698299148778166885718029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5132199432518777923812019 7698299148778166885718029)
                  ·
                    refine ⟨2886862180791812582144261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7698299148778166885718029 2886862180791812582144261)
                    ·
                      refine ⟨541286658898464859152049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2886862180791812582144261 541286658898464859152049)
                      ·
                        rfl

theorem cell23_1054152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_1054152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054152 prefixEnd_1054152 := by exact prefixLift 1054152
  have htrace : WordTrace (prefixWord ++ tailWord_1054152) baseStart_1054152 baseEnd_1054152 := by
    simpa [prefixWord, tailWord_1054152, baseEnd_1054152] using wordTrace_append hprefix tailTrace_1054152
  have hstable : (prefixWord ++ tailWord_1054152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054152).length < 2 ^ (prefixWord ++ tailWord_1054152).sum := by decide
  have hdescent : baseEnd_1054152 < baseStart_1054152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054166 : List Nat := [5, 2, 1, 1, 1, 2, 3, 1, 2, 5]
def baseStart_1054166 : Nat := 118140960795 + 1054166 * 2 ^ 59
def prefixEnd_1054166 : Nat := 4983230072969 + 3 ^ 40 * 1054166 * 2
def baseEnd_1054166 : Nat := 180431282542542601458995

theorem tailTrace_1054166 : CollatzResearch.WordTrace tailWord_1054166 prefixEnd_1054166 180431282542542601458995 := by
  unfold tailWord_1054166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2403037043684005879025897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25632395132629396042942901 2403037043684005879025897)
  ·
    refine ⟨1802277782763004409269423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2403037043684005879025897 1802277782763004409269423)
    ·
      refine ⟨2703416674144506613904135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1802277782763004409269423 2703416674144506613904135)
      ·
        refine ⟨4055125011216759920856203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2703416674144506613904135 4055125011216759920856203)
        ·
          refine ⟨6082687516825139881284305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4055125011216759920856203 6082687516825139881284305)
          ·
            refine ⟨4562015637618854910963229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6082687516825139881284305 4562015637618854910963229)
            ·
              refine ⟨1710755864107070591611211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4562015637618854910963229 1710755864107070591611211)
              ·
                refine ⟨2566133796160605887416817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1710755864107070591611211 2566133796160605887416817)
                ·
                  refine ⟨1924600347120454415562613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2566133796160605887416817 1924600347120454415562613)
                  ·
                    refine ⟨180431282542542601458995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1924600347120454415562613 180431282542542601458995)
                    ·
                      rfl

theorem cell23_1054166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_1054166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054166 prefixEnd_1054166 := by exact prefixLift 1054166
  have htrace : WordTrace (prefixWord ++ tailWord_1054166) baseStart_1054166 baseEnd_1054166 := by
    simpa [prefixWord, tailWord_1054166, baseEnd_1054166] using wordTrace_append hprefix tailTrace_1054166
  have hstable : (prefixWord ++ tailWord_1054166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054166).length < 2 ^ (prefixWord ++ tailWord_1054166).sum := by decide
  have hdescent : baseEnd_1054166 < baseStart_1054166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054169 : List Nat := [1, 2, 1, 2, 4, 2, 3, 1, 2, 1, 4]
def baseStart_1054169 : Nat := 118140960795 + 1054169 * 2 ^ 59
def prefixEnd_1054169 : Nat := 4983230072969 + 3 ^ 40 * 1054169 * 2
def baseEnd_1054169 : Nat := 541295388069591292639471

theorem tailTrace_1054169 : CollatzResearch.WordTrace tailWord_1054169 prefixEnd_1054169 541295388069591292639471 := by
  unfold tailWord_1054169
  simp only [CollatzResearch.WordTrace]
  refine ⟨38448702117933225576773561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25632468078622150384515707 38448702117933225576773561)
  ·
    refine ⟨28836526588449919182580171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38448702117933225576773561 28836526588449919182580171)
    ·
      refine ⟨43254789882674878773870257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28836526588449919182580171 43254789882674878773870257)
      ·
        refine ⟨32441092412006159080402693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43254789882674878773870257 32441092412006159080402693)
        ·
          refine ⟨6082704827251154827575505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32441092412006159080402693 6082704827251154827575505)
          ·
            refine ⟨4562028620438366120681629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6082704827251154827575505 4562028620438366120681629)
            ·
              refine ⟨1710760732664387295255611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4562028620438366120681629 1710760732664387295255611)
              ·
                refine ⟨2566141098996580942883417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1710760732664387295255611 2566141098996580942883417)
                ·
                  refine ⟨1924605824247435707162563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2566141098996580942883417 1924605824247435707162563)
                  ·
                    refine ⟨2886908736371153560743845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1924605824247435707162563 2886908736371153560743845)
                    ·
                      refine ⟨541295388069591292639471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2886908736371153560743845 541295388069591292639471)
                      ·
                        rfl

theorem cell23_1054169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 1, 4].length) (baseStart_1054169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054169 prefixEnd_1054169 := by exact prefixLift 1054169
  have htrace : WordTrace (prefixWord ++ tailWord_1054169) baseStart_1054169 baseEnd_1054169 := by
    simpa [prefixWord, tailWord_1054169, baseEnd_1054169] using wordTrace_append hprefix tailTrace_1054169
  have hstable : (prefixWord ++ tailWord_1054169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054169).length < 2 ^ (prefixWord ++ tailWord_1054169).sum := by decide
  have hdescent : baseEnd_1054169 < baseStart_1054169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054192 : List Nat := [2, 1, 1, 1, 3, 5, 1, 1, 8]
def baseStart_1054192 : Nat := 118140960795 + 1054192 * 2 ^ 59
def prefixEnd_1054192 : Nat := 4983230072969 + 3 ^ 40 * 1054192 * 2
def baseEnd_1054192 : Nat := 60145244236071633627985

theorem tailTrace_1054192 : CollatzResearch.WordTrace tailWord_1054192 prefixEnd_1054192 60145244236071633627985 := by
  unfold tailWord_1054192
  simp only [CollatzResearch.WordTrace]
  refine ⟨19224770498424950252430415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25633027331233267003240553 19224770498424950252430415)
  ·
    refine ⟨28837155747637425378645623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19224770498424950252430415 28837155747637425378645623)
    ·
      refine ⟨43255733621456138067968435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28837155747637425378645623 43255733621456138067968435)
      ·
        refine ⟨64883600432184207101952653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43255733621456138067968435 64883600432184207101952653)
        ·
          refine ⟨24331350162069077663232245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64883600432184207101952653 24331350162069077663232245)
          ·
            refine ⟨2281064077693976030928023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24331350162069077663232245 2281064077693976030928023)
            ·
              refine ⟨3421596116540964046392035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2281064077693976030928023 3421596116540964046392035)
              ·
                refine ⟨5132394174811446069588053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3421596116540964046392035 5132394174811446069588053)
                ·
                  refine ⟨60145244236071633627985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5132394174811446069588053 60145244236071633627985)
                  ·
                    rfl

theorem cell23_1054192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 8].length) (baseStart_1054192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054192 prefixEnd_1054192 := by exact prefixLift 1054192
  have htrace : WordTrace (prefixWord ++ tailWord_1054192) baseStart_1054192 baseEnd_1054192 := by
    simpa [prefixWord, tailWord_1054192, baseEnd_1054192] using wordTrace_append hprefix tailTrace_1054192
  have hstable : (prefixWord ++ tailWord_1054192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054192).length < 2 ^ (prefixWord ++ tailWord_1054192).sum := by decide
  have hdescent : baseEnd_1054192 < baseStart_1054192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054239 : List Nat := [1, 1, 2, 4, 1, 1, 4, 3, 1, 5]
def baseStart_1054239 : Nat := 118140960795 + 1054239 * 2 ^ 59
def prefixEnd_1054239 : Nat := 4983230072969 + 3 ^ 40 * 1054239 * 2
def baseEnd_1054239 : Nat := 180443777238468672921383

theorem tailTrace_1054239 : CollatzResearch.WordTrace tailWord_1054239 prefixEnd_1054239 180443777238468672921383 := by
  unfold tailWord_1054239
  simp only [CollatzResearch.WordTrace]
  refine ⟨38451255227679627531821771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25634170151786418354547847 38451255227679627531821771)
  ·
    refine ⟨57676882841519441297732657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38451255227679627531821771 57676882841519441297732657)
    ·
      refine ⟨43257662131139580973299493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57676882841519441297732657 43257662131139580973299493)
      ·
        refine ⟨8110811649588671432493655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43257662131139580973299493 8110811649588671432493655)
        ·
          refine ⟨12166217474383007148740483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8110811649588671432493655 12166217474383007148740483)
          ·
            refine ⟨18249326211574510723110725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12166217474383007148740483 18249326211574510723110725)
            ·
              refine ⟨3421748664670220760583261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18249326211574510723110725 3421748664670220760583261)
              ·
                refine ⟨1283155749251332785218723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3421748664670220760583261 1283155749251332785218723)
                ·
                  refine ⟨1924733623876999177828085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1283155749251332785218723 1924733623876999177828085)
                  ·
                    refine ⟨180443777238468672921383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1924733623876999177828085 180443777238468672921383)
                    ·
                      rfl

theorem cell23_1054239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 5].length) (baseStart_1054239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054239 prefixEnd_1054239 := by exact prefixLift 1054239
  have htrace : WordTrace (prefixWord ++ tailWord_1054239) baseStart_1054239 baseEnd_1054239 := by
    simpa [prefixWord, tailWord_1054239, baseEnd_1054239] using wordTrace_append hprefix tailTrace_1054239
  have hstable : (prefixWord ++ tailWord_1054239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054239).length < 2 ^ (prefixWord ++ tailWord_1054239).sum := by decide
  have hdescent : baseEnd_1054239 < baseStart_1054239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054282 : List Nat := [3, 1, 2, 1, 1, 3, 1, 11]
def baseStart_1054282 : Nat := 118140960795 + 1054282 * 2 ^ 59
def prefixEnd_1054282 : Nat := 4983230072969 + 3 ^ 40 * 1054282 * 2
def baseEnd_1054282 : Nat := 20050126347538864834313

theorem tailTrace_1054282 : CollatzResearch.WordTrace tailWord_1054282 prefixEnd_1054282 20050126347538864834313 := by
  unfold tailWord_1054282
  simp only [CollatzResearch.WordTrace]
  refine ⟨9613205891630961468909275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25635215711015897250424733 9613205891630961468909275)
  ·
    refine ⟨14419808837446442203363913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9613205891630961468909275 14419808837446442203363913)
    ·
      refine ⟨10814856628084831652522935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14419808837446442203363913 10814856628084831652522935)
      ·
        refine ⟨16222284942127247478784403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10814856628084831652522935 16222284942127247478784403)
        ·
          refine ⟨24333427413190871218176605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16222284942127247478784403 24333427413190871218176605)
          ·
            refine ⟨9125035279946576706816227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24333427413190871218176605 9125035279946576706816227)
            ·
              refine ⟨13687552919919865060224341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9125035279946576706816227 13687552919919865060224341)
              ·
                refine ⟨20050126347538864834313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 13687552919919865060224341 20050126347538864834313)
                ·
                  rfl

theorem cell23_1054282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 11].length) (baseStart_1054282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054282 prefixEnd_1054282 := by exact prefixLift 1054282
  have htrace : WordTrace (prefixWord ++ tailWord_1054282) baseStart_1054282 baseEnd_1054282 := by
    simpa [prefixWord, tailWord_1054282, baseEnd_1054282] using wordTrace_append hprefix tailTrace_1054282
  have hstable : (prefixWord ++ tailWord_1054282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054282).length < 2 ^ (prefixWord ++ tailWord_1054282).sum := by decide
  have hdescent : baseEnd_1054282 < baseStart_1054282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054289 : List Nat := [1, 2, 2, 1, 3, 2, 3, 2, 1, 2, 4]
def baseStart_1054289 : Nat := 118140960795 + 1054289 * 2 ^ 59
def prefixEnd_1054289 : Nat := 4983230072969 + 3 ^ 40 * 1054289 * 2
def baseEnd_1054289 : Nat := 541357005748130823138919

theorem tailTrace_1054289 : CollatzResearch.WordTrace tailWord_1054289 prefixEnd_1054289 541357005748130823138919 := by
  unfold tailWord_1054289
  simp only [CollatzResearch.WordTrace]
  refine ⟨38453078877498486071141921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25635385918332324047427947 38453078877498486071141921)
  ·
    refine ⟨28839809158123864553356441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38453078877498486071141921 28839809158123864553356441)
    ·
      refine ⟨21629856868592898415017331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28839809158123864553356441 21629856868592898415017331)
      ·
        refine ⟨32444785302889347622525997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21629856868592898415017331 32444785302889347622525997)
        ·
          refine ⟨12166794488583505358447249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32444785302889347622525997 12166794488583505358447249)
          ·
            refine ⟨9125095866437629018835437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12166794488583505358447249 9125095866437629018835437)
            ·
              refine ⟨3421910949914110882063289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9125095866437629018835437 3421910949914110882063289)
              ·
                refine ⟨2566433212435583161547467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3421910949914110882063289 2566433212435583161547467)
                ·
                  refine ⟨3849649818653374742321201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2566433212435583161547467 3849649818653374742321201)
                  ·
                    refine ⟨2887237363990031056740901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3849649818653374742321201 2887237363990031056740901)
                    ·
                      refine ⟨541357005748130823138919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2887237363990031056740901 541357005748130823138919)
                      ·
                        rfl

theorem cell23_1054289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_1054289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054289 prefixEnd_1054289 := by exact prefixLift 1054289
  have htrace : WordTrace (prefixWord ++ tailWord_1054289) baseStart_1054289 baseEnd_1054289 := by
    simpa [prefixWord, tailWord_1054289, baseEnd_1054289] using wordTrace_append hprefix tailTrace_1054289
  have hstable : (prefixWord ++ tailWord_1054289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054289).length < 2 ^ (prefixWord ++ tailWord_1054289).sum := by decide
  have hdescent : baseEnd_1054289 < baseStart_1054289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054336 : List Nat := [2, 1, 1, 2, 1, 4, 1, 3, 3, 3, 2]
def baseStart_1054336 : Nat := 118140960795 + 1054336 * 2 ^ 59
def prefixEnd_1054336 : Nat := 4983230072969 + 3 ^ 40 * 1054336 * 2
def baseEnd_1054336 : Nat := 541381139338892139251203

theorem tailTrace_1054336 : CollatzResearch.WordTrace tailWord_1054336 prefixEnd_1054336 541381139338892139251203 := by
  unfold tailWord_1054336
  simp only [CollatzResearch.WordTrace]
  refine ⟨19227396554164106549051431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25636528738885475398735241 19227396554164106549051431)
  ·
    refine ⟨28841094831246159823577147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19227396554164106549051431 28841094831246159823577147)
    ·
      refine ⟨43261642246869239735365721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28841094831246159823577147 43261642246869239735365721)
      ·
        refine ⟨32446231685151929801524291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43261642246869239735365721 32446231685151929801524291)
        ·
          refine ⟨48669347527727894702286437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32446231685151929801524291 48669347527727894702286437)
          ·
            refine ⟨9125502661448980256678707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48669347527727894702286437 9125502661448980256678707)
            ·
              refine ⟨13688253992173470385018061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9125502661448980256678707 13688253992173470385018061)
              ·
                refine ⟨5133095247065051394381773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13688253992173470385018061 5133095247065051394381773)
                ·
                  refine ⟨1924910717649394272893165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5133095247065051394381773 1924910717649394272893165)
                  ·
                    refine ⟨721841519118522852334937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1924910717649394272893165 721841519118522852334937)
                    ·
                      refine ⟨541381139338892139251203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 721841519118522852334937 541381139338892139251203)
                      ·
                        rfl

theorem cell23_1054336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 3, 3, 2].length) (baseStart_1054336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054336 prefixEnd_1054336 := by exact prefixLift 1054336
  have htrace : WordTrace (prefixWord ++ tailWord_1054336) baseStart_1054336 baseEnd_1054336 := by
    simpa [prefixWord, tailWord_1054336, baseEnd_1054336] using wordTrace_append hprefix tailTrace_1054336
  have hstable : (prefixWord ++ tailWord_1054336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054336).length < 2 ^ (prefixWord ++ tailWord_1054336).sum := by decide
  have hdescent : baseEnd_1054336 < baseStart_1054336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054344 : List Nat := [2, 1, 3, 5, 1, 1, 2, 3, 1, 2, 2]
def baseStart_1054344 : Nat := 118140960795 + 1054344 * 2 ^ 59
def prefixEnd_1054344 : Nat := 4983230072969 + 3 ^ 40 * 1054344 * 2
def baseEnd_1054344 : Nat := 541385247184128107951167

theorem tailTrace_1054344 : CollatzResearch.WordTrace tailWord_1054344 prefixEnd_1054344 541385247184128107951167 := by
  unfold tailWord_1054344
  simp only [CollatzResearch.WordTrace]
  refine ⟨19227542446149615232197043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25636723261532820309596057 19227542446149615232197043)
  ·
    refine ⟨28841313669224422848295565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19227542446149615232197043 28841313669224422848295565)
    ·
      refine ⟨10815492625959158568110837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28841313669224422848295565 10815492625959158568110837)
      ·
        refine ⟨1013952433683671115760391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10815492625959158568110837 1013952433683671115760391)
        ·
          refine ⟨1520928650525506673640587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1013952433683671115760391 1520928650525506673640587)
          ·
            refine ⟨2281392975788260010460881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1520928650525506673640587 2281392975788260010460881)
            ·
              refine ⟨1711044731841195007845661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2281392975788260010460881 1711044731841195007845661)
              ·
                refine ⟨641641774440448127942123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1711044731841195007845661 641641774440448127942123)
                ·
                  refine ⟨962462661660672191913185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 641641774440448127942123 962462661660672191913185)
                  ·
                    refine ⟨721846996245504143934889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 962462661660672191913185 721846996245504143934889)
                    ·
                      refine ⟨541385247184128107951167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 721846996245504143934889 541385247184128107951167)
                      ·
                        rfl

theorem cell23_1054344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_1054344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054344 prefixEnd_1054344 := by exact prefixLift 1054344
  have htrace : WordTrace (prefixWord ++ tailWord_1054344) baseStart_1054344 baseEnd_1054344 := by
    simpa [prefixWord, tailWord_1054344, baseEnd_1054344] using wordTrace_append hprefix tailTrace_1054344
  have hstable : (prefixWord ++ tailWord_1054344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054344).length < 2 ^ (prefixWord ++ tailWord_1054344).sum := by decide
  have hdescent : baseEnd_1054344 < baseStart_1054344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054359 : List Nat := [1, 1, 3, 3, 2, 2, 1, 2, 2, 6]
def baseStart_1054359 : Nat := 118140960795 + 1054359 * 2 ^ 59
def prefixEnd_1054359 : Nat := 4983230072969 + 3 ^ 40 * 1054359 * 2
def baseEnd_1054359 : Nat := 180464316464648516421199

theorem tailTrace_1054359 : CollatzResearch.WordTrace tailWord_1054359 prefixEnd_1054359 180464316464648516421199 := by
  unfold tailWord_1054359
  simp only [CollatzResearch.WordTrace]
  refine ⟨38455631987244888026190131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25637087991496592017460087 38455631987244888026190131)
  ·
    refine ⟨57683447980867332039285197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38455631987244888026190131 57683447980867332039285197)
    ·
      refine ⟨21631292992825249514731949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57683447980867332039285197 21631292992825249514731949)
      ·
        refine ⟨8111734872309468568024481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21631292992825249514731949 8111734872309468568024481)
        ·
          refine ⟨6083801154232101426018361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8111734872309468568024481 6083801154232101426018361)
          ·
            refine ⟨4562850865674076069513771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6083801154232101426018361 4562850865674076069513771)
            ·
              refine ⟨6844276298511114104270657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4562850865674076069513771 6844276298511114104270657)
              ·
                refine ⟨5133207223883335578202993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6844276298511114104270657 5133207223883335578202993)
                ·
                  refine ⟨3849905417912501683652245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5133207223883335578202993 3849905417912501683652245)
                  ·
                    refine ⟨180464316464648516421199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3849905417912501683652245 180464316464648516421199)
                    ·
                      rfl

theorem cell23_1054359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 6].length) (baseStart_1054359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054359 prefixEnd_1054359 := by exact prefixLift 1054359
  have htrace : WordTrace (prefixWord ++ tailWord_1054359) baseStart_1054359 baseEnd_1054359 := by
    simpa [prefixWord, tailWord_1054359, baseEnd_1054359] using wordTrace_append hprefix tailTrace_1054359
  have hstable : (prefixWord ++ tailWord_1054359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054359).length < 2 ^ (prefixWord ++ tailWord_1054359).sum := by decide
  have hdescent : baseEnd_1054359 < baseStart_1054359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054360 : List Nat := [2, 1, 2, 4, 1, 4, 1, 2, 2, 1, 3]
def baseStart_1054360 : Nat := 118140960795 + 1054360 * 2 ^ 59
def prefixEnd_1054360 : Nat := 4983230072969 + 3 ^ 40 * 1054360 * 2
def baseEnd_1054360 : Nat := 541393462874600045351093

theorem tailTrace_1054360 : CollatzResearch.WordTrace tailWord_1054360 prefixEnd_1054360 541393462874600045351093 := by
  unfold tailWord_1054360
  simp only [CollatzResearch.WordTrace]
  refine ⟨19227834230120632598488267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25637112306827510131317689 19227834230120632598488267)
  ·
    refine ⟨28841751345180948897732401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19227834230120632598488267 28841751345180948897732401)
    ·
      refine ⟨21631313508885711673299301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28841751345180948897732401 21631313508885711673299301)
      ·
        refine ⟨4055871282916070938743619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21631313508885711673299301 4055871282916070938743619)
        ·
          refine ⟨6083806924374106408115429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4055871282916070938743619 6083806924374106408115429)
          ·
            refine ⟨1140713798320144951521643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6083806924374106408115429 1140713798320144951521643)
            ·
              refine ⟨1711070697480217427282465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1140713798320144951521643 1711070697480217427282465)
              ·
                refine ⟨1283303023110163070461849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1711070697480217427282465 1283303023110163070461849)
                ·
                  refine ⟨962477267332622302846387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1283303023110163070461849 962477267332622302846387)
                  ·
                    refine ⟨1443715900998933454269581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 962477267332622302846387 1443715900998933454269581)
                    ·
                      refine ⟨541393462874600045351093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1443715900998933454269581 541393462874600045351093)
                      ·
                        rfl

theorem cell23_1054360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_1054360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054360 prefixEnd_1054360 := by exact prefixLift 1054360
  have htrace : WordTrace (prefixWord ++ tailWord_1054360) baseStart_1054360 baseEnd_1054360 := by
    simpa [prefixWord, tailWord_1054360, baseEnd_1054360] using wordTrace_append hprefix tailTrace_1054360
  have hstable : (prefixWord ++ tailWord_1054360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054360).length < 2 ^ (prefixWord ++ tailWord_1054360).sum := by decide
  have hdescent : baseEnd_1054360 < baseStart_1054360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054423 : List Nat := [1, 1, 3, 2, 1, 3, 5, 2, 5]
def baseStart_1054423 : Nat := 118140960795 + 1054423 * 2 ^ 59
def prefixEnd_1054423 : Nat := 4983230072969 + 3 ^ 40 * 1054423 * 2
def baseEnd_1054423 : Nat := 60158423572870366540367

theorem tailTrace_1054423 : CollatzResearch.WordTrace tailWord_1054423 prefixEnd_1054423 60158423572870366540367 := by
  unfold tailWord_1054423
  simp only [CollatzResearch.WordTrace]
  refine ⟨38457966259013026956519923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25638644172675351304346615 38457966259013026956519923)
  ·
    refine ⟨57686949388519540434779885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38457966259013026956519923 57686949388519540434779885)
    ·
      refine ⟨21632606020694827663042457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57686949388519540434779885 21632606020694827663042457)
      ·
        refine ⟨16224454515521120747281843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21632606020694827663042457 16224454515521120747281843)
        ·
          refine ⟨24336681773281681120922765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16224454515521120747281843 24336681773281681120922765)
          ·
            refine ⟨9126255664980630420346037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24336681773281681120922765 9126255664980630420346037)
            ·
              refine ⟨855586468591934101907441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9126255664980630420346037 855586468591934101907441)
              ·
                refine ⟨641689851443950576430581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 855586468591934101907441 641689851443950576430581)
                ·
                  refine ⟨60158423572870366540367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 641689851443950576430581 60158423572870366540367)
                  ·
                    rfl

theorem cell23_1054423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 2, 5].length) (baseStart_1054423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054423 prefixEnd_1054423 := by exact prefixLift 1054423
  have htrace : WordTrace (prefixWord ++ tailWord_1054423) baseStart_1054423 baseEnd_1054423 := by
    simpa [prefixWord, tailWord_1054423, baseEnd_1054423] using wordTrace_append hprefix tailTrace_1054423
  have hstable : (prefixWord ++ tailWord_1054423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054423).length < 2 ^ (prefixWord ++ tailWord_1054423).sum := by decide
  have hdescent : baseEnd_1054423 < baseStart_1054423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054456 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 3, 6, 2]
def baseStart_1054456 : Nat := 118140960795 + 1054456 * 2 ^ 59
def prefixEnd_1054456 : Nat := 4983230072969 + 3 ^ 40 * 1054456 * 2
def baseEnd_1054456 : Nat := 541442757017431669750651

theorem tailTrace_1054456 : CollatzResearch.WordTrace tailWord_1054456 prefixEnd_1054456 541442757017431669750651 := by
  unfold tailWord_1054456
  simp only [CollatzResearch.WordTrace]
  refine ⟨19229584933946736796235611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25639446578595649061647481 19229584933946736796235611)
  ·
    refine ⟨28844377400920105194353417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19229584933946736796235611 28844377400920105194353417)
    ·
      refine ⟨21633283050690078895765063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28844377400920105194353417 21633283050690078895765063)
      ·
        refine ⟨32449924576035118343647595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21633283050690078895765063 32449924576035118343647595)
        ·
          refine ⟨48674886864052677515471393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32449924576035118343647595 48674886864052677515471393)
          ·
            refine ⟨36506165148039508136603545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48674886864052677515471393 36506165148039508136603545)
            ·
              refine ⟨27379623861029631102452659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36506165148039508136603545 27379623861029631102452659)
              ·
                refine ⟨41069435791544446653678989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27379623861029631102452659 41069435791544446653678989)
                ·
                  refine ⟨15401038421829167495129621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41069435791544446653678989 15401038421829167495129621)
                  ·
                    refine ⟨721923676023242226334201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15401038421829167495129621 721923676023242226334201)
                    ·
                      refine ⟨541442757017431669750651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 721923676023242226334201 541442757017431669750651)
                      ·
                        rfl

theorem cell23_1054456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 3, 6, 2].length) (baseStart_1054456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054456 prefixEnd_1054456 := by exact prefixLift 1054456
  have htrace : WordTrace (prefixWord ++ tailWord_1054456) baseStart_1054456 baseEnd_1054456 := by
    simpa [prefixWord, tailWord_1054456, baseEnd_1054456] using wordTrace_append hprefix tailTrace_1054456
  have hstable : (prefixWord ++ tailWord_1054456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054456).length < 2 ^ (prefixWord ++ tailWord_1054456).sum := by decide
  have hdescent : baseEnd_1054456 < baseStart_1054456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054496 : List Nat := [2, 1, 1, 5, 1, 1, 1, 5, 6]
def baseStart_1054496 : Nat := 118140960795 + 1054496 * 2 ^ 59
def prefixEnd_1054496 : Nat := 4983230072969 + 3 ^ 40 * 1054496 * 2
def baseEnd_1054496 : Nat := 60162588471512390361163

theorem tailTrace_1054496 : CollatzResearch.WordTrace tailWord_1054496 prefixEnd_1054496 60162588471512390361163 := by
  unfold tailWord_1054496
  simp only [CollatzResearch.WordTrace]
  refine ⟨19230314393874280211963671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25640419191832373615951561 19230314393874280211963671)
  ·
    refine ⟨28845471590811420317945507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19230314393874280211963671 28845471590811420317945507)
    ·
      refine ⟨43268207386217130476918261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28845471590811420317945507 43268207386217130476918261)
      ·
        refine ⟨4056394442457855982211087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43268207386217130476918261 4056394442457855982211087)
        ·
          refine ⟨6084591663686783973316631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4056394442457855982211087 6084591663686783973316631)
          ·
            refine ⟨9126887495530175959974947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6084591663686783973316631 9126887495530175959974947)
            ·
              refine ⟨13690331243295263939962421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9126887495530175959974947 13690331243295263939962421)
              ·
                refine ⟨1283468554058930994371477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13690331243295263939962421 1283468554058930994371477)
                ·
                  refine ⟨60162588471512390361163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1283468554058930994371477 60162588471512390361163)
                  ·
                    rfl

theorem cell23_1054496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 6].length) (baseStart_1054496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054496 prefixEnd_1054496 := by exact prefixLift 1054496
  have htrace : WordTrace (prefixWord ++ tailWord_1054496) baseStart_1054496 baseEnd_1054496 := by
    simpa [prefixWord, tailWord_1054496, baseEnd_1054496] using wordTrace_append hprefix tailTrace_1054496
  have hstable : (prefixWord ++ tailWord_1054496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054496).length < 2 ^ (prefixWord ++ tailWord_1054496).sum := by decide
  have hdescent : baseEnd_1054496 < baseStart_1054496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054510 : List Nat := [4, 1, 3, 2, 2, 1, 1, 1, 1, 4, 3]
def baseStart_1054510 : Nat := 118140960795 + 1054510 * 2 ^ 59
def prefixEnd_1054510 : Nat := 4983230072969 + 3 ^ 40 * 1054510 * 2
def baseEnd_1054510 : Nat := 541470484972774458475403

theorem tailTrace_1054510 : CollatzResearch.WordTrace tailWord_1054510 prefixEnd_1054510 541470484972774458475403 := by
  unfold tailWord_1054510
  simp only [CollatzResearch.WordTrace]
  refine ⟨4807642426212230101867123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25640759606465227209957989 4807642426212230101867123)
  ·
    refine ⟨7211463639318345152800685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4807642426212230101867123 7211463639318345152800685)
    ·
      refine ⟨2704298864744379432300257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7211463639318345152800685 2704298864744379432300257)
      ·
        refine ⟨2028224148558284574225193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2704298864744379432300257 2028224148558284574225193)
        ·
          refine ⟨1521168111418713430668895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2028224148558284574225193 1521168111418713430668895)
          ·
            refine ⟨2281752167128070146003343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1521168111418713430668895 2281752167128070146003343)
            ·
              refine ⟨3422628250692105219005015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2281752167128070146003343 3422628250692105219005015)
              ·
                refine ⟨5133942376038157828507523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3422628250692105219005015 5133942376038157828507523)
                ·
                  refine ⟨7700913564057236742761285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5133942376038157828507523 7700913564057236742761285)
                  ·
                    refine ⟨1443921293260731889267741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7700913564057236742761285 1443921293260731889267741)
                    ·
                      refine ⟨541470484972774458475403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1443921293260731889267741 541470484972774458475403)
                      ·
                        rfl

theorem cell23_1054510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_1054510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054510 prefixEnd_1054510 := by exact prefixLift 1054510
  have htrace : WordTrace (prefixWord ++ tailWord_1054510) baseStart_1054510 baseEnd_1054510 := by
    simpa [prefixWord, tailWord_1054510, baseEnd_1054510] using wordTrace_append hprefix tailTrace_1054510
  have hstable : (prefixWord ++ tailWord_1054510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054510).length < 2 ^ (prefixWord ++ tailWord_1054510).sum := by decide
  have hdescent : baseEnd_1054510 < baseStart_1054510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054517 : List Nat := [1, 3, 3, 1, 4, 1, 2, 3, 1, 4]
def baseStart_1054517 : Nat := 118140960795 + 1054517 * 2 ^ 59
def prefixEnd_1054517 : Nat := 4983230072969 + 3 ^ 40 * 1054517 * 2
def baseEnd_1054517 : Nat := 180491359779118643695957

theorem tailTrace_1054517 : CollatzResearch.WordTrace tailWord_1054517 prefixEnd_1054517 180491359779118643695957 := by
  unfold tailWord_1054517
  simp only [CollatzResearch.WordTrace]
  refine ⟨38461394720672481010441805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25640929813781654006961203 38461394720672481010441805)
  ·
    refine ⟨14423023020252180378915677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38461394720672481010441805 14423023020252180378915677)
    ·
      refine ⟨5408633632594567642093379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14423023020252180378915677 5408633632594567642093379)
      ·
        refine ⟨8112950448891851463140069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5408633632594567642093379 8112950448891851463140069)
        ·
          refine ⟨1521178209167222149338763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8112950448891851463140069 1521178209167222149338763)
          ·
            refine ⟨2281767313750833224008145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1521178209167222149338763 2281767313750833224008145)
            ·
              refine ⟨1711325485313124918006109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2281767313750833224008145 1711325485313124918006109)
              ·
                refine ⟨641747056992421844252291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1711325485313124918006109 641747056992421844252291)
                ·
                  refine ⟨962620585488632766378437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 641747056992421844252291 962620585488632766378437)
                  ·
                    refine ⟨180491359779118643695957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 962620585488632766378437 180491359779118643695957)
                    ·
                      rfl

theorem cell23_1054517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_1054517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054517 prefixEnd_1054517 := by exact prefixLift 1054517
  have htrace : WordTrace (prefixWord ++ tailWord_1054517) baseStart_1054517 baseEnd_1054517 := by
    simpa [prefixWord, tailWord_1054517, baseEnd_1054517] using wordTrace_append hprefix tailTrace_1054517
  have hstable : (prefixWord ++ tailWord_1054517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054517).length < 2 ^ (prefixWord ++ tailWord_1054517).sum := by decide
  have hdescent : baseEnd_1054517 < baseStart_1054517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054533 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 4, 3, 2]
def baseStart_1054533 : Nat := 118140960795 + 1054533 * 2 ^ 59
def prefixEnd_1054533 : Nat := 4983230072969 + 3 ^ 40 * 1054533 * 2
def baseEnd_1054533 : Nat := 541482295027827868487797

theorem tailTrace_1054533 : CollatzResearch.WordTrace tailWord_1054533 prefixEnd_1054533 541482295027827868487797 := by
  unfold tailWord_1054533
  simp only [CollatzResearch.WordTrace]
  refine ⟨38461978288614515743024253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25641318859076343828682835 38461978288614515743024253)
  ·
    refine ⟨14423241858230443403634095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38461978288614515743024253 14423241858230443403634095)
    ·
      refine ⟨21634862787345665105451143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14423241858230443403634095 21634862787345665105451143)
      ·
        refine ⟨32452294181018497658176715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21634862787345665105451143 32452294181018497658176715)
        ·
          refine ⟨48678441271527746487265073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32452294181018497658176715 48678441271527746487265073)
          ·
            refine ⟨36508830953645809865448805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48678441271527746487265073 36508830953645809865448805)
            ·
              refine ⟨6845405803808589349771651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36508830953645809865448805 6845405803808589349771651)
              ·
                refine ⟨10268108705712884024657477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6845405803808589349771651 10268108705712884024657477)
                ·
                  refine ⟨1925270382321165754623277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10268108705712884024657477 1925270382321165754623277)
                  ·
                    refine ⟨721976393370437157983729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1925270382321165754623277 721976393370437157983729)
                    ·
                      refine ⟨541482295027827868487797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 721976393370437157983729 541482295027827868487797)
                      ·
                        rfl

theorem cell23_1054533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 3, 2].length) (baseStart_1054533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054533 prefixEnd_1054533 := by exact prefixLift 1054533
  have htrace : WordTrace (prefixWord ++ tailWord_1054533) baseStart_1054533 baseEnd_1054533 := by
    simpa [prefixWord, tailWord_1054533, baseEnd_1054533] using wordTrace_append hprefix tailTrace_1054533
  have hstable : (prefixWord ++ tailWord_1054533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054533).length < 2 ^ (prefixWord ++ tailWord_1054533).sum := by decide
  have hdescent : baseEnd_1054533 < baseStart_1054533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054534 : List Nat := [6, 1, 1, 2, 1, 1, 2, 4, 1, 4]
def baseStart_1054534 : Nat := 118140960795 + 1054534 * 2 ^ 59
def prefixEnd_1054534 : Nat := 4983230072969 + 3 ^ 40 * 1054534 * 2
def baseEnd_1054534 : Nat := 180494269502827454858431

theorem tailTrace_1054534 : CollatzResearch.WordTrace tailWord_1054534 prefixEnd_1054534 180494269502827454858431 := by
  unfold tailWord_1054534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1201937961300340403556583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25641343174407261942540437 1201937961300340403556583)
  ·
    refine ⟨1802906941950510605334875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1201937961300340403556583 1802906941950510605334875)
    ·
      refine ⟨2704360412925765908002313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1802906941950510605334875 2704360412925765908002313)
      ·
        refine ⟨2028270309694324431001735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2704360412925765908002313 2028270309694324431001735)
        ·
          refine ⟨3042405464541486646502603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2028270309694324431001735 3042405464541486646502603)
          ·
            refine ⟨4563608196812229969753905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3042405464541486646502603 4563608196812229969753905)
            ·
              refine ⟨3422706147609172477315429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4563608196812229969753905 3422706147609172477315429)
              ·
                refine ⟨641757402676719839496643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3422706147609172477315429 641757402676719839496643)
                ·
                  refine ⟨962636104015079759244965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 641757402676719839496643 962636104015079759244965)
                  ·
                    refine ⟨180494269502827454858431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 962636104015079759244965 180494269502827454858431)
                    ·
                      rfl

theorem cell23_1054534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_1054534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054534 prefixEnd_1054534 := by exact prefixLift 1054534
  have htrace : WordTrace (prefixWord ++ tailWord_1054534) baseStart_1054534 baseEnd_1054534 := by
    simpa [prefixWord, tailWord_1054534, baseEnd_1054534] using wordTrace_append hprefix tailTrace_1054534
  have hstable : (prefixWord ++ tailWord_1054534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054534).length < 2 ^ (prefixWord ++ tailWord_1054534).sum := by decide
  have hdescent : baseEnd_1054534 < baseStart_1054534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054539 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 1, 12]
def baseStart_1054539 : Nat := 118140960795 + 1054539 * 2 ^ 59
def prefixEnd_1054539 : Nat := 4983230072969 + 3 ^ 40 * 1054539 * 2
def baseEnd_1054539 : Nat := 180495125303918281670923

theorem tailTrace_1054539 : CollatzResearch.WordTrace tailWord_1054539 prefixEnd_1054539 180495125303918281670923 := by
  unfold tailWord_1054539
  simp only [CollatzResearch.WordTrace]
  refine ⟨38462197126592778767742671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25641464751061852511828447 38462197126592778767742671)
  ·
    refine ⟨57693295689889168151614007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38462197126592778767742671 57693295689889168151614007)
    ·
      refine ⟨86539943534833752227421011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57693295689889168151614007 86539943534833752227421011)
      ·
        refine ⟨129809915302250628341131517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86539943534833752227421011 129809915302250628341131517)
        ·
          refine ⟨48678718238343985627924319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129809915302250628341131517 48678718238343985627924319)
          ·
            refine ⟨73018077357515978441886479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48678718238343985627924319 73018077357515978441886479)
            ·
              refine ⟨109527116036273967662829719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73018077357515978441886479 109527116036273967662829719)
              ·
                refine ⟨164290674054410951494244579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109527116036273967662829719 164290674054410951494244579)
                ·
                  refine ⟨246436011081616427241366869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164290674054410951494244579 246436011081616427241366869)
                  ·
                    refine ⟨180495125303918281670923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 246436011081616427241366869 180495125303918281670923)
                    ·
                      rfl

theorem cell23_1054539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 12].length) (baseStart_1054539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054539 prefixEnd_1054539 := by exact prefixLift 1054539
  have htrace : WordTrace (prefixWord ++ tailWord_1054539) baseStart_1054539 baseEnd_1054539 := by
    simpa [prefixWord, tailWord_1054539, baseEnd_1054539] using wordTrace_append hprefix tailTrace_1054539
  have hstable : (prefixWord ++ tailWord_1054539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054539).length < 2 ^ (prefixWord ++ tailWord_1054539).sum := by decide
  have hdescent : baseEnd_1054539 < baseStart_1054539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054573 : List Nat := [1, 5, 1, 1, 1, 1, 3, 2, 4, 4]
def baseStart_1054573 : Nat := 118140960795 + 1054573 * 2 ^ 59
def prefixEnd_1054573 : Nat := 4983230072969 + 3 ^ 40 * 1054573 * 2
def baseEnd_1054573 : Nat := 180500944751335903995871

theorem tailTrace_1054573 : CollatzResearch.WordTrace tailWord_1054573 prefixEnd_1054573 180500944751335903995871 := by
  unfold tailWord_1054573
  simp only [CollatzResearch.WordTrace]
  refine ⟨38463437208469602574480373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25642291472313068382986915 38463437208469602574480373)
  ·
    refine ⟨3605947238294025241357535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38463437208469602574480373 3605947238294025241357535)
    ·
      refine ⟨5408920857441037862036303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3605947238294025241357535 5408920857441037862036303)
      ·
        refine ⟨8113381286161556793054455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5408920857441037862036303 8113381286161556793054455)
        ·
          refine ⟨12170071929242335189581683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8113381286161556793054455 12170071929242335189581683)
          ·
            refine ⟨18255107893863502784372525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12170071929242335189581683 18255107893863502784372525)
            ·
              refine ⟨6845665460198813544139697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18255107893863502784372525 6845665460198813544139697)
              ·
                refine ⟨5134249095149110158104773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6845665460198813544139697 5134249095149110158104773)
                ·
                  refine ⟨962671705340458154644645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5134249095149110158104773 962671705340458154644645)
                  ·
                    refine ⟨180500944751335903995871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 962671705340458154644645 180500944751335903995871)
                    ·
                      rfl

theorem cell23_1054573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_1054573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054573 prefixEnd_1054573 := by exact prefixLift 1054573
  have htrace : WordTrace (prefixWord ++ tailWord_1054573) baseStart_1054573 baseEnd_1054573 := by
    simpa [prefixWord, tailWord_1054573, baseEnd_1054573] using wordTrace_append hprefix tailTrace_1054573
  have hstable : (prefixWord ++ tailWord_1054573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054573).length < 2 ^ (prefixWord ++ tailWord_1054573).sum := by decide
  have hdescent : baseEnd_1054573 < baseStart_1054573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054574 : List Nat := [4, 1, 2, 3, 1, 1, 3, 3, 1, 1, 3]
def baseStart_1054574 : Nat := 118140960795 + 1054574 * 2 ^ 59
def prefixEnd_1054574 : Nat := 4983230072969 + 3 ^ 40 * 1054574 * 2
def baseEnd_1054574 : Nat := 541503347734662208075109

theorem tailTrace_1054574 : CollatzResearch.WordTrace tailWord_1054574 prefixEnd_1054574 541503347734662208075109 := by
  unfold tailWord_1054574
  simp only [CollatzResearch.WordTrace]
  refine ⟨4807934210183247468158347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25642315787643986496844517 4807934210183247468158347)
  ·
    refine ⟨7211901315274871202237521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4807934210183247468158347 7211901315274871202237521)
    ·
      refine ⟨5408925986456153401678141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7211901315274871202237521 5408925986456153401678141)
      ·
        refine ⟨2028347244921057525629303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5408925986456153401678141 2028347244921057525629303)
        ·
          refine ⟨3042520867381586288443955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2028347244921057525629303 3042520867381586288443955)
          ·
            refine ⟨4563781301072379432665933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3042520867381586288443955 4563781301072379432665933)
            ·
              refine ⟨1711417987902142287249725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4563781301072379432665933 1711417987902142287249725)
              ·
                refine ⟨641781745463303357718647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1711417987902142287249725 641781745463303357718647)
                ·
                  refine ⟨962672618194955036577971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 641781745463303357718647 962672618194955036577971)
                  ·
                    refine ⟨1444008927292432554866957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 962672618194955036577971 1444008927292432554866957)
                    ·
                      refine ⟨541503347734662208075109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1444008927292432554866957 541503347734662208075109)
                      ·
                        rfl

theorem cell23_1054574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_1054574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054574 prefixEnd_1054574 := by exact prefixLift 1054574
  have htrace : WordTrace (prefixWord ++ tailWord_1054574) baseStart_1054574 baseEnd_1054574 := by
    simpa [prefixWord, tailWord_1054574, baseEnd_1054574] using wordTrace_append hprefix tailTrace_1054574
  have hstable : (prefixWord ++ tailWord_1054574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054574).length < 2 ^ (prefixWord ++ tailWord_1054574).sum := by decide
  have hdescent : baseEnd_1054574 < baseStart_1054574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054576 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 4]
def baseStart_1054576 : Nat := 118140960795 + 1054576 * 2 ^ 59
def prefixEnd_1054576 : Nat := 4983230072969 + 3 ^ 40 * 1054576 * 2
def baseEnd_1054576 : Nat := 541504374695971200250099

theorem tailTrace_1054576 : CollatzResearch.WordTrace tailWord_1054576 prefixEnd_1054576 541504374695971200250099 := by
  unfold tailWord_1054576
  simp only [CollatzResearch.WordTrace]
  refine ⟨19231773313729367043419791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25642364418305822724559721 19231773313729367043419791)
  ·
    refine ⟨28847659970594050565129687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19231773313729367043419791 28847659970594050565129687)
    ·
      refine ⟨43271489955891075847694531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28847659970594050565129687 43271489955891075847694531)
      ·
        refine ⟨64907234933836613771541797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43271489955891075847694531 64907234933836613771541797)
        ·
          refine ⟨12170106550094365082164087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64907234933836613771541797 12170106550094365082164087)
          ·
            refine ⟨18255159825141547623246131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12170106550094365082164087 18255159825141547623246131)
            ·
              refine ⟨27382739737712321434869197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18255159825141547623246131 27382739737712321434869197)
              ·
                refine ⟨10268527401642120538075949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27382739737712321434869197 10268527401642120538075949)
                ·
                  refine ⟨3850697775615795201778481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10268527401642120538075949 3850697775615795201778481)
                  ·
                    refine ⟨2888023331711846401333861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3850697775615795201778481 2888023331711846401333861)
                    ·
                      refine ⟨541504374695971200250099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2888023331711846401333861 541504374695971200250099)
                      ·
                        rfl

theorem cell23_1054576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 4].length) (baseStart_1054576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054576 prefixEnd_1054576 := by exact prefixLift 1054576
  have htrace : WordTrace (prefixWord ++ tailWord_1054576) baseStart_1054576 baseEnd_1054576 := by
    simpa [prefixWord, tailWord_1054576, baseEnd_1054576] using wordTrace_append hprefix tailTrace_1054576
  have hstable : (prefixWord ++ tailWord_1054576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054576).length < 2 ^ (prefixWord ++ tailWord_1054576).sum := by decide
  have hdescent : baseEnd_1054576 < baseStart_1054576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054613 : List Nat := [1, 3, 2, 1, 1, 3, 2, 3, 1, 3, 3]
def baseStart_1054613 : Nat := 118140960795 + 1054613 * 2 ^ 59
def prefixEnd_1054613 : Nat := 4983230072969 + 3 ^ 40 * 1054613 * 2
def baseEnd_1054613 : Nat := 541523373480187555487429

theorem tailTrace_1054613 : CollatzResearch.WordTrace tailWord_1054613 prefixEnd_1054613 541523373480187555487429 := by
  unfold tailWord_1054613
  simp only [CollatzResearch.WordTrace]
  refine ⟨38464896128324689405936493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25643264085549792937290995 38464896128324689405936493)
  ·
    refine ⟨14424336048121758527226185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38464896128324689405936493 14424336048121758527226185)
    ·
      refine ⟨10818252036091318895419639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14424336048121758527226185 10818252036091318895419639)
      ·
        refine ⟨16227378054136978343129459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10818252036091318895419639 16227378054136978343129459)
        ·
          refine ⟨24341067081205467514694189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16227378054136978343129459 24341067081205467514694189)
          ·
            refine ⟨9127900155452050318010321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24341067081205467514694189 9127900155452050318010321)
            ·
              refine ⟨6845925116589037738507741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9127900155452050318010321 6845925116589037738507741)
              ·
                refine ⟨2567221918720889151940403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6845925116589037738507741 2567221918720889151940403)
                ·
                  refine ⟨3850832878081333727910605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2567221918720889151940403 3850832878081333727910605)
                  ·
                    refine ⟨1444062329280500147966477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3850832878081333727910605 1444062329280500147966477)
                    ·
                      refine ⟨541523373480187555487429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1444062329280500147966477 541523373480187555487429)
                      ·
                        rfl

theorem cell23_1054613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_1054613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054613 prefixEnd_1054613 := by exact prefixLift 1054613
  have htrace : WordTrace (prefixWord ++ tailWord_1054613) baseStart_1054613 baseEnd_1054613 := by
    simpa [prefixWord, tailWord_1054613, baseEnd_1054613] using wordTrace_append hprefix tailTrace_1054613
  have hstable : (prefixWord ++ tailWord_1054613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054613).length < 2 ^ (prefixWord ++ tailWord_1054613).sum := by decide
  have hdescent : baseEnd_1054613 < baseStart_1054613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054614 : List Nat := [5, 3, 1, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_1054614 : Nat := 118140960795 + 1054614 * 2 ^ 59
def prefixEnd_1054614 : Nat := 4983230072969 + 3 ^ 40 * 1054614 * 2
def baseEnd_1054614 : Nat := 541523886960842051574925

theorem tailTrace_1054614 : CollatzResearch.WordTrace tailWord_1054614 prefixEnd_1054614 541523886960842051574925 := by
  unfold tailWord_1054614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2404058287582566661045181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25643288400880711051148597 2404058287582566661045181)
  ·
    refine ⟨901521857843462497891943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2404058287582566661045181 901521857843462497891943)
    ·
      refine ⟨1352282786765193746837915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 901521857843462497891943 1352282786765193746837915)
      ·
        refine ⟨2028424180147790620256873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1352282786765193746837915 2028424180147790620256873)
        ·
          refine ⟨1521318135110842965192655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2028424180147790620256873 1521318135110842965192655)
          ·
            refine ⟨2281977202666264447788983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1521318135110842965192655 2281977202666264447788983)
            ·
              refine ⟨3422965803999396671683475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2281977202666264447788983 3422965803999396671683475)
              ·
                refine ⟨5134448705999095007525213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3422965803999396671683475 5134448705999095007525213)
                ·
                  refine ⟨1925418264749660627821955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5134448705999095007525213 1925418264749660627821955)
                  ·
                    refine ⟨2888127397124490941732933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1925418264749660627821955 2888127397124490941732933)
                    ·
                      refine ⟨541523886960842051574925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2888127397124490941732933 541523886960842051574925)
                      ·
                        rfl

theorem cell23_1054614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_1054614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054614 prefixEnd_1054614 := by exact prefixLift 1054614
  have htrace : WordTrace (prefixWord ++ tailWord_1054614) baseStart_1054614 baseEnd_1054614 := by
    simpa [prefixWord, tailWord_1054614, baseEnd_1054614] using wordTrace_append hprefix tailTrace_1054614
  have hstable : (prefixWord ++ tailWord_1054614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054614).length < 2 ^ (prefixWord ++ tailWord_1054614).sum := by decide
  have hdescent : baseEnd_1054614 < baseStart_1054614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054636 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 4]
def baseStart_1054636 : Nat := 118140960795 + 1054636 * 2 ^ 59
def prefixEnd_1054636 : Nat := 4983230072969 + 3 ^ 40 * 1054636 * 2
def baseEnd_1054636 : Nat := 541535183535240965499823

theorem tailTrace_1054636 : CollatzResearch.WordTrace tailWord_1054636 prefixEnd_1054636 541535183535240965499823 := by
  unfold tailWord_1054636
  simp only [CollatzResearch.WordTrace]
  refine ⟨19232867503620682167011881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25643823338160909556015841 19232867503620682167011881)
  ·
    refine ⟨14424650627715511625258911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19232867503620682167011881 14424650627715511625258911)
    ·
      refine ⟨21636975941573267437888367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14424650627715511625258911 21636975941573267437888367)
      ·
        refine ⟨32455463912359901156832551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21636975941573267437888367 32455463912359901156832551)
        ·
          refine ⟨48683195868539851735248827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32455463912359901156832551 48683195868539851735248827)
          ·
            refine ⟨73024793802809777602873241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48683195868539851735248827 73024793802809777602873241)
            ·
              refine ⟨54768595352107333202154931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73024793802809777602873241 54768595352107333202154931)
              ·
                refine ⟨82152893028160999803232397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54768595352107333202154931 82152893028160999803232397)
                ·
                  refine ⟨30807334885560374926212149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82152893028160999803232397 30807334885560374926212149)
                  ·
                    refine ⟨2888187645521285149332389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30807334885560374926212149 2888187645521285149332389)
                    ·
                      refine ⟨541535183535240965499823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2888187645521285149332389 541535183535240965499823)
                      ·
                        rfl

theorem cell23_1054636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_1054636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054636 prefixEnd_1054636 := by exact prefixLift 1054636
  have htrace : WordTrace (prefixWord ++ tailWord_1054636) baseStart_1054636 baseEnd_1054636 := by
    simpa [prefixWord, tailWord_1054636, baseEnd_1054636] using wordTrace_append hprefix tailTrace_1054636
  have hstable : (prefixWord ++ tailWord_1054636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054636).length < 2 ^ (prefixWord ++ tailWord_1054636).sum := by decide
  have hdescent : baseEnd_1054636 < baseStart_1054636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054653 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 2, 3, 4]
def baseStart_1054653 : Nat := 118140960795 + 1054653 * 2 ^ 59
def prefixEnd_1054653 : Nat := 4983230072969 + 3 ^ 40 * 1054653 * 2
def baseEnd_1054653 : Nat := 541543912706367398987245

theorem tailTrace_1054653 : CollatzResearch.WordTrace tailWord_1054653 prefixEnd_1054653 541543912706367398987245 := by
  unfold tailWord_1054653
  simp only [CollatzResearch.WordTrace]
  refine ⟨38466355048179776237392613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25644236698786517491595075 38466355048179776237392613)
  ·
    refine ⟨7212441571533708044511115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38466355048179776237392613 7212441571533708044511115)
    ·
      refine ⟨10818662357300562066766673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7212441571533708044511115 10818662357300562066766673)
      ·
        refine ⟨8113996767975421550075005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10818662357300562066766673 8113996767975421550075005)
        ·
          refine ⟨3042748787990783081278127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8113996767975421550075005 3042748787990783081278127)
          ·
            refine ⟨4564123181986174621917191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3042748787990783081278127 4564123181986174621917191)
            ·
              refine ⟨6846184772979261932875787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4564123181986174621917191 6846184772979261932875787)
              ·
                refine ⟨10269277159468892899313681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6846184772979261932875787 10269277159468892899313681)
                ·
                  refine ⟨7701957869601669674485261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10269277159468892899313681 7701957869601669674485261)
                  ·
                    refine ⟨2888234201100626127931973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7701957869601669674485261 2888234201100626127931973)
                    ·
                      refine ⟨541543912706367398987245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2888234201100626127931973 541543912706367398987245)
                      ·
                        rfl

theorem cell23_1054653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_1054653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054653 prefixEnd_1054653 := by exact prefixLift 1054653
  have htrace : WordTrace (prefixWord ++ tailWord_1054653) baseStart_1054653 baseEnd_1054653 := by
    simpa [prefixWord, tailWord_1054653, baseEnd_1054653] using wordTrace_append hprefix tailTrace_1054653
  have hstable : (prefixWord ++ tailWord_1054653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054653).length < 2 ^ (prefixWord ++ tailWord_1054653).sum := by decide
  have hdescent : baseEnd_1054653 < baseStart_1054653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054703 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 4, 3, 3]
def baseStart_1054703 : Nat := 118140960795 + 1054703 * 2 ^ 59
def prefixEnd_1054703 : Nat := 4983230072969 + 3 ^ 40 * 1054703 * 2
def baseEnd_1054703 : Nat := 541569586739092203362015

theorem tailTrace_1054703 : CollatzResearch.WordTrace tailWord_1054703 prefixEnd_1054703 541569586739092203362015 := by
  unfold tailWord_1054703
  simp only [CollatzResearch.WordTrace]
  refine ⟨38468178697998634776712763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25645452465332423184475175 38468178697998634776712763)
  ·
    refine ⟨57702268046997952165069145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38468178697998634776712763 57702268046997952165069145)
    ·
      refine ⟨43276701035248464123801859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57702268046997952165069145 43276701035248464123801859)
      ·
        refine ⟨64915051552872696185702789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43276701035248464123801859 64915051552872696185702789)
        ·
          refine ⟨12171572166163630534819273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64915051552872696185702789 12171572166163630534819273)
          ·
            refine ⟨9128679124622722901114455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12171572166163630534819273 9128679124622722901114455)
            ·
              refine ⟨13693018686934084351671683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9128679124622722901114455 13693018686934084351671683)
              ·
                refine ⟨20539528030401126527507525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13693018686934084351671683 20539528030401126527507525)
                ·
                  refine ⟨3851161505700211223907661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20539528030401126527507525 3851161505700211223907661)
                  ·
                    refine ⟨1444185564637579208965373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3851161505700211223907661 1444185564637579208965373)
                    ·
                      refine ⟨541569586739092203362015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1444185564637579208965373 541569586739092203362015)
                      ·
                        rfl

theorem cell23_1054703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 3, 3].length) (baseStart_1054703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054703 prefixEnd_1054703 := by exact prefixLift 1054703
  have htrace : WordTrace (prefixWord ++ tailWord_1054703) baseStart_1054703 baseEnd_1054703 := by
    simpa [prefixWord, tailWord_1054703, baseEnd_1054703] using wordTrace_append hprefix tailTrace_1054703
  have hstable : (prefixWord ++ tailWord_1054703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054703).length < 2 ^ (prefixWord ++ tailWord_1054703).sum := by decide
  have hdescent : baseEnd_1054703 < baseStart_1054703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054763 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 3, 4, 3]
def baseStart_1054763 : Nat := 118140960795 + 1054763 * 2 ^ 59
def prefixEnd_1054763 : Nat := 4983230072969 + 3 ^ 40 * 1054763 * 2
def baseEnd_1054763 : Nat := 541600395578361968611739

theorem tailTrace_1054763 : CollatzResearch.WordTrace tailWord_1054763 prefixEnd_1054763 541600395578361968611739 := by
  unfold tailWord_1054763
  simp only [CollatzResearch.WordTrace]
  refine ⟨38470367077781265023896943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25646911385187510015931295 38470367077781265023896943)
  ·
    refine ⟨57705550616671897535845415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38470367077781265023896943 57705550616671897535845415)
    ·
      refine ⟨86558325925007846303768123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57705550616671897535845415 86558325925007846303768123)
      ·
        refine ⟨129837488887511769455652185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86558325925007846303768123 129837488887511769455652185)
        ·
          refine ⟨97378116665633827091739139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129837488887511769455652185 97378116665633827091739139)
          ·
            refine ⟨146067174998450740637608709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97378116665633827091739139 146067174998450740637608709)
            ·
              refine ⟨27387595312209513869551633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 146067174998450740637608709 27387595312209513869551633)
              ·
                refine ⟨20540696484157135402163725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27387595312209513869551633 20540696484157135402163725)
                ·
                  refine ⟨7702761181558925775811397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20540696484157135402163725 7702761181558925775811397)
                  ·
                    refine ⟨1444267721542298582964637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7702761181558925775811397 1444267721542298582964637)
                    ·
                      refine ⟨541600395578361968611739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1444267721542298582964637 541600395578361968611739)
                      ·
                        rfl

theorem cell23_1054763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 4, 3].length) (baseStart_1054763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054763 prefixEnd_1054763 := by exact prefixLift 1054763
  have htrace : WordTrace (prefixWord ++ tailWord_1054763) baseStart_1054763 baseEnd_1054763 := by
    simpa [prefixWord, tailWord_1054763, baseEnd_1054763] using wordTrace_append hprefix tailTrace_1054763
  have hstable : (prefixWord ++ tailWord_1054763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054763).length < 2 ^ (prefixWord ++ tailWord_1054763).sum := by decide
  have hdescent : baseEnd_1054763 < baseStart_1054763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054773 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 2, 1, 6]
def baseStart_1054773 : Nat := 118140960795 + 1054773 * 2 ^ 59
def prefixEnd_1054773 : Nat := 4983230072969 + 3 ^ 40 * 1054773 * 2
def baseEnd_1054773 : Nat := 541605530384906929486693

theorem tailTrace_1054773 : CollatzResearch.WordTrace tailWord_1054773 prefixEnd_1054773 541605530384906929486693 := by
  unfold tailWord_1054773
  simp only [CollatzResearch.WordTrace]
  refine ⟨38470731807745036731760973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25647154538496691154507315 38470731807745036731760973)
  ·
    refine ⟨14426524427904388774410365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38470731807745036731760973 14426524427904388774410365)
    ·
      refine ⟨5409946660464145790403887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14426524427904388774410365 5409946660464145790403887)
      ·
        refine ⟨8114919990696218685605831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5409946660464145790403887 8114919990696218685605831)
        ·
          refine ⟨12172379986044328028408747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8114919990696218685605831 12172379986044328028408747)
          ·
            refine ⟨18258569979066492042613121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12172379986044328028408747 18258569979066492042613121)
            ·
              refine ⟨13693927484299869031959841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18258569979066492042613121 13693927484299869031959841)
              ·
                refine ⟨10270445613224901773969881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13693927484299869031959841 10270445613224901773969881)
                ·
                  refine ⟨7702834209918676330477411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10270445613224901773969881 7702834209918676330477411)
                  ·
                    refine ⟨11554251314878014495716117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7702834209918676330477411 11554251314878014495716117)
                    ·
                      refine ⟨541605530384906929486693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11554251314878014495716117 541605530384906929486693)
                      ·
                        rfl

theorem cell23_1054773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_1054773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054773 prefixEnd_1054773 := by exact prefixLift 1054773
  have htrace : WordTrace (prefixWord ++ tailWord_1054773) baseStart_1054773 baseEnd_1054773 := by
    simpa [prefixWord, tailWord_1054773, baseEnd_1054773] using wordTrace_append hprefix tailTrace_1054773
  have hstable : (prefixWord ++ tailWord_1054773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054773).length < 2 ^ (prefixWord ++ tailWord_1054773).sum := by decide
  have hdescent : baseEnd_1054773 < baseStart_1054773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054780 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 4, 2, 3]
def baseStart_1054780 : Nat := 118140960795 + 1054780 * 2 ^ 59
def prefixEnd_1054780 : Nat := 4983230072969 + 3 ^ 40 * 1054780 * 2
def baseEnd_1054780 : Nat := 541609124749488402099161

theorem tailTrace_1054780 : CollatzResearch.WordTrace tailWord_1054780 prefixEnd_1054780 541609124749488402099161 := by
  unfold tailWord_1054780
  simp only [CollatzResearch.WordTrace]
  refine ⟨19235493559359838463632897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25647324745813117951510529 19235493559359838463632897)
  ·
    refine ⟨14426620169519878847724673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19235493559359838463632897 14426620169519878847724673)
    ·
      refine ⟨10819965127139909135793505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14426620169519878847724673 10819965127139909135793505)
      ·
        refine ⟨8114973845354931851845129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10819965127139909135793505 8114973845354931851845129)
        ·
          refine ⟨6086230384016198888883847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8114973845354931851845129 6086230384016198888883847)
          ·
            refine ⟨9129345576024298333325771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6086230384016198888883847 9129345576024298333325771)
            ·
              refine ⟨13694018364036447499988657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9129345576024298333325771 13694018364036447499988657)
              ·
                refine ⟨10270513773027335624991493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13694018364036447499988657 10270513773027335624991493)
                ·
                  refine ⟨1925721332442625429685905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10270513773027335624991493 1925721332442625429685905)
                  ·
                    refine ⟨1444290999331969072264429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1925721332442625429685905 1444290999331969072264429)
                    ·
                      refine ⟨541609124749488402099161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1444290999331969072264429 541609124749488402099161)
                      ·
                        rfl

theorem cell23_1054780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_1054780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054780 prefixEnd_1054780 := by exact prefixLift 1054780
  have htrace : WordTrace (prefixWord ++ tailWord_1054780) baseStart_1054780 baseEnd_1054780 := by
    simpa [prefixWord, tailWord_1054780, baseEnd_1054780] using wordTrace_append hprefix tailTrace_1054780
  have hstable : (prefixWord ++ tailWord_1054780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054780).length < 2 ^ (prefixWord ++ tailWord_1054780).sum := by decide
  have hdescent : baseEnd_1054780 < baseStart_1054780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054821 : List Nat := [1, 3, 1, 3, 2, 4, 2, 2, 1, 4]
def baseStart_1054821 : Nat := 118140960795 + 1054821 * 2 ^ 59
def prefixEnd_1054821 : Nat := 4983230072969 + 3 ^ 40 * 1054821 * 2
def baseEnd_1054821 : Nat := 180543392485440913895491

theorem tailTrace_1054821 : CollatzResearch.WordTrace tailWord_1054821 prefixEnd_1054821 180543392485440913895491 := by
  unfold tailWord_1054821
  simp only [CollatzResearch.WordTrace]
  refine ⟨38472482511571140929508317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25648321674380760619672211 38472482511571140929508317)
  ·
    refine ⟨14427180941839177848565619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38472482511571140929508317 14427180941839177848565619)
    ·
      refine ⟨21640771412758766772848429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14427180941839177848565619 21640771412758766772848429)
      ·
        refine ⟨8115289279784537539818161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21640771412758766772848429 8115289279784537539818161)
        ·
          refine ⟨6086466959838403154863621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8115289279784537539818161 6086466959838403154863621)
          ·
            refine ⟨1141212554969700591536929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6086466959838403154863621 1141212554969700591536929)
            ·
              refine ⟨855909416227275443652697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1141212554969700591536929 855909416227275443652697)
              ·
                refine ⟨641932062170456582739523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 855909416227275443652697 641932062170456582739523)
                ·
                  refine ⟨962898093255684874109285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 641932062170456582739523 962898093255684874109285)
                  ·
                    refine ⟨180543392485440913895491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 962898093255684874109285 180543392485440913895491)
                    ·
                      rfl

theorem cell23_1054821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 2, 1, 4].length) (baseStart_1054821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054821 prefixEnd_1054821 := by exact prefixLift 1054821
  have htrace : WordTrace (prefixWord ++ tailWord_1054821) baseStart_1054821 baseEnd_1054821 := by
    simpa [prefixWord, tailWord_1054821, baseEnd_1054821] using wordTrace_append hprefix tailTrace_1054821
  have hstable : (prefixWord ++ tailWord_1054821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054821).length < 2 ^ (prefixWord ++ tailWord_1054821).sum := by decide
  have hdescent : baseEnd_1054821 < baseStart_1054821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054830 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 5, 5]
def baseStart_1054830 : Nat := 118140960795 + 1054830 * 2 ^ 59
def prefixEnd_1054830 : Nat := 4983230072969 + 3 ^ 40 * 1054830 * 2
def baseEnd_1054830 : Nat := 180544932927404402157977

theorem tailTrace_1054830 : CollatzResearch.WordTrace tailWord_1054830 prefixEnd_1054830 180544932927404402157977 := by
  unfold tailWord_1054830
  simp only [CollatzResearch.WordTrace]
  refine ⟨4809101346067316933323243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25648540512359023644390629 4809101346067316933323243)
  ·
    refine ⟨7213652019100975399984865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4809101346067316933323243 7213652019100975399984865)
    ·
      refine ⟨5410239014325731549988649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7213652019100975399984865 5410239014325731549988649)
      ·
        refine ⟨4057679260744298662491487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5410239014325731549988649 4057679260744298662491487)
        ·
          refine ⟨6086518891116447993737231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4057679260744298662491487 6086518891116447993737231)
          ·
            refine ⟨9129778336674671990605847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6086518891116447993737231 9129778336674671990605847)
            ·
              refine ⟨13694667505012007985908771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9129778336674671990605847 13694667505012007985908771)
              ·
                refine ⟨20542001257518011978863157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13694667505012007985908771 20542001257518011978863157)
                ·
                  refine ⟨1925812617892313623018421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20542001257518011978863157 1925812617892313623018421)
                  ·
                    refine ⟨180544932927404402157977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1925812617892313623018421 180544932927404402157977)
                    ·
                      rfl

theorem cell23_1054830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_1054830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054830 prefixEnd_1054830 := by exact prefixLift 1054830
  have htrace : WordTrace (prefixWord ++ tailWord_1054830) baseStart_1054830 baseEnd_1054830 := by
    simpa [prefixWord, tailWord_1054830, baseEnd_1054830] using wordTrace_append hprefix tailTrace_1054830
  have hstable : (prefixWord ++ tailWord_1054830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054830).length < 2 ^ (prefixWord ++ tailWord_1054830).sum := by decide
  have hdescent : baseEnd_1054830 < baseStart_1054830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054867 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 7, 2, 2]
def baseStart_1054867 : Nat := 118140960795 + 1054867 * 2 ^ 59
def prefixEnd_1054867 : Nat := 4983230072969 + 3 ^ 40 * 1054867 * 2
def baseEnd_1054867 : Nat := 541653797566429561711261

theorem tailTrace_1054867 : CollatzResearch.WordTrace tailWord_1054867 prefixEnd_1054867 541653797566429561711261 := by
  unfold tailWord_1054867
  simp only [CollatzResearch.WordTrace]
  refine ⟨38474160269404490785682855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25649440179602993857121903 38474160269404490785682855)
  ·
    refine ⟨57711240404106736178524283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38474160269404490785682855 57711240404106736178524283)
    ·
      refine ⟨86566860606160104267786425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57711240404106736178524283 86566860606160104267786425)
      ·
        refine ⟨64925145454620078200839819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86566860606160104267786425 64925145454620078200839819)
        ·
          refine ⟨97387718181930117301259729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64925145454620078200839819 97387718181930117301259729)
          ·
            refine ⟨73040788636447587975944797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97387718181930117301259729 73040788636447587975944797)
            ·
              refine ⟨27390295738667845490979299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73040788636447587975944797 27390295738667845490979299)
              ·
                refine ⟨41085443608001768236468949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27390295738667845490979299 41085443608001768236468949)
                ·
                  refine ⟨962940084562541443042241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 41085443608001768236468949 962940084562541443042241)
                  ·
                    refine ⟨722205063421906082281681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 962940084562541443042241 722205063421906082281681)
                    ·
                      refine ⟨541653797566429561711261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 722205063421906082281681 541653797566429561711261)
                      ·
                        rfl

theorem cell23_1054867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 7, 2, 2].length) (baseStart_1054867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054867 prefixEnd_1054867 := by exact prefixLift 1054867
  have htrace : WordTrace (prefixWord ++ tailWord_1054867) baseStart_1054867 baseEnd_1054867 := by
    simpa [prefixWord, tailWord_1054867, baseEnd_1054867] using wordTrace_append hprefix tailTrace_1054867
  have hstable : (prefixWord ++ tailWord_1054867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054867).length < 2 ^ (prefixWord ++ tailWord_1054867).sum := by decide
  have hdescent : baseEnd_1054867 < baseStart_1054867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054877 : List Nat := [1, 4, 2, 1, 1, 4, 1, 1, 4, 4]
def baseStart_1054877 : Nat := 118140960795 + 1054877 * 2 ^ 59
def prefixEnd_1054877 : Nat := 4983230072969 + 3 ^ 40 * 1054877 * 2
def baseEnd_1054877 : Nat := 180552977457658174195405

theorem tailTrace_1054877 : CollatzResearch.WordTrace tailWord_1054877 prefixEnd_1054877 180552977457658174195405 := by
  unfold tailWord_1054877
  simp only [CollatzResearch.WordTrace]
  refine ⟨38474524999368262493546885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25649683332912174995697923 38474524999368262493546885)
  ·
    refine ⟨7213973437381549217540041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38474524999368262493546885 7213973437381549217540041)
    ·
      refine ⟨5410480078036161913155031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7213973437381549217540041 5410480078036161913155031)
      ·
        refine ⟨8115720117054242869732547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5410480078036161913155031 8115720117054242869732547)
        ·
          refine ⟨12173580175581364304598821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8115720117054242869732547 12173580175581364304598821)
          ·
            refine ⟨2282546282921505807112279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12173580175581364304598821 2282546282921505807112279)
            ·
              refine ⟨3423819424382258710668419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2282546282921505807112279 3423819424382258710668419)
              ·
                refine ⟨5135729136573388066002629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3423819424382258710668419 5135729136573388066002629)
                ·
                  refine ⟨962949213107510262375493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5135729136573388066002629 962949213107510262375493)
                  ·
                    refine ⟨180552977457658174195405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 962949213107510262375493 180552977457658174195405)
                    ·
                      rfl

theorem cell23_1054877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_1054877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054877 prefixEnd_1054877 := by exact prefixLift 1054877
  have htrace : WordTrace (prefixWord ++ tailWord_1054877) baseStart_1054877 baseEnd_1054877 := by
    simpa [prefixWord, tailWord_1054877, baseEnd_1054877] using wordTrace_append hprefix tailTrace_1054877
  have hstable : (prefixWord ++ tailWord_1054877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054877).length < 2 ^ (prefixWord ++ tailWord_1054877).sum := by decide
  have hdescent : baseEnd_1054877 < baseStart_1054877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054883 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 7]
def baseStart_1054883 : Nat := 118140960795 + 1054883 * 2 ^ 59
def prefixEnd_1054883 : Nat := 4983230072969 + 3 ^ 40 * 1054883 * 2
def baseEnd_1054883 : Nat := 541662013256901499111187

theorem tailTrace_1054883 : CollatzResearch.WordTrace tailWord_1054883 prefixEnd_1054883 541662013256901499111187 := by
  unfold tailWord_1054883
  simp only [CollatzResearch.WordTrace]
  refine ⟨38474743837346525518265303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25649829224897683678843535 38474743837346525518265303)
  ·
    refine ⟨57712115756019788277397955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38474743837346525518265303 57712115756019788277397955)
    ·
      refine ⟨86568173634029682416096933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57712115756019788277397955 86568173634029682416096933)
      ·
        refine ⟨16231532556380565453018175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86568173634029682416096933 16231532556380565453018175)
        ·
          refine ⟨24347298834570848179527263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16231532556380565453018175 24347298834570848179527263)
          ·
            refine ⟨36520948251856272269290895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24347298834570848179527263 36520948251856272269290895)
            ·
              refine ⟨54781422377784408403936343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36520948251856272269290895 54781422377784408403936343)
              ·
                refine ⟨82172133566676612605904515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54781422377784408403936343 82172133566676612605904515)
                ·
                  refine ⟨123258200350014918908856773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82172133566676612605904515 123258200350014918908856773)
                  ·
                    refine ⟨23110912565627797295410645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 123258200350014918908856773 23110912565627797295410645)
                    ·
                      refine ⟨541662013256901499111187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 23110912565627797295410645 541662013256901499111187)
                      ·
                        rfl

theorem cell23_1054883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_1054883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054883 prefixEnd_1054883 := by exact prefixLift 1054883
  have htrace : WordTrace (prefixWord ++ tailWord_1054883) baseStart_1054883 baseEnd_1054883 := by
    simpa [prefixWord, tailWord_1054883, baseEnd_1054883] using wordTrace_append hprefix tailTrace_1054883
  have hstable : (prefixWord ++ tailWord_1054883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054883).length < 2 ^ (prefixWord ++ tailWord_1054883).sum := by decide
  have hdescent : baseEnd_1054883 < baseStart_1054883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054897 : List Nat := [1, 2, 2, 5, 2, 1, 1, 1, 1, 1, 6]
def baseStart_1054897 : Nat := 118140960795 + 1054897 * 2 ^ 59
def prefixEnd_1054897 : Nat := 4983230072969 + 3 ^ 40 * 1054897 * 2
def baseEnd_1054897 : Nat := 541669201986064444336123

theorem tailTrace_1054897 : CollatzResearch.WordTrace tailWord_1054897 prefixEnd_1054897 541669201986064444336123 := by
  unfold tailWord_1054897
  simp only [CollatzResearch.WordTrace]
  refine ⟨38475254459295805909274945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25650169639530537272849963 38475254459295805909274945)
  ·
    refine ⟨28856440844471854431956209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38475254459295805909274945 28856440844471854431956209)
    ·
      refine ⟨21642330633353890823967157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28856440844471854431956209 21642330633353890823967157)
      ·
        refine ⟨2028968496876927264746921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21642330633353890823967157 2028968496876927264746921)
        ·
          refine ⟨1521726372657695448560191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2028968496876927264746921 1521726372657695448560191)
          ·
            refine ⟨2282589558986543172840287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1521726372657695448560191 2282589558986543172840287)
            ·
              refine ⟨3423884338479814759260431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2282589558986543172840287 3423884338479814759260431)
              ·
                refine ⟨5135826507719722138890647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3423884338479814759260431 5135826507719722138890647)
                ·
                  refine ⟨7703739761579583208335971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5135826507719722138890647 7703739761579583208335971)
                  ·
                    refine ⟨11555609642369374812503957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7703739761579583208335971 11555609642369374812503957)
                    ·
                      refine ⟨541669201986064444336123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11555609642369374812503957 541669201986064444336123)
                      ·
                        rfl

theorem cell23_1054897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_1054897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054897 prefixEnd_1054897 := by exact prefixLift 1054897
  have htrace : WordTrace (prefixWord ++ tailWord_1054897) baseStart_1054897 baseEnd_1054897 := by
    simpa [prefixWord, tailWord_1054897, baseEnd_1054897] using wordTrace_append hprefix tailTrace_1054897
  have hstable : (prefixWord ++ tailWord_1054897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054897).length < 2 ^ (prefixWord ++ tailWord_1054897).sum := by decide
  have hdescent : baseEnd_1054897 < baseStart_1054897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054901 : List Nat := [1, 3, 3, 4, 1, 1, 2, 2, 1, 1, 4]
def baseStart_1054901 : Nat := 118140960795 + 1054901 * 2 ^ 59
def prefixEnd_1054901 : Nat := 4983230072969 + 3 ^ 40 * 1054901 * 2
def baseEnd_1054901 : Nat := 541671255908682428686105

theorem tailTrace_1054901 : CollatzResearch.WordTrace tailWord_1054901 prefixEnd_1054901 541671255908682428686105 := by
  unfold tailWord_1054901
  simp only [CollatzResearch.WordTrace]
  refine ⟨38475400351281314592420557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25650266900854209728280371 38475400351281314592420557)
  ·
    refine ⟨14428275131730492972157709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38475400351281314592420557 14428275131730492972157709)
    ·
      refine ⟨5410603174398934864559141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14428275131730492972157709 5410603174398934864559141)
      ·
        refine ⟨1014488095199800287104839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5410603174398934864559141 1014488095199800287104839)
        ·
          refine ⟨1521732142799700430657259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1014488095199800287104839 1521732142799700430657259)
          ·
            refine ⟨2282598214199550645985889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1521732142799700430657259 2282598214199550645985889)
            ·
              refine ⟨1711948660649662984489417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2282598214199550645985889 1711948660649662984489417)
              ·
                refine ⟨1283961495487247238367063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1711948660649662984489417 1283961495487247238367063)
                ·
                  refine ⟨1925942243230870857550595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1283961495487247238367063 1925942243230870857550595)
                  ·
                    refine ⟨2888913364846306286325893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1925942243230870857550595 2888913364846306286325893)
                    ·
                      refine ⟨541671255908682428686105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2888913364846306286325893 541671255908682428686105)
                      ·
                        rfl

theorem cell23_1054901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_1054901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054901 prefixEnd_1054901 := by exact prefixLift 1054901
  have htrace : WordTrace (prefixWord ++ tailWord_1054901) baseStart_1054901 baseEnd_1054901 := by
    simpa [prefixWord, tailWord_1054901, baseEnd_1054901] using wordTrace_append hprefix tailTrace_1054901
  have hstable : (prefixWord ++ tailWord_1054901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054901).length < 2 ^ (prefixWord ++ tailWord_1054901).sum := by decide
  have hdescent : baseEnd_1054901 < baseStart_1054901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054917 : List Nat := [1, 3, 1, 1, 1, 1, 5, 2, 4, 1, 3]
def baseStart_1054917 : Nat := 118140960795 + 1054917 * 2 ^ 59
def prefixEnd_1054917 : Nat := 4983230072969 + 3 ^ 40 * 1054917 * 2
def baseEnd_1054917 : Nat := 541679471599154366086031

theorem tailTrace_1054917 : CollatzResearch.WordTrace tailWord_1054917 prefixEnd_1054917 541679471599154366086031 := by
  unfold tailWord_1054917
  simp only [CollatzResearch.WordTrace]
  refine ⟨38475983919223349325003005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25650655946148899550002003 38475983919223349325003005)
  ·
    refine ⟨14428493969708755996876127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38475983919223349325003005 14428493969708755996876127)
    ·
      refine ⟨21642740954563133995314191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14428493969708755996876127 21642740954563133995314191)
      ·
        refine ⟨32464111431844700992971287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21642740954563133995314191 32464111431844700992971287)
        ·
          refine ⟨48696167147767051489456931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32464111431844700992971287 48696167147767051489456931)
          ·
            refine ⟨73044250721650577234185397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48696167147767051489456931 73044250721650577234185397)
            ·
              refine ⟨6847898505154741615704881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 73044250721650577234185397 6847898505154741615704881)
              ·
                refine ⟨5135923878866056211778661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6847898505154741615704881 5135923878866056211778661)
                ·
                  refine ⟨962985727287385539708499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5135923878866056211778661 962985727287385539708499)
                  ·
                    refine ⟨1444478590931078309562749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 962985727287385539708499 1444478590931078309562749)
                    ·
                      refine ⟨541679471599154366086031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1444478590931078309562749 541679471599154366086031)
                      ·
                        rfl

theorem cell23_1054917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 4, 1, 3].length) (baseStart_1054917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054917 prefixEnd_1054917 := by exact prefixLift 1054917
  have htrace : WordTrace (prefixWord ++ tailWord_1054917) baseStart_1054917 baseEnd_1054917 := by
    simpa [prefixWord, tailWord_1054917, baseEnd_1054917] using wordTrace_append hprefix tailTrace_1054917
  have hstable : (prefixWord ++ tailWord_1054917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054917).length < 2 ^ (prefixWord ++ tailWord_1054917).sum := by decide
  have hdescent : baseEnd_1054917 < baseStart_1054917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054924 : List Nat := [2, 2, 1, 6, 2, 1, 9]
def baseStart_1054924 : Nat := 118140960795 + 1054924 * 2 ^ 59
def prefixEnd_1054924 : Nat := 4983230072969 + 3 ^ 40 * 1054924 * 2
def baseEnd_1054924 : Nat := 6687445258811553564179

theorem tailTrace_1054924 : CollatzResearch.WordTrace tailWord_1054924 prefixEnd_1054924 6687445258811553564179 := by
  unfold tailWord_1054924
  simp only [CollatzResearch.WordTrace]
  refine ⟨19238119615098994760253913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25650826153465326347005217 19238119615098994760253913)
  ·
    refine ⟨14428589711324246070190435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19238119615098994760253913 14428589711324246070190435)
    ·
      refine ⟨21642884566986369105285653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14428589711324246070190435 21642884566986369105285653)
      ·
        refine ⟨1014510214077486051810265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 21642884566986369105285653 1014510214077486051810265)
        ·
          refine ⟨760882660558114538857699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1014510214077486051810265 760882660558114538857699)
          ·
            refine ⟨1141323990837171808286549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760882660558114538857699 1141323990837171808286549)
            ·
              refine ⟨6687445258811553564179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1141323990837171808286549 6687445258811553564179)
              ·
                rfl

theorem cell23_1054924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 9].length) (baseStart_1054924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054924 prefixEnd_1054924 := by exact prefixLift 1054924
  have htrace : WordTrace (prefixWord ++ tailWord_1054924) baseStart_1054924 baseEnd_1054924 := by
    simpa [prefixWord, tailWord_1054924, baseEnd_1054924] using wordTrace_append hprefix tailTrace_1054924
  have hstable : (prefixWord ++ tailWord_1054924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054924).length < 2 ^ (prefixWord ++ tailWord_1054924).sum := by decide
  have hdescent : baseEnd_1054924 < baseStart_1054924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054951 : List Nat := [1, 1, 5, 3, 1, 2, 1, 3, 2, 1, 3]
def baseStart_1054951 : Nat := 118140960795 + 1054951 * 2 ^ 59
def prefixEnd_1054951 : Nat := 4983230072969 + 3 ^ 40 * 1054951 * 2
def baseEnd_1054951 : Nat := 541696929941407233060875

theorem tailTrace_1054951 : CollatzResearch.WordTrace tailWord_1054951 prefixEnd_1054951 541696929941407233060875 := by
  unfold tailWord_1054951
  simp only [CollatzResearch.WordTrace]
  refine ⟨38477224001100173131740707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25651482667400115421160471 38477224001100173131740707)
  ·
    refine ⟨57715836001650259697611061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38477224001100173131740707 57715836001650259697611061)
    ·
      refine ⟨5410859625154711846651037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57715836001650259697611061 5410859625154711846651037)
      ·
        refine ⟨2029072359433016942494139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5410859625154711846651037 2029072359433016942494139)
        ·
          refine ⟨3043608539149525413741209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2029072359433016942494139 3043608539149525413741209)
          ·
            refine ⟨2282706404362144060305907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3043608539149525413741209 2282706404362144060305907)
            ·
              refine ⟨3424059606543216090458861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2282706404362144060305907 3424059606543216090458861)
              ·
                refine ⟨1284022352453706033922073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3424059606543216090458861 1284022352453706033922073)
                ·
                  refine ⟨963016764340279525441555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1284022352453706033922073 963016764340279525441555)
                  ·
                    refine ⟨1444525146510419288162333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 963016764340279525441555 1444525146510419288162333)
                    ·
                      refine ⟨541696929941407233060875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1444525146510419288162333 541696929941407233060875)
                      ·
                        rfl

theorem cell23_1054951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_1054951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1054951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1054951 prefixEnd_1054951 := by exact prefixLift 1054951
  have htrace : WordTrace (prefixWord ++ tailWord_1054951) baseStart_1054951 baseEnd_1054951 := by
    simpa [prefixWord, tailWord_1054951, baseEnd_1054951] using wordTrace_append hprefix tailTrace_1054951
  have hstable : (prefixWord ++ tailWord_1054951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054951).length < 2 ^ (prefixWord ++ tailWord_1054951).sum := by decide
  have hdescent : baseEnd_1054951 < baseStart_1054951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055007 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 1, 5, 3]
def baseStart_1055007 : Nat := 118140960795 + 1055007 * 2 ^ 59
def prefixEnd_1055007 : Nat := 4983230072969 + 3 ^ 40 * 1055007 * 2
def baseEnd_1055007 : Nat := 541725684858059013960617

theorem tailTrace_1055007 : CollatzResearch.WordTrace tailWord_1055007 prefixEnd_1055007 541725684858059013960617 := by
  unfold tailWord_1055007
  simp only [CollatzResearch.WordTrace]
  refine ⟨38479266488897294695779275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25652844325931529797186183 38479266488897294695779275)
  ·
    refine ⟨57718899733345942043668913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38479266488897294695779275 57718899733345942043668913)
    ·
      refine ⟨43289174800009456532751685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57718899733345942043668913 43289174800009456532751685)
      ·
        refine ⟨8116720275001773099890941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43289174800009456532751685 8116720275001773099890941)
        ·
          refine ⟨3043770103125664912459103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8116720275001773099890941 3043770103125664912459103)
          ·
            refine ⟨4565655154688497368688655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3043770103125664912459103 4565655154688497368688655)
            ·
              refine ⟨6848482732032746053032983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4565655154688497368688655 6848482732032746053032983)
              ·
                refine ⟨10272724098049119079549475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6848482732032746053032983 10272724098049119079549475)
                ·
                  refine ⟨15409086147073678619324213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10272724098049119079549475 15409086147073678619324213)
                  ·
                    refine ⟨1444601826288157370561645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15409086147073678619324213 1444601826288157370561645)
                    ·
                      refine ⟨541725684858059013960617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1444601826288157370561645 541725684858059013960617)
                      ·
                        rfl

theorem cell23_1055007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_1055007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055007 prefixEnd_1055007 := by exact prefixLift 1055007
  have htrace : WordTrace (prefixWord ++ tailWord_1055007) baseStart_1055007 baseEnd_1055007 := by
    simpa [prefixWord, tailWord_1055007, baseEnd_1055007] using wordTrace_append hprefix tailTrace_1055007
  have hstable : (prefixWord ++ tailWord_1055007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055007).length < 2 ^ (prefixWord ++ tailWord_1055007).sum := by decide
  have hdescent : baseEnd_1055007 < baseStart_1055007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055020 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 7]
def baseStart_1055020 : Nat := 118140960795 + 1055020 * 2 ^ 59
def prefixEnd_1055020 : Nat := 4983230072969 + 3 ^ 40 * 1055020 * 2
def baseEnd_1055020 : Nat := 541732360106567463098057

theorem tailTrace_1055020 : CollatzResearch.WordTrace tailWord_1055020 prefixEnd_1055020 541732360106567463098057 := by
  unfold tailWord_1055020
  simp only [CollatzResearch.WordTrace]
  refine ⟨19239870318925098958001257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25653160425233465277335009 19239870318925098958001257)
  ·
    refine ⟨14429902739193824218500943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19239870318925098958001257 14429902739193824218500943)
    ·
      refine ⟨21644854108790736327751415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14429902739193824218500943 21644854108790736327751415)
      ·
        refine ⟨32467281163186104491627123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21644854108790736327751415 32467281163186104491627123)
        ·
          refine ⟨48700921744779156737440685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32467281163186104491627123 48700921744779156737440685)
          ·
            refine ⟨18262845654292183776540257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48700921744779156737440685 18262845654292183776540257)
            ·
              refine ⟨13697134240719137832405193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18262845654292183776540257 13697134240719137832405193)
              ·
                refine ⟨10272850680539353374303895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13697134240719137832405193 10272850680539353374303895)
                ·
                  refine ⟨15409276020809030061455843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10272850680539353374303895 15409276020809030061455843)
                  ·
                    refine ⟨23113914031213545092183765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15409276020809030061455843 23113914031213545092183765)
                    ·
                      refine ⟨541732360106567463098057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 23113914031213545092183765 541732360106567463098057)
                      ·
                        rfl

theorem cell23_1055020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_1055020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055020 prefixEnd_1055020 := by exact prefixLift 1055020
  have htrace : WordTrace (prefixWord ++ tailWord_1055020) baseStart_1055020 baseEnd_1055020 := by
    simpa [prefixWord, tailWord_1055020, baseEnd_1055020] using wordTrace_append hprefix tailTrace_1055020
  have hstable : (prefixWord ++ tailWord_1055020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055020).length < 2 ^ (prefixWord ++ tailWord_1055020).sum := by decide
  have hdescent : baseEnd_1055020 < baseStart_1055020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055047 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 4]
def baseStart_1055047 : Nat := 118140960795 + 1055047 * 2 ^ 59
def prefixEnd_1055047 : Nat := 4983230072969 + 3 ^ 40 * 1055047 * 2
def baseEnd_1055047 : Nat := 541746224084238857460433

theorem tailTrace_1055047 : CollatzResearch.WordTrace tailWord_1055047 prefixEnd_1055047 541746224084238857460433 := by
  unfold tailWord_1055047
  simp only [CollatzResearch.WordTrace]
  refine ⟨38480725408752381527235395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25653816939168254351490263 38480725408752381527235395)
  ·
    refine ⟨57721088113128572290853093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38480725408752381527235395 57721088113128572290853093)
    ·
      refine ⟨10822704021211607304534955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57721088113128572290853093 10822704021211607304534955)
      ·
        refine ⟨16234056031817410956802433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10822704021211607304534955 16234056031817410956802433)
        ·
          refine ⟨12175542023863058217601825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16234056031817410956802433 12175542023863058217601825)
          ·
            refine ⟨9131656517897293663201369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12175542023863058217601825 9131656517897293663201369)
            ·
              refine ⟨6848742388422970247401027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9131656517897293663201369 6848742388422970247401027)
              ·
                refine ⟨10273113582634455371101541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6848742388422970247401027 10273113582634455371101541)
                ·
                  refine ⟨1926208796743960382081539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10273113582634455371101541 1926208796743960382081539)
                  ·
                    refine ⟨2889313195115940573122309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1926208796743960382081539 2889313195115940573122309)
                    ·
                      refine ⟨541746224084238857460433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2889313195115940573122309 541746224084238857460433)
                      ·
                        rfl

theorem cell23_1055047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_1055047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055047 prefixEnd_1055047 := by exact prefixLift 1055047
  have htrace : WordTrace (prefixWord ++ tailWord_1055047) baseStart_1055047 baseEnd_1055047 := by
    simpa [prefixWord, tailWord_1055047, baseEnd_1055047] using wordTrace_append hprefix tailTrace_1055047
  have hstable : (prefixWord ++ tailWord_1055047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055047).length < 2 ^ (prefixWord ++ tailWord_1055047).sum := by decide
  have hdescent : baseEnd_1055047 < baseStart_1055047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055108 : List Nat := [2, 3, 2, 1, 1, 2, 5, 2, 1, 4]
def baseStart_1055108 : Nat := 118140960795 + 1055108 * 2 ^ 59
def prefixEnd_1055108 : Nat := 4983230072969 + 3 ^ 40 * 1055108 * 2
def baseEnd_1055108 : Nat := 180592515468054372932551

theorem tailTrace_1055108 : CollatzResearch.WordTrace tailWord_1055108 prefixEnd_1055108 180592515468054372932551 := by
  unfold tailWord_1055108
  simp only [CollatzResearch.WordTrace]
  refine ⟨19241475130765694472602989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25655300174354259296803985 19241475130765694472602989)
  ·
    refine ⟨7215553174037135427226121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19241475130765694472602989 7215553174037135427226121)
    ·
      refine ⟨5411664880527851570419591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7215553174037135427226121 5411664880527851570419591)
      ·
        refine ⟨8117497320791777355629387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5411664880527851570419591 8117497320791777355629387)
        ·
          refine ⟨12176245981187666033444081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8117497320791777355629387 12176245981187666033444081)
          ·
            refine ⟨9132184485890749525083061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12176245981187666033444081 9132184485890749525083061)
            ·
              refine ⟨856142295552257767976537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9132184485890749525083061 856142295552257767976537)
              ·
                refine ⟨642106721664193325982403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 856142295552257767976537 642106721664193325982403)
                ·
                  refine ⟨963160082496289988973605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 642106721664193325982403 963160082496289988973605)
                  ·
                    refine ⟨180592515468054372932551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 963160082496289988973605 180592515468054372932551)
                    ·
                      rfl

theorem cell23_1055108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_1055108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055108 prefixEnd_1055108 := by exact prefixLift 1055108
  have htrace : WordTrace (prefixWord ++ tailWord_1055108) baseStart_1055108 baseEnd_1055108 := by
    simpa [prefixWord, tailWord_1055108, baseEnd_1055108] using wordTrace_append hprefix tailTrace_1055108
  have hstable : (prefixWord ++ tailWord_1055108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055108).length < 2 ^ (prefixWord ++ tailWord_1055108).sum := by decide
  have hdescent : baseEnd_1055108 < baseStart_1055108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055141 : List Nat := [1, 3, 1, 2, 1, 1, 6, 1, 2, 3, 2]
def baseStart_1055141 : Nat := 118140960795 + 1055141 * 2 ^ 59
def prefixEnd_1055141 : Nat := 4983230072969 + 3 ^ 40 * 1055141 * 2
def baseEnd_1055141 : Nat := 541794491265761489685001

theorem tailTrace_1055141 : CollatzResearch.WordTrace tailWord_1055141 prefixEnd_1055141 541794491265761489685001 := by
  unfold tailWord_1055141
  simp only [CollatzResearch.WordTrace]
  refine ⟨38484153870411835581157277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25656102580274557054104851 38484153870411835581157277)
  ·
    refine ⟨14431557701404438342933979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38484153870411835581157277 14431557701404438342933979)
    ·
      refine ⟨21647336552106657514400969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14431557701404438342933979 21647336552106657514400969)
      ·
        refine ⟨16235502414079993135800727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21647336552106657514400969 16235502414079993135800727)
        ·
          refine ⟨24353253621119989703701091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16235502414079993135800727 24353253621119989703701091)
          ·
            refine ⟨36529880431679984555551637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24353253621119989703701091 36529880431679984555551637)
            ·
              refine ⟨1712338145234999276041483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36529880431679984555551637 1712338145234999276041483)
              ·
                refine ⟨2568507217852498914062225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1712338145234999276041483 2568507217852498914062225)
                ·
                  refine ⟨1926380413389374185546669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2568507217852498914062225 1926380413389374185546669)
                  ·
                    refine ⟨722392655021015319580001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1926380413389374185546669 722392655021015319580001)
                    ·
                      refine ⟨541794491265761489685001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 722392655021015319580001 541794491265761489685001)
                      ·
                        rfl

theorem cell23_1055141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 3, 2].length) (baseStart_1055141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055141 prefixEnd_1055141 := by exact prefixLift 1055141
  have htrace : WordTrace (prefixWord ++ tailWord_1055141) baseStart_1055141 baseEnd_1055141 := by
    simpa [prefixWord, tailWord_1055141, baseEnd_1055141] using wordTrace_append hprefix tailTrace_1055141
  have hstable : (prefixWord ++ tailWord_1055141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055141).length < 2 ^ (prefixWord ++ tailWord_1055141).sum := by decide
  have hdescent : baseEnd_1055141 < baseStart_1055141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055165 : List Nat := [1, 4, 1, 2, 2, 2, 4, 2, 1, 1, 3]
def baseStart_1055165 : Nat := 118140960795 + 1055165 * 2 ^ 59
def prefixEnd_1055165 : Nat := 4983230072969 + 3 ^ 40 * 1055165 * 2
def baseEnd_1055165 : Nat := 541806814801469395784891

theorem tailTrace_1055165 : CollatzResearch.WordTrace tailWord_1055165 prefixEnd_1055165 541806814801469395784891 := by
  unfold tailWord_1055165
  simp only [CollatzResearch.WordTrace]
  refine ⟨38485029222324887680030949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25656686148216591786687299 38485029222324887680030949)
  ·
    refine ⟨7215942979185916440005803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38485029222324887680030949 7215942979185916440005803)
    ·
      refine ⟨10823914468778874660008705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7215942979185916440005803 10823914468778874660008705)
      ·
        refine ⟨8117935851584155995006529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10823914468778874660008705 8117935851584155995006529)
        ·
          refine ⟨6088451888688116996254897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8117935851584155995006529 6088451888688116996254897)
          ·
            refine ⟨4566338916516087747191173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6088451888688116996254897 4566338916516087747191173)
            ·
              refine ⟨856188546846766452598345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4566338916516087747191173 856188546846766452598345)
              ·
                refine ⟨642141410135074839448759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 856188546846766452598345 642141410135074839448759)
                ·
                  refine ⟨963212115202612259173139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 642141410135074839448759 963212115202612259173139)
                  ·
                    refine ⟨1444818172803918388759709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 963212115202612259173139 1444818172803918388759709)
                    ·
                      refine ⟨541806814801469395784891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1444818172803918388759709 541806814801469395784891)
                      ·
                        rfl

theorem cell23_1055165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_1055165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055165 prefixEnd_1055165 := by exact prefixLift 1055165
  have htrace : WordTrace (prefixWord ++ tailWord_1055165) baseStart_1055165 baseEnd_1055165 := by
    simpa [prefixWord, tailWord_1055165, baseEnd_1055165] using wordTrace_append hprefix tailTrace_1055165
  have hstable : (prefixWord ++ tailWord_1055165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055165).length < 2 ^ (prefixWord ++ tailWord_1055165).sum := by decide
  have hdescent : baseEnd_1055165 < baseStart_1055165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055171 : List Nat := [1, 1, 1, 3, 1, 1, 3, 5, 3, 2, 2]
def baseStart_1055171 : Nat := 118140960795 + 1055171 * 2 ^ 59
def prefixEnd_1055171 : Nat := 4983230072969 + 3 ^ 40 * 1055171 * 2
def baseEnd_1055171 : Nat := 541809895685396372309863

theorem tailTrace_1055171 : CollatzResearch.WordTrace tailWord_1055171 prefixEnd_1055171 541809895685396372309863 := by
  unfold tailWord_1055171
  simp only [CollatzResearch.WordTrace]
  refine ⟨38485248060303150704749367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25656832040202100469832911 38485248060303150704749367)
  ·
    refine ⟨57727872090454726057124051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38485248060303150704749367 57727872090454726057124051)
    ·
      refine ⟨86591808135682089085686077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57727872090454726057124051 86591808135682089085686077)
      ·
        refine ⟨32471928050880783407132279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86591808135682089085686077 32471928050880783407132279)
        ·
          refine ⟨48707892076321175110698419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32471928050880783407132279 48707892076321175110698419)
          ·
            refine ⟨73061838114481762666047629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48707892076321175110698419 73061838114481762666047629)
            ·
              refine ⟨27398189292930660999767861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73061838114481762666047629 27398189292930660999767861)
              ·
                refine ⟨2568580246212249468728237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27398189292930660999767861 2568580246212249468728237)
                ·
                  refine ⟨963217592329593550773089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2568580246212249468728237 963217592329593550773089)
                  ·
                    refine ⟨722413194247195163079817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 963217592329593550773089 722413194247195163079817)
                    ·
                      refine ⟨541809895685396372309863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 722413194247195163079817 541809895685396372309863)
                      ·
                        rfl

theorem cell23_1055171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 3, 2, 2].length) (baseStart_1055171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055171 prefixEnd_1055171 := by exact prefixLift 1055171
  have htrace : WordTrace (prefixWord ++ tailWord_1055171) baseStart_1055171 baseEnd_1055171 := by
    simpa [prefixWord, tailWord_1055171, baseEnd_1055171] using wordTrace_append hprefix tailTrace_1055171
  have hstable : (prefixWord ++ tailWord_1055171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055171).length < 2 ^ (prefixWord ++ tailWord_1055171).sum := by decide
  have hdescent : baseEnd_1055171 < baseStart_1055171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055177 : List Nat := [1, 2, 1, 1, 2, 1, 7, 8]
def baseStart_1055177 : Nat := 118140960795 + 1055177 * 2 ^ 59
def prefixEnd_1055177 : Nat := 4983230072969 + 3 ^ 40 * 1055177 * 2
def baseEnd_1055177 : Nat := 20067147280345309216105

theorem tailTrace_1055177 : CollatzResearch.WordTrace tailWord_1055177 prefixEnd_1055177 20067147280345309216105 := by
  unfold tailWord_1055177
  simp only [CollatzResearch.WordTrace]
  refine ⟨38485466898281413729467785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25656977932187609152978523 38485466898281413729467785)
  ·
    refine ⟨28864100173711060297100839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38485466898281413729467785 28864100173711060297100839)
    ·
      refine ⟨43296150260566590445651259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28864100173711060297100839 43296150260566590445651259)
      ·
        refine ⟨64944225390849885668476889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43296150260566590445651259 64944225390849885668476889)
        ·
          refine ⟨48708169043137414251357667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64944225390849885668476889 48708169043137414251357667)
          ·
            refine ⟨73062253564706121377036501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48708169043137414251357667 73062253564706121377036501)
            ·
              refine ⟨1712396567922799719774293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 73062253564706121377036501 1712396567922799719774293)
              ·
                refine ⟨20067147280345309216105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1712396567922799719774293 20067147280345309216105)
                ·
                  rfl

theorem cell23_1055177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 8].length) (baseStart_1055177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055177 prefixEnd_1055177 := by exact prefixLift 1055177
  have htrace : WordTrace (prefixWord ++ tailWord_1055177) baseStart_1055177 baseEnd_1055177 := by
    simpa [prefixWord, tailWord_1055177, baseEnd_1055177] using wordTrace_append hprefix tailTrace_1055177
  have hstable : (prefixWord ++ tailWord_1055177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055177).length < 2 ^ (prefixWord ++ tailWord_1055177).sum := by decide
  have hdescent : baseEnd_1055177 < baseStart_1055177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055188 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 5, 2, 2]
def baseStart_1055188 : Nat := 118140960795 + 1055188 * 2 ^ 59
def prefixEnd_1055188 : Nat := 4983230072969 + 3 ^ 40 * 1055188 * 2
def baseEnd_1055188 : Nat := 541818624856522805797285

theorem tailTrace_1055188 : CollatzResearch.WordTrace tailWord_1055188 prefixEnd_1055188 541818624856522805797285 := by
  unfold tailWord_1055188
  simp only [CollatzResearch.WordTrace]
  refine ⟨19242934050620781304059109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25657245400827708405412145 19242934050620781304059109)
  ·
    refine ⟨3608050134491396494511083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19242934050620781304059109 3608050134491396494511083)
    ·
      refine ⟨5412075201737094741766625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3608050134491396494511083 5412075201737094741766625)
      ·
        refine ⟨4059056401302821056324969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5412075201737094741766625 4059056401302821056324969)
        ·
          refine ⟨3044292300977115792243727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4059056401302821056324969 3044292300977115792243727)
          ·
            refine ⟨4566438451465673688365591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3044292300977115792243727 4566438451465673688365591)
            ·
              refine ⟨6849657677198510532548387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4566438451465673688365591 6849657677198510532548387)
              ·
                refine ⟨10274486515797765798822581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6849657677198510532548387 10274486515797765798822581)
                ·
                  refine ⟨963233110856040543639617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10274486515797765798822581 963233110856040543639617)
                  ·
                    refine ⟨722424833142030407729713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 963233110856040543639617 722424833142030407729713)
                    ·
                      refine ⟨541818624856522805797285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 722424833142030407729713 541818624856522805797285)
                      ·
                        rfl

theorem cell23_1055188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_1055188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055188 prefixEnd_1055188 := by exact prefixLift 1055188
  have htrace : WordTrace (prefixWord ++ tailWord_1055188) baseStart_1055188 baseEnd_1055188 := by
    simpa [prefixWord, tailWord_1055188, baseEnd_1055188] using wordTrace_append hprefix tailTrace_1055188
  have hstable : (prefixWord ++ tailWord_1055188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055188).length < 2 ^ (prefixWord ++ tailWord_1055188).sum := by decide
  have hdescent : baseEnd_1055188 < baseStart_1055188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055194 : List Nat := [3, 1, 1, 2, 3, 1, 5, 7]
def baseStart_1055194 : Nat := 118140960795 + 1055194 * 2 ^ 59
def prefixEnd_1055194 : Nat := 4983230072969 + 3 ^ 40 * 1055194 * 2
def baseEnd_1055194 : Nat := 20067470582979621567491

theorem tailTrace_1055194 : CollatzResearch.WordTrace tailWord_1055194 prefixEnd_1055194 20067470582979621567491 := by
  unfold tailWord_1055194
  simp only [CollatzResearch.WordTrace]
  refine ⟨9621521734804956408209159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25657391292813217088557757 9621521734804956408209159)
  ·
    refine ⟨14432282602207434612313739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9621521734804956408209159 14432282602207434612313739)
    ·
      refine ⟨21648423903311151918470609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14432282602207434612313739 21648423903311151918470609)
      ·
        refine ⟨16236317927483363938852957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21648423903311151918470609 16236317927483363938852957)
        ·
          refine ⟨6088619222806261477069859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16236317927483363938852957 6088619222806261477069859)
          ·
            refine ⟨9132928834209392215604789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6088619222806261477069859 9132928834209392215604789)
            ·
              refine ⟨856212078207130520212949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9132928834209392215604789 856212078207130520212949)
              ·
                refine ⟨20067470582979621567491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 856212078207130520212949 20067470582979621567491)
                ·
                  rfl

theorem cell23_1055194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 7].length) (baseStart_1055194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055194 prefixEnd_1055194 := by exact prefixLift 1055194
  have htrace : WordTrace (prefixWord ++ tailWord_1055194) baseStart_1055194 baseEnd_1055194 := by
    simpa [prefixWord, tailWord_1055194, baseEnd_1055194] using wordTrace_append hprefix tailTrace_1055194
  have hstable : (prefixWord ++ tailWord_1055194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055194).length < 2 ^ (prefixWord ++ tailWord_1055194).sum := by decide
  have hdescent : baseEnd_1055194 < baseStart_1055194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055202 : List Nat := [3, 3, 3, 2, 1, 2, 2, 1, 1, 5]
def baseStart_1055202 : Nat := 118140960795 + 1055202 * 2 ^ 59
def prefixEnd_1055202 : Nat := 4983230072969 + 3 ^ 40 * 1055202 * 2
def baseEnd_1055202 : Nat := 180608604528561917007407

theorem tailTrace_1055202 : CollatzResearch.WordTrace tailWord_1055202 prefixEnd_1055202 180608604528561917007407 := by
  unfold tailWord_1055202
  simp only [CollatzResearch.WordTrace]
  refine ⟨9621594680797710749781965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25657585815460561999418573 9621594680797710749781965)
  ·
    refine ⟨3608098005299141531168237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9621594680797710749781965 3608098005299141531168237)
    ·
      refine ⟨1353036751987178074188089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3608098005299141531168237 1353036751987178074188089)
      ·
        refine ⟨1014777563990383555641067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1353036751987178074188089 1014777563990383555641067)
        ·
          refine ⟨1522166345985575333461601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1014777563990383555641067 1522166345985575333461601)
          ·
            refine ⟨1141624759489181500096201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1522166345985575333461601 1141624759489181500096201)
            ·
              refine ⟨856218569616886125072151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1141624759489181500096201 856218569616886125072151)
              ·
                refine ⟨1284327854425329187608227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 856218569616886125072151 1284327854425329187608227)
                ·
                  refine ⟨1926491781637993781412341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1284327854425329187608227 1926491781637993781412341)
                  ·
                    refine ⟨180608604528561917007407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1926491781637993781412341 180608604528561917007407)
                    ·
                      rfl

theorem cell23_1055202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_1055202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055202 prefixEnd_1055202 := by exact prefixLift 1055202
  have htrace : WordTrace (prefixWord ++ tailWord_1055202) baseStart_1055202 baseEnd_1055202 := by
    simpa [prefixWord, tailWord_1055202, baseEnd_1055202] using wordTrace_append hprefix tailTrace_1055202
  have hstable : (prefixWord ++ tailWord_1055202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055202).length < 2 ^ (prefixWord ++ tailWord_1055202).sum := by decide
  have hdescent : baseEnd_1055202 < baseStart_1055202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055205 : List Nat := [1, 3, 1, 5, 2, 2, 2, 1, 1, 1, 4]
def baseStart_1055205 : Nat := 118140960795 + 1055205 * 2 ^ 59
def prefixEnd_1055205 : Nat := 4983230072969 + 3 ^ 40 * 1055205 * 2
def baseEnd_1055205 : Nat := 541827354027649239284707

theorem tailTrace_1055205 : CollatzResearch.WordTrace tailWord_1055205 prefixEnd_1055205 541827354027649239284707 := by
  unfold tailWord_1055205
  simp only [CollatzResearch.WordTrace]
  refine ⟨38486488142179974511487069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25657658761453316340991379 38486488142179974511487069)
  ·
    refine ⟨14432433053317490441807651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38486488142179974511487069 14432433053317490441807651)
    ·
      refine ⟨21648649579976235662711477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14432433053317490441807651 21648649579976235662711477)
      ·
        refine ⟨2029560898122772093379201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21648649579976235662711477 2029560898122772093379201)
        ·
          refine ⟨1522170673592079070034401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2029560898122772093379201 1522170673592079070034401)
          ·
            refine ⟨1141628005194059302525801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1522170673592079070034401 1141628005194059302525801)
            ·
              refine ⟨856221003895544476894351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1141628005194059302525801 856221003895544476894351)
              ·
                refine ⟨1284331505843316715341527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 856221003895544476894351 1284331505843316715341527)
                ·
                  refine ⟨1926497258764975073012291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1284331505843316715341527 1926497258764975073012291)
                  ·
                    refine ⟨2889745888147462609518437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1926497258764975073012291 2889745888147462609518437)
                    ·
                      refine ⟨541827354027649239284707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2889745888147462609518437 541827354027649239284707)
                      ·
                        rfl

theorem cell23_1055205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_1055205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055205 prefixEnd_1055205 := by exact prefixLift 1055205
  have htrace : WordTrace (prefixWord ++ tailWord_1055205) baseStart_1055205 baseEnd_1055205 := by
    simpa [prefixWord, tailWord_1055205, baseEnd_1055205] using wordTrace_append hprefix tailTrace_1055205
  have hstable : (prefixWord ++ tailWord_1055205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055205).length < 2 ^ (prefixWord ++ tailWord_1055205).sum := by decide
  have hdescent : baseEnd_1055205 < baseStart_1055205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055208 : List Nat := [2, 1, 4, 1, 1, 3, 4, 1, 1, 2, 3]
def baseStart_1055208 : Nat := 118140960795 + 1055208 * 2 ^ 59
def prefixEnd_1055208 : Nat := 4983230072969 + 3 ^ 40 * 1055208 * 2
def baseEnd_1055208 : Nat := 541828894469612727547193

theorem tailTrace_1055208 : CollatzResearch.WordTrace tailWord_1055208 prefixEnd_1055208 541828894469612727547193 := by
  unfold tailWord_1055208
  simp only [CollatzResearch.WordTrace]
  refine ⟨19243298780584553011923139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25657731707446070682564185 19243298780584553011923139)
  ·
    refine ⟨28864948170876829517884709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19243298780584553011923139 28864948170876829517884709)
    ·
      refine ⟨5412177782039405534603383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28864948170876829517884709 5412177782039405534603383)
      ·
        refine ⟨8118266673059108301905075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5412177782039405534603383 8118266673059108301905075)
        ·
          refine ⟨12177400009588662452857613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8118266673059108301905075 12177400009588662452857613)
          ·
            refine ⟨4566525003595748419821605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12177400009588662452857613 4566525003595748419821605)
            ·
              refine ⟨856223438174202828716551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4566525003595748419821605 856223438174202828716551)
              ·
                refine ⟨1284335157261304243074827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 856223438174202828716551 1284335157261304243074827)
                ·
                  refine ⟨1926502735891956364612241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1284335157261304243074827 1926502735891956364612241)
                  ·
                    refine ⟨1444877051918967273459181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1926502735891956364612241 1444877051918967273459181)
                    ·
                      refine ⟨541828894469612727547193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1444877051918967273459181 541828894469612727547193)
                      ·
                        rfl

theorem cell23_1055208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_1055208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055208 prefixEnd_1055208 := by exact prefixLift 1055208
  have htrace : WordTrace (prefixWord ++ tailWord_1055208) baseStart_1055208 baseEnd_1055208 := by
    simpa [prefixWord, tailWord_1055208, baseEnd_1055208] using wordTrace_append hprefix tailTrace_1055208
  have hstable : (prefixWord ++ tailWord_1055208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055208).length < 2 ^ (prefixWord ++ tailWord_1055208).sum := by decide
  have hdescent : baseEnd_1055208 < baseStart_1055208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055245 : List Nat := [1, 7, 1, 1, 1, 3, 2, 7]
def baseStart_1055245 : Nat := 118140960795 + 1055245 * 2 ^ 59
def prefixEnd_1055245 : Nat := 4983230072969 + 3 ^ 40 * 1055245 * 2
def baseEnd_1055245 : Nat := 20068440490882558621649

theorem tailTrace_1055245 : CollatzResearch.WordTrace tailWord_1055245 prefixEnd_1055245 20068440490882558621649 := by
  unfold tailWord_1055245
  simp only [CollatzResearch.WordTrace]
  refine ⟨38487947062035061342943189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25658631374690040895295459 38487947062035061342943189)
  ·
    refine ⟨902061259266446750225231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 38487947062035061342943189 902061259266446750225231)
    ·
      refine ⟨1353091888899670125337847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 902061259266446750225231 1353091888899670125337847)
      ·
        refine ⟨2029637833349505188006771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1353091888899670125337847 2029637833349505188006771)
        ·
          refine ⟨3044456750024257782010157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2029637833349505188006771 3044456750024257782010157)
          ·
            refine ⟨1141671281259096668253809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3044456750024257782010157 1141671281259096668253809)
            ·
              refine ⟨856253460944322501190357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1141671281259096668253809 856253460944322501190357)
              ·
                refine ⟨20068440490882558621649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 856253460944322501190357 20068440490882558621649)
                ·
                  rfl

theorem cell23_1055245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 7].length) (baseStart_1055245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055245 prefixEnd_1055245 := by exact prefixLift 1055245
  have htrace : WordTrace (prefixWord ++ tailWord_1055245) baseStart_1055245 baseEnd_1055245 := by
    simpa [prefixWord, tailWord_1055245, baseEnd_1055245] using wordTrace_append hprefix tailTrace_1055245
  have hstable : (prefixWord ++ tailWord_1055245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055245).length < 2 ^ (prefixWord ++ tailWord_1055245).sum := by decide
  have hdescent : baseEnd_1055245 < baseStart_1055245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055341 : List Nat := [1, 5, 1, 1, 3, 1, 2, 1, 1, 2, 5]
def baseStart_1055341 : Nat := 118140960795 + 1055341 * 2 ^ 59
def prefixEnd_1055341 : Nat := 4983230072969 + 3 ^ 40 * 1055341 * 2
def baseEnd_1055341 : Nat := 541897187396660707184081

theorem tailTrace_1055341 : CollatzResearch.WordTrace tailWord_1055341 prefixEnd_1055341 541897187396660707184081 := by
  unfold tailWord_1055341
  simp only [CollatzResearch.WordTrace]
  refine ⟨38491448469687269738437877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25660965646458179825625251 38491448469687269738437877)
  ·
    refine ⟨3608573294033181537978551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38491448469687269738437877 3608573294033181537978551)
    ·
      refine ⟨5412859941049772306967827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3608573294033181537978551 5412859941049772306967827)
      ·
        refine ⟨8119289911574658460451741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5412859941049772306967827 8119289911574658460451741)
        ·
          refine ⟨3044733716840496922669403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8119289911574658460451741 3044733716840496922669403)
          ·
            refine ⟨4567100575260745384004105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3044733716840496922669403 4567100575260745384004105)
            ·
              refine ⟨3425325431445559038003079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4567100575260745384004105 3425325431445559038003079)
              ·
                refine ⟨5137988147168338557004619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3425325431445559038003079 5137988147168338557004619)
                ·
                  refine ⟨7706982220752507835506929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5137988147168338557004619 7706982220752507835506929)
                  ·
                    refine ⟨5780236665564380876630197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7706982220752507835506929 5780236665564380876630197)
                    ·
                      refine ⟨541897187396660707184081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5780236665564380876630197 541897187396660707184081)
                      ·
                        rfl

theorem cell23_1055341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_1055341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055341 prefixEnd_1055341 := by exact prefixLift 1055341
  have htrace : WordTrace (prefixWord ++ tailWord_1055341) baseStart_1055341 baseEnd_1055341 := by
    simpa [prefixWord, tailWord_1055341, baseEnd_1055341] using wordTrace_append hprefix tailTrace_1055341
  have hstable : (prefixWord ++ tailWord_1055341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055341).length < 2 ^ (prefixWord ++ tailWord_1055341).sum := by decide
  have hdescent : baseEnd_1055341 < baseStart_1055341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055351 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 1, 6, 2]
def baseStart_1055351 : Nat := 118140960795 + 1055351 * 2 ^ 59
def prefixEnd_1055351 : Nat := 4983230072969 + 3 ^ 40 * 1055351 * 2
def baseEnd_1055351 : Nat := 541902322203205668059035

theorem tailTrace_1055351 : CollatzResearch.WordTrace tailWord_1055351 prefixEnd_1055351 541902322203205668059035 := by
  unfold tailWord_1055351
  simp only [CollatzResearch.WordTrace]
  refine ⟨38491813199651041446301907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25661208799767360964201271 38491813199651041446301907)
  ·
    refine ⟨57737719799476562169452861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38491813199651041446301907 57737719799476562169452861)
    ·
      refine ⟨21651644924803710813544823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57737719799476562169452861 21651644924803710813544823)
      ·
        refine ⟨32477467387205566220317235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21651644924803710813544823 32477467387205566220317235)
        ·
          refine ⟨48716201080808349330475853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32477467387205566220317235 48716201080808349330475853)
          ·
            refine ⟨18268575405303130998928445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48716201080808349330475853 18268575405303130998928445)
            ·
              refine ⟨6850715776988674124598167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18268575405303130998928445 6850715776988674124598167)
              ·
                refine ⟨10276073665483011186897251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6850715776988674124598167 10276073665483011186897251)
                ·
                  refine ⟨15414110498224516780345877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10276073665483011186897251 15414110498224516780345877)
                  ·
                    refine ⟨722536429604274224078713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15414110498224516780345877 722536429604274224078713)
                    ·
                      refine ⟨541902322203205668059035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 722536429604274224078713 541902322203205668059035)
                      ·
                        rfl

theorem cell23_1055351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 6, 2].length) (baseStart_1055351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055351 prefixEnd_1055351 := by exact prefixLift 1055351
  have htrace : WordTrace (prefixWord ++ tailWord_1055351) baseStart_1055351 baseEnd_1055351 := by
    simpa [prefixWord, tailWord_1055351, baseEnd_1055351] using wordTrace_append hprefix tailTrace_1055351
  have hstable : (prefixWord ++ tailWord_1055351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055351).length < 2 ^ (prefixWord ++ tailWord_1055351).sum := by decide
  have hdescent : baseEnd_1055351 < baseStart_1055351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055371 : List Nat := [1, 1, 1, 1, 4, 1, 2, 5, 2, 2, 3]
def baseStart_1055371 : Nat := 118140960795 + 1055371 * 2 ^ 59
def prefixEnd_1055371 : Nat := 4983230072969 + 3 ^ 40 * 1055371 * 2
def baseEnd_1055371 : Nat := 541912591816295589808943

theorem tailTrace_1055371 : CollatzResearch.WordTrace tailWord_1055371 prefixEnd_1055371 541912591816295589808943 := by
  unfold tailWord_1055371
  simp only [CollatzResearch.WordTrace]
  refine ⟨38492542659578584862029967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25661695106385723241353311 38492542659578584862029967)
  ·
    refine ⟨57738813989367877293044951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38492542659578584862029967 57738813989367877293044951)
    ·
      refine ⟨86608220984051815939567427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57738813989367877293044951 86608220984051815939567427)
      ·
        refine ⟨129912331476077723909351141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86608220984051815939567427 129912331476077723909351141)
        ·
          refine ⟨24358562151764573233003339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129912331476077723909351141 24358562151764573233003339)
          ·
            refine ⟨36537843227646859849505009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24358562151764573233003339 36537843227646859849505009)
            ·
              refine ⟨27403382420735144887128757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36537843227646859849505009 27403382420735144887128757)
              ·
                refine ⟨2569067101943919833168321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27403382420735144887128757 2569067101943919833168321)
                ·
                  refine ⟨1926800326457939874876241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2569067101943919833168321 1926800326457939874876241)
                  ·
                    refine ⟨1445100244843454906157181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1926800326457939874876241 1445100244843454906157181)
                    ·
                      refine ⟨541912591816295589808943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1445100244843454906157181 541912591816295589808943)
                      ·
                        rfl

theorem cell23_1055371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 2, 3].length) (baseStart_1055371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055371 prefixEnd_1055371 := by exact prefixLift 1055371
  have htrace : WordTrace (prefixWord ++ tailWord_1055371) baseStart_1055371 baseEnd_1055371 := by
    simpa [prefixWord, tailWord_1055371, baseEnd_1055371] using wordTrace_append hprefix tailTrace_1055371
  have hstable : (prefixWord ++ tailWord_1055371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055371).length < 2 ^ (prefixWord ++ tailWord_1055371).sum := by decide
  have hdescent : baseEnd_1055371 < baseStart_1055371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055418 : List Nat := [3, 1, 1, 1, 2, 3, 1, 4, 3, 1, 3]
def baseStart_1055418 : Nat := 118140960795 + 1055418 * 2 ^ 59
def prefixEnd_1055418 : Nat := 4983230072969 + 3 ^ 40 * 1055418 * 2
def baseEnd_1055418 : Nat := 541936725407056905921227

theorem tailTrace_1055418 : CollatzResearch.WordTrace tailWord_1055418 prefixEnd_1055418 541936725407056905921227 := by
  unfold tailWord_1055418
  simp only [CollatzResearch.WordTrace]
  refine ⟨9623564222602077972247727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25662837926938874592660605 9623564222602077972247727)
  ·
    refine ⟨14435346333903116958371591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9623564222602077972247727 14435346333903116958371591)
    ·
      refine ⟨21653019500854675437557387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14435346333903116958371591 21653019500854675437557387)
      ·
        refine ⟨32479529251282013156336081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21653019500854675437557387 32479529251282013156336081)
        ·
          refine ⟨24359646938461509867252061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32479529251282013156336081 24359646938461509867252061)
          ·
            refine ⟨9134867601923066200219523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24359646938461509867252061 9134867601923066200219523)
            ·
              refine ⟨13702301402884599300329285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9134867601923066200219523 13702301402884599300329285)
              ·
                refine ⟨2569181513040862368811741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13702301402884599300329285 2569181513040862368811741)
                ·
                  refine ⟨963443067390323388304403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2569181513040862368811741 963443067390323388304403)
                  ·
                    refine ⟨1445164601085485082456605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 963443067390323388304403 1445164601085485082456605)
                    ·
                      refine ⟨541936725407056905921227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1445164601085485082456605 541936725407056905921227)
                      ·
                        rfl

theorem cell23_1055418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 3, 1, 3].length) (baseStart_1055418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055418 prefixEnd_1055418 := by exact prefixLift 1055418
  have htrace : WordTrace (prefixWord ++ tailWord_1055418) baseStart_1055418 baseEnd_1055418 := by
    simpa [prefixWord, tailWord_1055418, baseEnd_1055418] using wordTrace_append hprefix tailTrace_1055418
  have hstable : (prefixWord ++ tailWord_1055418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055418).length < 2 ^ (prefixWord ++ tailWord_1055418).sum := by decide
  have hdescent : baseEnd_1055418 < baseStart_1055418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055438 : List Nat := [4, 1, 1, 1, 3, 2, 2, 3, 1, 5]
def baseStart_1055438 : Nat := 118140960795 + 1055438 * 2 ^ 59
def prefixEnd_1055438 : Nat := 4983230072969 + 3 ^ 40 * 1055438 * 2
def baseEnd_1055438 : Nat := 180648998340048942557045

theorem tailTrace_1055438 : CollatzResearch.WordTrace tailWord_1055438 prefixEnd_1055438 180648998340048942557045 := by
  unfold tailWord_1055438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4811873293791981913089871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25663324233557236869812645 4811873293791981913089871)
  ·
    refine ⟨7217809940687972869634807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4811873293791981913089871 7217809940687972869634807)
    ·
      refine ⟨10826714911031959304452211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7217809940687972869634807 10826714911031959304452211)
      ·
        refine ⟨16240072366547938956678317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10826714911031959304452211 16240072366547938956678317)
        ·
          refine ⟨6090027137455477108754369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16240072366547938956678317 6090027137455477108754369)
          ·
            refine ⟨4567520353091607831565777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6090027137455477108754369 4567520353091607831565777)
            ·
              refine ⟨3425640264818705873674333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4567520353091607831565777 3425640264818705873674333)
              ·
                refine ⟨1284615099307014702627875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3425640264818705873674333 1284615099307014702627875)
                ·
                  refine ⟨1926922648960522053941813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1284615099307014702627875 1926922648960522053941813)
                  ·
                    refine ⟨180648998340048942557045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1926922648960522053941813 180648998340048942557045)
                    ·
                      rfl

theorem cell23_1055438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_1055438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055438 prefixEnd_1055438 := by exact prefixLift 1055438
  have htrace : WordTrace (prefixWord ++ tailWord_1055438) baseStart_1055438 baseEnd_1055438 := by
    simpa [prefixWord, tailWord_1055438, baseEnd_1055438] using wordTrace_append hprefix tailTrace_1055438
  have hstable : (prefixWord ++ tailWord_1055438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055438).length < 2 ^ (prefixWord ++ tailWord_1055438).sum := by decide
  have hdescent : baseEnd_1055438 < baseStart_1055438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055452 : List Nat := [2, 2, 5, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_1055452 : Nat := 118140960795 + 1055452 * 2 ^ 59
def prefixEnd_1055452 : Nat := 4983230072969 + 3 ^ 40 * 1055452 * 2
def baseEnd_1055452 : Nat := 541954183749309772896071

theorem tailTrace_1055452 : CollatzResearch.WordTrace tailWord_1055452 prefixEnd_1055452 541954183749309772896071 := by
  unfold tailWord_1055452
  simp only [CollatzResearch.WordTrace]
  refine ⟨19247748486142567847864305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25663664648190090463819073 19247748486142567847864305)
  ·
    refine ⟨14435811364606925885898229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19247748486142567847864305 14435811364606925885898229)
    ·
      refine ⟨1353357315431899301802959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14435811364606925885898229 1353357315431899301802959)
      ·
        refine ⟨2030035973147848952704439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1353357315431899301802959 2030035973147848952704439)
        ·
          refine ⟨3045053959721773429056659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2030035973147848952704439 3045053959721773429056659)
          ·
            refine ⟨4567580939582660143584989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3045053959721773429056659 4567580939582660143584989)
            ·
              refine ⟨1712842852343497553844371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4567580939582660143584989 1712842852343497553844371)
              ·
                refine ⟨2569264278515246330766557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1712842852343497553844371 2569264278515246330766557)
                ·
                  refine ⟨963474104443217374037459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2569264278515246330766557 963474104443217374037459)
                  ·
                    refine ⟨1445211156664826061056189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 963474104443217374037459 1445211156664826061056189)
                    ·
                      refine ⟨541954183749309772896071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1445211156664826061056189 541954183749309772896071)
                      ·
                        rfl

theorem cell23_1055452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_1055452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055452 prefixEnd_1055452 := by exact prefixLift 1055452
  have htrace : WordTrace (prefixWord ++ tailWord_1055452) baseStart_1055452 baseEnd_1055452 := by
    simpa [prefixWord, tailWord_1055452, baseEnd_1055452] using wordTrace_append hprefix tailTrace_1055452
  have hstable : (prefixWord ++ tailWord_1055452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055452).length < 2 ^ (prefixWord ++ tailWord_1055452).sum := by decide
  have hdescent : baseEnd_1055452 < baseStart_1055452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055471 : List Nat := [1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 6]
def baseStart_1055471 : Nat := 118140960795 + 1055471 * 2 ^ 59
def prefixEnd_1055471 : Nat := 4983230072969 + 3 ^ 40 * 1055471 * 2
def baseEnd_1055471 : Nat := 541963939881745198558483

theorem tailTrace_1055471 : CollatzResearch.WordTrace tailWord_1055471 prefixEnd_1055471 541963939881745198558483 := by
  unfold tailWord_1055471
  simp only [CollatzResearch.WordTrace]
  refine ⟨38496189959216301940670267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25664126639477534627113511 38496189959216301940670267)
  ·
    refine ⟨57744284938824452911005401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38496189959216301940670267 57744284938824452911005401)
    ·
      refine ⟨43308213704118339683254051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57744284938824452911005401 43308213704118339683254051)
      ·
        refine ⟨64962320556177509524881077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43308213704118339683254051 64962320556177509524881077)
        ·
          refine ⟨6090217552141641517957601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64962320556177509524881077 6090217552141641517957601)
          ·
            refine ⟨4567663164106231138468201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6090217552141641517957601 4567663164106231138468201)
            ·
              refine ⟨3425747373079673353851151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4567663164106231138468201 3425747373079673353851151)
              ·
                refine ⟨5138621059619510030776727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3425747373079673353851151 5138621059619510030776727)
                ·
                  refine ⟨7707931589429265046165091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5138621059619510030776727 7707931589429265046165091)
                  ·
                    refine ⟨11561897384143897569247637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7707931589429265046165091 11561897384143897569247637)
                    ·
                      refine ⟨541963939881745198558483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11561897384143897569247637 541963939881745198558483)
                      ·
                        rfl

theorem cell23_1055471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 6].length) (baseStart_1055471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055471 prefixEnd_1055471 := by exact prefixLift 1055471
  have htrace : WordTrace (prefixWord ++ tailWord_1055471) baseStart_1055471 baseEnd_1055471 := by
    simpa [prefixWord, tailWord_1055471, baseEnd_1055471] using wordTrace_append hprefix tailTrace_1055471
  have hstable : (prefixWord ++ tailWord_1055471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055471).length < 2 ^ (prefixWord ++ tailWord_1055471).sum := by decide
  have hdescent : baseEnd_1055471 < baseStart_1055471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055495 : List Nat := [1, 1, 4, 4, 1, 3, 1, 1, 1, 1, 5]
def baseStart_1055495 : Nat := 118140960795 + 1055495 * 2 ^ 59
def prefixEnd_1055495 : Nat := 4983230072969 + 3 ^ 40 * 1055495 * 2
def baseEnd_1055495 : Nat := 541976263417453104658373

theorem tailTrace_1055495 : CollatzResearch.WordTrace tailWord_1055495 prefixEnd_1055495 541976263417453104658373 := by
  unfold tailWord_1055495
  simp only [CollatzResearch.WordTrace]
  refine ⟨38497065311129354039543939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25664710207419569359695959 38497065311129354039543939)
  ·
    refine ⟨57745597966694031059315909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38497065311129354039543939 57745597966694031059315909)
    ·
      refine ⟨10827299618755130823621733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57745597966694031059315909 10827299618755130823621733)
      ·
        refine ⟨2030118678516587029429075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10827299618755130823621733 2030118678516587029429075)
        ·
          refine ⟨3045178017774880544143613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2030118678516587029429075 3045178017774880544143613)
          ·
            refine ⟨1141941756665580204053855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3045178017774880544143613 1141941756665580204053855)
            ·
              refine ⟨1712912634998370306080783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1141941756665580204053855 1712912634998370306080783)
              ·
                refine ⟨2569368952497555459121175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1712912634998370306080783 2569368952497555459121175)
                ·
                  refine ⟨3854053428746333188681763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2569368952497555459121175 3854053428746333188681763)
                  ·
                    refine ⟨5781080143119499783022645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3854053428746333188681763 5781080143119499783022645)
                    ·
                      refine ⟨541976263417453104658373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5781080143119499783022645 541976263417453104658373)
                      ·
                        rfl

theorem cell23_1055495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_1055495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055495 prefixEnd_1055495 := by exact prefixLift 1055495
  have htrace : WordTrace (prefixWord ++ tailWord_1055495) baseStart_1055495 baseEnd_1055495 := by
    simpa [prefixWord, tailWord_1055495, baseEnd_1055495] using wordTrace_append hprefix tailTrace_1055495
  have hstable : (prefixWord ++ tailWord_1055495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055495).length < 2 ^ (prefixWord ++ tailWord_1055495).sum := by decide
  have hdescent : baseEnd_1055495 < baseStart_1055495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055525 : List Nat := [1, 3, 1, 2, 3, 1, 1, 5, 2, 1, 3]
def baseStart_1055525 : Nat := 118140960795 + 1055525 * 2 ^ 59
def prefixEnd_1055525 : Nat := 4983230072969 + 3 ^ 40 * 1055525 * 2
def baseEnd_1055525 : Nat := 541991667837087987283235

theorem tailTrace_1055525 : CollatzResearch.WordTrace tailWord_1055525 prefixEnd_1055525 541991667837087987283235 := by
  unfold tailWord_1055525
  simp only [CollatzResearch.WordTrace]
  refine ⟨38498159501020669163136029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25665439667347112775424019 38498159501020669163136029)
  ·
    refine ⟨14436809812882750936176011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38498159501020669163136029 14436809812882750936176011)
    ·
      refine ⟨21655214719324126404264017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14436809812882750936176011 21655214719324126404264017)
      ·
        refine ⟨16241411039493094803198013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21655214719324126404264017 16241411039493094803198013)
        ·
          refine ⟨6090529139809910551199255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16241411039493094803198013 6090529139809910551199255)
          ·
            refine ⟨9135793709714865826798883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6090529139809910551199255 9135793709714865826798883)
            ·
              refine ⟨13703690564572298740198325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9135793709714865826798883 13703690564572298740198325)
              ·
                refine ⟨1284720990428653006893593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13703690564572298740198325 1284720990428653006893593)
                ·
                  refine ⟨963540742821489755170195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1284720990428653006893593 963540742821489755170195)
                  ·
                    refine ⟨1445311114232234632755293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 963540742821489755170195 1445311114232234632755293)
                    ·
                      refine ⟨541991667837087987283235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1445311114232234632755293 541991667837087987283235)
                      ·
                        rfl

theorem cell23_1055525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_1055525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055525 prefixEnd_1055525 := by exact prefixLift 1055525
  have htrace : WordTrace (prefixWord ++ tailWord_1055525) baseStart_1055525 baseEnd_1055525 := by
    simpa [prefixWord, tailWord_1055525, baseEnd_1055525] using wordTrace_append hprefix tailTrace_1055525
  have hstable : (prefixWord ++ tailWord_1055525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055525).length < 2 ^ (prefixWord ++ tailWord_1055525).sum := by decide
  have hdescent : baseEnd_1055525 < baseStart_1055525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055578 : List Nat := [3, 1, 1, 2, 1, 4, 2, 1, 2, 2, 4]
def baseStart_1055578 : Nat := 118140960795 + 1055578 * 2 ^ 59
def prefixEnd_1055578 : Nat := 4983230072969 + 3 ^ 40 * 1055578 * 2
def baseEnd_1055578 : Nat := 542018882311776279920491

theorem tailTrace_1055578 : CollatzResearch.WordTrace tailWord_1055578 prefixEnd_1055578 542018882311776279920491 := by
  unfold tailWord_1055578
  simp only [CollatzResearch.WordTrace]
  refine ⟨9625023142457164803703847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25666728379885772809876925 9625023142457164803703847)
  ·
    refine ⟨14437534713685747205555771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9625023142457164803703847 14437534713685747205555771)
    ·
      refine ⟨21656302070528620808333657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14437534713685747205555771 21656302070528620808333657)
      ·
        refine ⟨16242226552896465606250243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21656302070528620808333657 16242226552896465606250243)
        ·
          refine ⟨24363339829344698409375365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16242226552896465606250243 24363339829344698409375365)
          ·
            refine ⟨4568126218002130951757881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24363339829344698409375365 4568126218002130951757881)
            ·
              refine ⟨3426094663501598213818411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4568126218002130951757881 3426094663501598213818411)
              ·
                refine ⟨5139141995252397320727617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3426094663501598213818411 5139141995252397320727617)
                ·
                  refine ⟨3854356496439297990545713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5139141995252397320727617 3854356496439297990545713)
                  ·
                    refine ⟨2890767372329473492909285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3854356496439297990545713 2890767372329473492909285)
                    ·
                      refine ⟨542018882311776279920491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2890767372329473492909285 542018882311776279920491)
                      ·
                        rfl

theorem cell23_1055578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_1055578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055578 prefixEnd_1055578 := by exact prefixLift 1055578
  have htrace : WordTrace (prefixWord ++ tailWord_1055578) baseStart_1055578 baseEnd_1055578 := by
    simpa [prefixWord, tailWord_1055578, baseEnd_1055578] using wordTrace_append hprefix tailTrace_1055578
  have hstable : (prefixWord ++ tailWord_1055578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055578).length < 2 ^ (prefixWord ++ tailWord_1055578).sum := by decide
  have hdescent : baseEnd_1055578 < baseStart_1055578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055588 : List Nat := [2, 3, 1, 1, 4, 1, 2, 2, 7]
def baseStart_1055588 : Nat := 118140960795 + 1055588 * 2 ^ 59
def prefixEnd_1055588 : Nat := 4983230072969 + 3 ^ 40 * 1055588 * 2
def baseEnd_1055588 : Nat := 60224890790924582310605

theorem tailTrace_1055588 : CollatzResearch.WordTrace tailWord_1055588 prefixEnd_1055588 60224890790924582310605 := by
  unfold tailWord_1055588
  simp only [CollatzResearch.WordTrace]
  refine ⟨19250228649896215461339709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25666971533194953948452945 19250228649896215461339709)
  ·
    refine ⟨7218835743711080798002391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19250228649896215461339709 7218835743711080798002391)
    ·
      refine ⟨10828253615566621197003587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7218835743711080798002391 10828253615566621197003587)
      ·
        refine ⟨16242380423349931795505381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10828253615566621197003587 16242380423349931795505381)
        ·
          refine ⟨3045446329378112211657259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16242380423349931795505381 3045446329378112211657259)
          ·
            refine ⟨4568169494067168317485889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3045446329378112211657259 4568169494067168317485889)
            ·
              refine ⟨3426127120550376238114417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4568169494067168317485889 3426127120550376238114417)
              ·
                refine ⟨2569595340412782178585813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3426127120550376238114417 2569595340412782178585813)
                ·
                  refine ⟨60224890790924582310605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2569595340412782178585813 60224890790924582310605)
                  ·
                    rfl

theorem cell23_1055588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 7].length) (baseStart_1055588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055588 prefixEnd_1055588 := by exact prefixLift 1055588
  have htrace : WordTrace (prefixWord ++ tailWord_1055588) baseStart_1055588 baseEnd_1055588 := by
    simpa [prefixWord, tailWord_1055588, baseEnd_1055588] using wordTrace_append hprefix tailTrace_1055588
  have hstable : (prefixWord ++ tailWord_1055588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055588).length < 2 ^ (prefixWord ++ tailWord_1055588).sum := by decide
  have hdescent : baseEnd_1055588 < baseStart_1055588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055709 : List Nat := [1, 4, 3, 1, 2, 3, 1, 1, 2, 2, 3]
def baseStart_1055709 : Nat := 118140960795 + 1055709 * 2 ^ 59
def prefixEnd_1055709 : Nat := 4983230072969 + 3 ^ 40 * 1055709 * 2
def baseEnd_1055709 : Nat := 542086148277515267382389

theorem tailTrace_1055709 : CollatzResearch.WordTrace tailWord_1055709 prefixEnd_1055709 542086148277515267382389 := by
  unfold tailWord_1055709
  simp only [CollatzResearch.WordTrace]
  refine ⟨38504870532354068587834181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25669913688236045725222787 38504870532354068587834181)
  ·
    refine ⟨7219663224816387860218909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38504870532354068587834181 7219663224816387860218909)
    ·
      refine ⟨2707373709306145447582091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7219663224816387860218909 2707373709306145447582091)
      ·
        refine ⟨4061060563959218171373137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2707373709306145447582091 4061060563959218171373137)
        ·
          refine ⟨3045795422969413628529853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4061060563959218171373137 3045795422969413628529853)
          ·
            refine ⟨1142173283613530110698695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3045795422969413628529853 1142173283613530110698695)
            ·
              refine ⟨1713259925420295166048043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1142173283613530110698695 1713259925420295166048043)
              ·
                refine ⟨2569889888130442749072065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1713259925420295166048043 2569889888130442749072065)
                ·
                  refine ⟨1927417416097832061804049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2569889888130442749072065 1927417416097832061804049)
                  ·
                    refine ⟨1445563062073374046353037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1927417416097832061804049 1445563062073374046353037)
                    ·
                      refine ⟨542086148277515267382389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1445563062073374046353037 542086148277515267382389)
                      ·
                        rfl

theorem cell23_1055709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_1055709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055709 prefixEnd_1055709 := by exact prefixLift 1055709
  have htrace : WordTrace (prefixWord ++ tailWord_1055709) baseStart_1055709 baseEnd_1055709 := by
    simpa [prefixWord, tailWord_1055709, baseEnd_1055709] using wordTrace_append hprefix tailTrace_1055709
  have hstable : (prefixWord ++ tailWord_1055709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055709).length < 2 ^ (prefixWord ++ tailWord_1055709).sum := by decide
  have hdescent : baseEnd_1055709 < baseStart_1055709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055738 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 3, 6]
def baseStart_1055738 : Nat := 118140960795 + 1055738 * 2 ^ 59
def prefixEnd_1055738 : Nat := 4983230072969 + 3 ^ 40 * 1055738 * 2
def baseEnd_1055738 : Nat := 180700346405498551306585

theorem tailTrace_1055738 : CollatzResearch.WordTrace tailWord_1055738 prefixEnd_1055738 180700346405498551306585 := by
  unfold tailWord_1055738
  simp only [CollatzResearch.WordTrace]
  refine ⟨9626482062312251635159967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25670618832832671027093245 9626482062312251635159967)
  ·
    refine ⟨14439723093468377452739951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9626482062312251635159967 14439723093468377452739951)
    ·
      refine ⟨21659584640202566179109927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14439723093468377452739951 21659584640202566179109927)
      ·
        refine ⟨32489376960303849268664891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21659584640202566179109927 32489376960303849268664891)
        ·
          refine ⟨48734065440455773902997337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32489376960303849268664891 48734065440455773902997337)
          ·
            refine ⟨36550549080341830427248003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48734065440455773902997337 36550549080341830427248003)
            ·
              refine ⟨54825823620512745640872005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36550549080341830427248003 54825823620512745640872005)
              ·
                refine ⟨10279841928846139807663501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54825823620512745640872005 10279841928846139807663501)
                ·
                  refine ⟨3854940723317302427873813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10279841928846139807663501 3854940723317302427873813)
                  ·
                    refine ⟨180700346405498551306585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3854940723317302427873813 180700346405498551306585)
                    ·
                      rfl

theorem cell23_1055738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 3, 6].length) (baseStart_1055738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055738 prefixEnd_1055738 := by exact prefixLift 1055738
  have htrace : WordTrace (prefixWord ++ tailWord_1055738) baseStart_1055738 baseEnd_1055738 := by
    simpa [prefixWord, tailWord_1055738, baseEnd_1055738] using wordTrace_append hprefix tailTrace_1055738
  have hstable : (prefixWord ++ tailWord_1055738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055738).length < 2 ^ (prefixWord ++ tailWord_1055738).sum := by decide
  have hdescent : baseEnd_1055738 < baseStart_1055738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055746 : List Nat := [3, 4, 1, 3, 1, 1, 3, 1, 6]
def baseStart_1055746 : Nat := 118140960795 + 1055746 * 2 ^ 59
def prefixEnd_1055746 : Nat := 4983230072969 + 3 ^ 40 * 1055746 * 2
def baseEnd_1055746 : Nat := 60233905229081291402191

theorem tailTrace_1055746 : CollatzResearch.WordTrace tailWord_1055746 prefixEnd_1055746 60233905229081291402191 := by
  unfold tailWord_1055746
  simp only [CollatzResearch.WordTrace]
  refine ⟨9626555008305005976732773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25670813355480015937954061 9626555008305005976732773)
  ·
    refine ⟨1804979064057188620637395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9626555008305005976732773 1804979064057188620637395)
    ·
      refine ⟨2707468596085782930956093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1804979064057188620637395 2707468596085782930956093)
      ·
        refine ⟨1015300723532168599108535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2707468596085782930956093 1015300723532168599108535)
        ·
          refine ⟨1522951085298252898662803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1015300723532168599108535 1522951085298252898662803)
          ·
            refine ⟨2284426627947379347994205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1522951085298252898662803 2284426627947379347994205)
            ·
              refine ⟨856659985480267255497827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2284426627947379347994205 856659985480267255497827)
              ·
                refine ⟨1284989978220400883246741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 856659985480267255497827 1284989978220400883246741)
                ·
                  refine ⟨60233905229081291402191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1284989978220400883246741 60233905229081291402191)
                  ·
                    rfl

theorem cell23_1055746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_1055746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055746 prefixEnd_1055746 := by exact prefixLift 1055746
  have htrace : WordTrace (prefixWord ++ tailWord_1055746) baseStart_1055746 baseEnd_1055746 := by
    simpa [prefixWord, tailWord_1055746, baseEnd_1055746] using wordTrace_append hprefix tailTrace_1055746
  have hstable : (prefixWord ++ tailWord_1055746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055746).length < 2 ^ (prefixWord ++ tailWord_1055746).sum := by decide
  have hdescent : baseEnd_1055746 < baseStart_1055746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055755 : List Nat := [1, 1, 1, 1, 6, 2, 3, 1, 1, 6]
def baseStart_1055755 : Nat := 118140960795 + 1055755 * 2 ^ 59
def prefixEnd_1055755 : Nat := 4983230072969 + 3 ^ 40 * 1055755 * 2
def baseEnd_1055755 : Nat := 180703256129207362469059

theorem tailTrace_1055755 : CollatzResearch.WordTrace tailWord_1055755 prefixEnd_1055755 180703256129207362469059 := by
  unfold tailWord_1055755
  simp only [CollatzResearch.WordTrace]
  refine ⟨38506548290187418444008719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25671032193458278962672479 38506548290187418444008719)
  ·
    refine ⟨57759822435281127666013079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38506548290187418444008719 57759822435281127666013079)
    ·
      refine ⟨86639733652921691499019619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57759822435281127666013079 86639733652921691499019619)
      ·
        refine ⟨129959600479382537248529429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86639733652921691499019619 129959600479382537248529429)
        ·
          refine ⟨6091856272471056433524817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 129959600479382537248529429 6091856272471056433524817)
          ·
            refine ⟨4568892204353292325143613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6091856272471056433524817 4568892204353292325143613)
            ·
              refine ⟨1713334576632484621928855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4568892204353292325143613 1713334576632484621928855)
              ·
                refine ⟨2570001864948726932893283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1713334576632484621928855 2570001864948726932893283)
                ·
                  refine ⟨3855002797423090399339925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2570001864948726932893283 3855002797423090399339925)
                  ·
                    refine ⟨180703256129207362469059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3855002797423090399339925 180703256129207362469059)
                    ·
                      rfl

theorem cell23_1055755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 6].length) (baseStart_1055755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055755 prefixEnd_1055755 := by exact prefixLift 1055755
  have htrace : WordTrace (prefixWord ++ tailWord_1055755) baseStart_1055755 baseEnd_1055755 := by
    simpa [prefixWord, tailWord_1055755, baseEnd_1055755] using wordTrace_append hprefix tailTrace_1055755
  have hstable : (prefixWord ++ tailWord_1055755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055755).length < 2 ^ (prefixWord ++ tailWord_1055755).sum := by decide
  have hdescent : baseEnd_1055755 < baseStart_1055755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055773 : List Nat := [1, 4, 2, 2, 3, 2, 1, 3, 1, 1, 3]
def baseStart_1055773 : Nat := 118140960795 + 1055773 * 2 ^ 59
def prefixEnd_1055773 : Nat := 4983230072969 + 3 ^ 40 * 1055773 * 2
def baseEnd_1055773 : Nat := 542119011039403016982095

theorem tailTrace_1055773 : CollatzResearch.WordTrace tailWord_1055773 prefixEnd_1055773 542119011039403016982095 := by
  unfold tailWord_1055773
  simp only [CollatzResearch.WordTrace]
  refine ⟨38507204804122207518163973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25671469869414805012109315 38507204804122207518163973)
  ·
    refine ⟨7220100900772913909655745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38507204804122207518163973 7220100900772913909655745)
    ·
      refine ⟨5415075675579685432241809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7220100900772913909655745 5415075675579685432241809)
      ·
        refine ⟨4061306756684764074181357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5415075675579685432241809 4061306756684764074181357)
        ·
          refine ⟨1522990033756786527818009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4061306756684764074181357 1522990033756786527818009)
          ·
            refine ⟨1142242525317589895863507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1522990033756786527818009 1142242525317589895863507)
            ·
              refine ⟨1713363787976384843795261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1142242525317589895863507 1713363787976384843795261)
              ·
                refine ⟨642511420491144316423223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1713363787976384843795261 642511420491144316423223)
                ·
                  refine ⟨963767130736716474634835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 642511420491144316423223 963767130736716474634835)
                  ·
                    refine ⟨1445650696105074711952253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 963767130736716474634835 1445650696105074711952253)
                    ·
                      refine ⟨542119011039403016982095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1445650696105074711952253 542119011039403016982095)
                      ·
                        rfl

theorem cell23_1055773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_1055773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055773 prefixEnd_1055773 := by exact prefixLift 1055773
  have htrace : WordTrace (prefixWord ++ tailWord_1055773) baseStart_1055773 baseEnd_1055773 := by
    simpa [prefixWord, tailWord_1055773, baseEnd_1055773] using wordTrace_append hprefix tailTrace_1055773
  have hstable : (prefixWord ++ tailWord_1055773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055773).length < 2 ^ (prefixWord ++ tailWord_1055773).sum := by decide
  have hdescent : baseEnd_1055773 < baseStart_1055773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055806 : List Nat := [4, 2, 1, 3, 1, 1, 4, 1, 2, 4]
def baseStart_1055806 : Nat := 118140960795 + 1055806 * 2 ^ 59
def prefixEnd_1055806 : Nat := 4983230072969 + 3 ^ 40 * 1055806 * 2
def baseEnd_1055806 : Nat := 180711985300333795956481

theorem tailTrace_1055806 : CollatzResearch.WordTrace tailWord_1055806 prefixEnd_1055806 180711985300333795956481 := by
  unfold tailWord_1055806
  simp only [CollatzResearch.WordTrace]
  refine ⟨4813551051625331769264409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25672272275335102769410181 4813551051625331769264409)
  ·
    refine ⟨3610163288718998826948307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4813551051625331769264409 3610163288718998826948307)
    ·
      refine ⟨5415244933078498240422461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3610163288718998826948307 5415244933078498240422461)
      ·
        refine ⟨2030716849904436840158423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5415244933078498240422461 2030716849904436840158423)
        ·
          refine ⟨3046075274856655260237635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2030716849904436840158423 3046075274856655260237635)
          ·
            refine ⟨4569112912284982890356453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3046075274856655260237635 4569112912284982890356453)
            ·
              refine ⟨856708671053434291941835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4569112912284982890356453 856708671053434291941835)
              ·
                refine ⟨1285063006580151437912753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 856708671053434291941835 1285063006580151437912753)
                ·
                  refine ⟨963797254935113578434565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1285063006580151437912753 963797254935113578434565)
                  ·
                    refine ⟨180711985300333795956481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 963797254935113578434565 180711985300333795956481)
                    ·
                      rfl

theorem cell23_1055806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_1055806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055806 prefixEnd_1055806 := by exact prefixLift 1055806
  have htrace : WordTrace (prefixWord ++ tailWord_1055806) baseStart_1055806 baseEnd_1055806 := by
    simpa [prefixWord, tailWord_1055806, baseEnd_1055806] using wordTrace_append hprefix tailTrace_1055806
  have hstable : (prefixWord ++ tailWord_1055806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055806).length < 2 ^ (prefixWord ++ tailWord_1055806).sum := by decide
  have hdescent : baseEnd_1055806 < baseStart_1055806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055845 : List Nat := [1, 3, 1, 3, 2, 1, 2, 2, 2, 6]
def baseStart_1055845 : Nat := 118140960795 + 1055845 * 2 ^ 59
def prefixEnd_1055845 : Nat := 4983230072969 + 3 ^ 40 * 1055845 * 2
def baseEnd_1055845 : Nat := 180718660548842245093921

theorem tailTrace_1055845 : CollatzResearch.WordTrace tailWord_1055845 prefixEnd_1055845 180718660548842245093921 := by
  unfold tailWord_1055845
  simp only [CollatzResearch.WordTrace]
  refine ⟨38509830859861363814784989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25673220573240909209856659 38509830859861363814784989)
  ·
    refine ⟨14441186572448011430544371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38509830859861363814784989 14441186572448011430544371)
    ·
      refine ⟨21661779858672017145816557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14441186572448011430544371 21661779858672017145816557)
      ·
        refine ⟨8123167447002006429681209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21661779858672017145816557 8123167447002006429681209)
        ·
          refine ⟨6092375585251504822260907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8123167447002006429681209 6092375585251504822260907)
          ·
            refine ⟨9138563377877257233391361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6092375585251504822260907 9138563377877257233391361)
            ·
              refine ⟨6853922533407942925043521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9138563377877257233391361 6853922533407942925043521)
              ·
                refine ⟨5140441900055957193782641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6853922533407942925043521 5140441900055957193782641)
                ·
                  refine ⟨3855331425041967895336981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5140441900055957193782641 3855331425041967895336981)
                  ·
                    refine ⟨180718660548842245093921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3855331425041967895336981 180718660548842245093921)
                    ·
                      rfl

theorem cell23_1055845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 6].length) (baseStart_1055845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055845 prefixEnd_1055845 := by exact prefixLift 1055845
  have htrace : WordTrace (prefixWord ++ tailWord_1055845) baseStart_1055845 baseEnd_1055845 := by
    simpa [prefixWord, tailWord_1055845, baseEnd_1055845] using wordTrace_append hprefix tailTrace_1055845
  have hstable : (prefixWord ++ tailWord_1055845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055845).length < 2 ^ (prefixWord ++ tailWord_1055845).sum := by decide
  have hdescent : baseEnd_1055845 < baseStart_1055845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055852 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 3, 4, 2]
def baseStart_1055852 : Nat := 118140960795 + 1055852 * 2 ^ 59
def prefixEnd_1055852 : Nat := 4983230072969 + 3 ^ 40 * 1055852 * 2
def baseEnd_1055852 : Nat := 542159576011108207894231

theorem tailTrace_1055852 : CollatzResearch.WordTrace tailWord_1055852 prefixEnd_1055852 542159576011108207894231 := by
  unfold tailWord_1055852
  simp only [CollatzResearch.WordTrace]
  refine ⟨19255043085418002005144905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25673390780557336006859873 19255043085418002005144905)
  ·
    refine ⟨14441282314063501503858679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19255043085418002005144905 14441282314063501503858679)
    ·
      refine ⟨21661923471095252255788019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14441282314063501503858679 21661923471095252255788019)
      ·
        refine ⟨32492885206642878383682029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21661923471095252255788019 32492885206642878383682029)
        ·
          refine ⟨12184831952491079393880761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32492885206642878383682029 12184831952491079393880761)
          ·
            refine ⟨9138623964368309545410571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12184831952491079393880761 9138623964368309545410571)
            ·
              refine ⟨13707935946552464318115857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9138623964368309545410571 13707935946552464318115857)
              ·
                refine ⟨10280951959914348238586893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13707935946552464318115857 10280951959914348238586893)
                ·
                  refine ⟨3855356984967880589470085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10280951959914348238586893 3855356984967880589470085)
                  ·
                    refine ⟨722879434681477610525641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3855356984967880589470085 722879434681477610525641)
                    ·
                      refine ⟨542159576011108207894231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 722879434681477610525641 542159576011108207894231)
                      ·
                        rfl

theorem cell23_1055852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 4, 2].length) (baseStart_1055852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055852 prefixEnd_1055852 := by exact prefixLift 1055852
  have htrace : WordTrace (prefixWord ++ tailWord_1055852) baseStart_1055852 baseEnd_1055852 := by
    simpa [prefixWord, tailWord_1055852, baseEnd_1055852] using wordTrace_append hprefix tailTrace_1055852
  have hstable : (prefixWord ++ tailWord_1055852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055852).length < 2 ^ (prefixWord ++ tailWord_1055852).sum := by decide
  have hdescent : baseEnd_1055852 < baseStart_1055852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055855 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 1, 6, 3]
def baseStart_1055855 : Nat := 118140960795 + 1055855 * 2 ^ 59
def prefixEnd_1055855 : Nat := 4983230072969 + 3 ^ 40 * 1055855 * 2
def baseEnd_1055855 : Nat := 542161116453071696156717

theorem tailTrace_1055855 : CollatzResearch.WordTrace tailWord_1055855 prefixEnd_1055855 542161116453071696156717 := by
  unfold tailWord_1055855
  simp only [CollatzResearch.WordTrace]
  refine ⟨38510195589825135522649019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25673463726550090348432679 38510195589825135522649019)
  ·
    refine ⟨57765293384737703283973529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38510195589825135522649019 57765293384737703283973529)
    ·
      refine ⟨43323970038553277462980147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57765293384737703283973529 43323970038553277462980147)
      ·
        refine ⟨64985955057829916194470221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43323970038553277462980147 64985955057829916194470221)
        ·
          refine ⟨24369733146686218572926333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64985955057829916194470221 24369733146686218572926333)
          ·
            refine ⟨9138649930007331964847375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24369733146686218572926333 9138649930007331964847375)
            ·
              refine ⟨13707974895010997947271063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9138649930007331964847375 13707974895010997947271063)
              ·
                refine ⟨20561962342516496920906595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13707974895010997947271063 20561962342516496920906595)
                ·
                  refine ⟨30842943513774745381359893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20561962342516496920906595 30842943513774745381359893)
                  ·
                    refine ⟨1445762977208191189751245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30842943513774745381359893 1445762977208191189751245)
                    ·
                      refine ⟨542161116453071696156717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1445762977208191189751245 542161116453071696156717)
                      ·
                        rfl

theorem cell23_1055855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 6, 3].length) (baseStart_1055855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055855 prefixEnd_1055855 := by exact prefixLift 1055855
  have htrace : WordTrace (prefixWord ++ tailWord_1055855) baseStart_1055855 baseEnd_1055855 := by
    simpa [prefixWord, tailWord_1055855, baseEnd_1055855] using wordTrace_append hprefix tailTrace_1055855
  have hstable : (prefixWord ++ tailWord_1055855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055855).length < 2 ^ (prefixWord ++ tailWord_1055855).sum := by decide
  have hdescent : baseEnd_1055855 < baseStart_1055855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055862 : List Nat := [5, 1, 1, 2, 1, 1, 3, 1, 2, 6]
def baseStart_1055862 : Nat := 118140960795 + 1055862 * 2 ^ 59
def prefixEnd_1055862 : Nat := 4983230072969 + 3 ^ 40 * 1055862 * 2
def baseEnd_1055862 : Nat := 180721570272551056256395

theorem tailTrace_1055862 : CollatzResearch.WordTrace tailWord_1055862 prefixEnd_1055862 180721570272551056256395 := by
  unfold tailWord_1055862
  simp only [CollatzResearch.WordTrace]
  refine ⟨2406903181299985982384615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25673633933866517145435893 2406903181299985982384615)
  ·
    refine ⟨3610354771949978973576923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2406903181299985982384615 3610354771949978973576923)
    ·
      refine ⟨5415532157924968460365385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3610354771949978973576923 5415532157924968460365385)
      ·
        refine ⟨4061649118443726345274039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5415532157924968460365385 4061649118443726345274039)
        ·
          refine ⟨6092473677665589517911059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4061649118443726345274039 6092473677665589517911059)
          ·
            refine ⟨9138710516498384276866589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6092473677665589517911059 9138710516498384276866589)
            ·
              refine ⟨3427016443686894103824971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9138710516498384276866589 3427016443686894103824971)
              ·
                refine ⟨5140524665530341155737457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3427016443686894103824971 5140524665530341155737457)
                ·
                  refine ⟨3855393499147755866803093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5140524665530341155737457 3855393499147755866803093)
                  ·
                    refine ⟨180721570272551056256395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3855393499147755866803093 180721570272551056256395)
                    ·
                      rfl

theorem cell23_1055862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_1055862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055862 prefixEnd_1055862 := by exact prefixLift 1055862
  have htrace : WordTrace (prefixWord ++ tailWord_1055862) baseStart_1055862 baseEnd_1055862 := by
    simpa [prefixWord, tailWord_1055862, baseEnd_1055862] using wordTrace_append hprefix tailTrace_1055862
  have hstable : (prefixWord ++ tailWord_1055862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055862).length < 2 ^ (prefixWord ++ tailWord_1055862).sum := by decide
  have hdescent : baseEnd_1055862 < baseStart_1055862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055869 : List Nat := [1, 4, 1, 1, 3, 1, 4, 1, 1, 4, 2]
def baseStart_1055869 : Nat := 118140960795 + 1055869 * 2 ^ 59
def prefixEnd_1055869 : Nat := 4983230072969 + 3 ^ 40 * 1055869 * 2
def baseEnd_1055869 : Nat := 542168305182234641381653

theorem tailTrace_1055869 : CollatzResearch.WordTrace tailWord_1055869 prefixEnd_1055869 542168305182234641381653 := by
  unfold tailWord_1055869
  simp only [CollatzResearch.WordTrace]
  refine ⟨38510706211774415913658661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25673804141182943942439107 38510706211774415913658661)
  ·
    refine ⟨7220757414707702983810999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38510706211774415913658661 7220757414707702983810999)
    ·
      refine ⟨10831136122061554475716499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7220757414707702983810999 10831136122061554475716499)
      ·
        refine ⟨16246704183092331713574749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10831136122061554475716499 16246704183092331713574749)
        ·
          refine ⟨6092514068659624392590531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16246704183092331713574749 6092514068659624392590531)
          ·
            refine ⟨9138771102989436588885797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6092514068659624392590531 9138771102989436588885797)
            ·
              refine ⟨1713519581810519360416087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9138771102989436588885797 1713519581810519360416087)
              ·
                refine ⟨2570279372715779040624131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1713519581810519360416087 2570279372715779040624131)
                ·
                  refine ⟨3855419059073668560936197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2570279372715779040624131 3855419059073668560936197)
                  ·
                    refine ⟨722891073576312855175537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3855419059073668560936197 722891073576312855175537)
                    ·
                      refine ⟨542168305182234641381653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 722891073576312855175537 542168305182234641381653)
                      ·
                        rfl

theorem cell23_1055869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 4, 2].length) (baseStart_1055869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055869 prefixEnd_1055869 := by exact prefixLift 1055869
  have htrace : WordTrace (prefixWord ++ tailWord_1055869) baseStart_1055869 baseEnd_1055869 := by
    simpa [prefixWord, tailWord_1055869, baseEnd_1055869] using wordTrace_append hprefix tailTrace_1055869
  have hstable : (prefixWord ++ tailWord_1055869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055869).length < 2 ^ (prefixWord ++ tailWord_1055869).sum := by decide
  have hdescent : baseEnd_1055869 < baseStart_1055869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055875 : List Nat := [1, 1, 1, 3, 3, 2, 3, 2, 7]
def baseStart_1055875 : Nat := 118140960795 + 1055875 * 2 ^ 59
def prefixEnd_1055875 : Nat := 4983230072969 + 3 ^ 40 * 1055875 * 2
def baseEnd_1055875 : Nat := 60241265118462401989625

theorem tailTrace_1055875 : CollatzResearch.WordTrace tailWord_1055875 prefixEnd_1055875 60241265118462401989625 := by
  unfold tailWord_1055875
  simp only [CollatzResearch.WordTrace]
  refine ⟨38510925049752678938377079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25673950033168452625584719 38510925049752678938377079)
  ·
    refine ⟨57766387574629018407565619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38510925049752678938377079 57766387574629018407565619)
    ·
      refine ⟨86649581361943527611348429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57766387574629018407565619 86649581361943527611348429)
      ·
        refine ⟨32493593010728822854255661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86649581361943527611348429 32493593010728822854255661)
        ·
          refine ⟨12185097379023308570345873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32493593010728822854255661 12185097379023308570345873)
          ·
            refine ⟨9138823034267481427759405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12185097379023308570345873 9138823034267481427759405)
            ·
              refine ⟨3427058637850305535409777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9138823034267481427759405 3427058637850305535409777)
              ·
                refine ⟨2570293978387729151557333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3427058637850305535409777 2570293978387729151557333)
                ·
                  refine ⟨60241265118462401989625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2570293978387729151557333 60241265118462401989625)
                  ·
                    rfl

theorem cell23_1055875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 7].length) (baseStart_1055875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055875 prefixEnd_1055875 := by exact prefixLift 1055875
  have htrace : WordTrace (prefixWord ++ tailWord_1055875) baseStart_1055875 baseEnd_1055875 := by
    simpa [prefixWord, tailWord_1055875, baseEnd_1055875] using wordTrace_append hprefix tailTrace_1055875
  have hstable : (prefixWord ++ tailWord_1055875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055875).length < 2 ^ (prefixWord ++ tailWord_1055875).sum := by decide
  have hdescent : baseEnd_1055875 < baseStart_1055875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055955 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 4]
def baseStart_1055955 : Nat := 118140960795 + 1055955 * 2 ^ 59
def prefixEnd_1055955 : Nat := 4983230072969 + 3 ^ 40 * 1055955 * 2
def baseEnd_1055955 : Nat := 542212464518521304906257

theorem tailTrace_1055955 : CollatzResearch.WordTrace tailWord_1055955 prefixEnd_1055955 542212464518521304906257 := by
  unfold tailWord_1055955
  simp only [CollatzResearch.WordTrace]
  refine ⟨38513842889462852601289319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25675895259641901734192879 38513842889462852601289319)
  ·
    refine ⟨57770764334194278901933979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38513842889462852601289319 57770764334194278901933979)
    ·
      refine ⟨86656146501291418352900969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57770764334194278901933979 86656146501291418352900969)
      ·
        refine ⟨64992109875968563764675727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86656146501291418352900969 64992109875968563764675727)
        ·
          refine ⟨97488164813952845647013591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64992109875968563764675727 97488164813952845647013591)
          ·
            refine ⟨146232247220929268470520387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97488164813952845647013591 146232247220929268470520387)
            ·
              refine ⟨219348370831393902705780581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146232247220929268470520387 219348370831393902705780581)
              ·
                refine ⟨41127819530886356757333859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 219348370831393902705780581 41127819530886356757333859)
                ·
                  refine ⟨61691729296329535136000789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41127819530886356757333859 61691729296329535136000789)
                  ·
                    refine ⟨2891799810765446959500037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61691729296329535136000789 2891799810765446959500037)
                    ·
                      refine ⟨542212464518521304906257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2891799810765446959500037 542212464518521304906257)
                      ·
                        rfl

theorem cell23_1055955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 4].length) (baseStart_1055955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055955 prefixEnd_1055955 := by exact prefixLift 1055955
  have htrace : WordTrace (prefixWord ++ tailWord_1055955) baseStart_1055955 baseEnd_1055955 := by
    simpa [prefixWord, tailWord_1055955, baseEnd_1055955] using wordTrace_append hprefix tailTrace_1055955
  have hstable : (prefixWord ++ tailWord_1055955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055955).length < 2 ^ (prefixWord ++ tailWord_1055955).sum := by decide
  have hdescent : baseEnd_1055955 < baseStart_1055955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055956 : List Nat := [2, 4, 1, 4, 1, 1, 1, 2, 2, 5]
def baseStart_1055956 : Nat := 118140960795 + 1055956 * 2 ^ 59
def prefixEnd_1055956 : Nat := 4983230072969 + 3 ^ 40 * 1055956 * 2
def baseEnd_1055956 : Nat := 180737659333058600331251

theorem tailTrace_1055956 : CollatzResearch.WordTrace tailWord_1055956 prefixEnd_1055956 180737659333058600331251 := by
  unfold tailWord_1055956
  simp only [CollatzResearch.WordTrace]
  refine ⟨19256939681229614886037861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25675919574972819848050481 19256939681229614886037861)
  ·
    refine ⟨3610676190230552791132099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19256939681229614886037861 3610676190230552791132099)
    ·
      refine ⟨5416014285345829186698149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3610676190230552791132099 5416014285345829186698149)
      ·
        refine ⟨1015502678502342972505903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5416014285345829186698149 1015502678502342972505903)
        ·
          refine ⟨1523254017753514458758855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1015502678502342972505903 1523254017753514458758855)
          ·
            refine ⟨2284881026630271688138283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1523254017753514458758855 2284881026630271688138283)
            ·
              refine ⟨3427321539945407532207425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2284881026630271688138283 3427321539945407532207425)
              ·
                refine ⟨2570491154959055649155569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3427321539945407532207425 2570491154959055649155569)
                ·
                  refine ⟨1927868366219291736866677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2570491154959055649155569 1927868366219291736866677)
                  ·
                    refine ⟨180737659333058600331251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1927868366219291736866677 180737659333058600331251)
                    ·
                      rfl

theorem cell23_1055956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_1055956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055956 prefixEnd_1055956 := by exact prefixLift 1055956
  have htrace : WordTrace (prefixWord ++ tailWord_1055956) baseStart_1055956 baseEnd_1055956 := by
    simpa [prefixWord, tailWord_1055956, baseEnd_1055956] using wordTrace_append hprefix tailTrace_1055956
  have hstable : (prefixWord ++ tailWord_1055956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055956).length < 2 ^ (prefixWord ++ tailWord_1055956).sum := by decide
  have hdescent : baseEnd_1055956 < baseStart_1055956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055969 : List Nat := [1, 2, 3, 1, 3, 2, 3, 1, 3, 4]
def baseStart_1055969 : Nat := 118140960795 + 1055969 * 2 ^ 59
def prefixEnd_1055969 : Nat := 4983230072969 + 3 ^ 40 * 1055969 * 2
def baseEnd_1055969 : Nat := 180739884415894750043731

theorem tailTrace_1055969 : CollatzResearch.WordTrace tailWord_1055969 prefixEnd_1055969 180739884415894750043731 := by
  unfold tailWord_1055969
  simp only [CollatzResearch.WordTrace]
  refine ⟨38514353511412132992298961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25676235674274755328199307 38514353511412132992298961)
  ·
    refine ⟨28885765133559099744224221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38514353511412132992298961 28885765133559099744224221)
    ·
      refine ⟨10832161925084662404084083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28885765133559099744224221 10832161925084662404084083)
      ·
        refine ⟨16248242887626993606126125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10832161925084662404084083 16248242887626993606126125)
        ·
          refine ⟨6093091082860122602297297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16248242887626993606126125 6093091082860122602297297)
          ·
            refine ⟨4569818312145091951722973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6093091082860122602297297 4569818312145091951722973)
            ·
              refine ⟨1713681867054409481896115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4569818312145091951722973 1713681867054409481896115)
              ·
                refine ⟨2570522800581614222844173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1713681867054409481896115 2570522800581614222844173)
                ·
                  refine ⟨963946050218105333566565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2570522800581614222844173 963946050218105333566565)
                  ·
                    refine ⟨180739884415894750043731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 963946050218105333566565 180739884415894750043731)
                    ·
                      rfl

theorem cell23_1055969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_1055969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055969 prefixEnd_1055969 := by exact prefixLift 1055969
  have htrace : WordTrace (prefixWord ++ tailWord_1055969) baseStart_1055969 baseEnd_1055969 := by
    simpa [prefixWord, tailWord_1055969, baseEnd_1055969] using wordTrace_append hprefix tailTrace_1055969
  have hstable : (prefixWord ++ tailWord_1055969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055969).length < 2 ^ (prefixWord ++ tailWord_1055969).sum := by decide
  have hdescent : baseEnd_1055969 < baseStart_1055969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055996 : List Nat := [2, 2, 2, 1, 5, 1, 2, 1, 2, 2, 3]
def baseStart_1055996 : Nat := 118140960795 + 1055996 * 2 ^ 59
def prefixEnd_1055996 : Nat := 4983230072969 + 3 ^ 40 * 1055996 * 2
def baseEnd_1055996 : Nat := 542233517225355644493569

theorem tailTrace_1055996 : CollatzResearch.WordTrace tailWord_1055996 prefixEnd_1055996 542233517225355644493569 := by
  unfold tailWord_1055996
  simp only [CollatzResearch.WordTrace]
  refine ⟨19257669141157158301765921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25676892188209544402354561 19257669141157158301765921)
  ·
    refine ⟨14443251855867868726324441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19257669141157158301765921 14443251855867868726324441)
    ·
      refine ⟨10832438891900901544743331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14443251855867868726324441 10832438891900901544743331)
      ·
        refine ⟨16248658337851352317114997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10832438891900901544743331 16248658337851352317114997)
        ·
          refine ⟨1523311719173564279729531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16248658337851352317114997 1523311719173564279729531)
          ·
            refine ⟨2284967578760346419594297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1523311719173564279729531 2284967578760346419594297)
            ·
              refine ⟨1713725684070259814695723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2284967578760346419594297 1713725684070259814695723)
              ·
                refine ⟨2570588526105389722043585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1713725684070259814695723 2570588526105389722043585)
                ·
                  refine ⟨1927941394579042291532689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2570588526105389722043585 1927941394579042291532689)
                  ·
                    refine ⟨1445956045934281718649517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1927941394579042291532689 1445956045934281718649517)
                    ·
                      refine ⟨542233517225355644493569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1445956045934281718649517 542233517225355644493569)
                      ·
                        rfl

theorem cell23_1055996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_1055996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1055996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1055996 prefixEnd_1055996 := by exact prefixLift 1055996
  have htrace : WordTrace (prefixWord ++ tailWord_1055996) baseStart_1055996 baseEnd_1055996 := by
    simpa [prefixWord, tailWord_1055996, baseEnd_1055996] using wordTrace_append hprefix tailTrace_1055996
  have hstable : (prefixWord ++ tailWord_1055996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055996).length < 2 ^ (prefixWord ++ tailWord_1055996).sum := by decide
  have hdescent : baseEnd_1055996 < baseStart_1055996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056029 : List Nat := [1, 4, 2, 3, 1, 1, 1, 2, 3, 5]
def baseStart_1056029 : Nat := 118140960795 + 1056029 * 2 ^ 59
def prefixEnd_1056029 : Nat := 4983230072969 + 3 ^ 40 * 1056029 * 2
def baseEnd_1056029 : Nat := 180750154028984671793639

theorem tailTrace_1056029 : CollatzResearch.WordTrace tailWord_1056029 prefixEnd_1056029 180750154028984671793639 := by
  unfold tailWord_1056029
  simp only [CollatzResearch.WordTrace]
  refine ⟨38516541891194763239483141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25677694594129842159655427 38516541891194763239483141)
  ·
    refine ⟨7221851604599018107403089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38516541891194763239483141 7221851604599018107403089)
    ·
      refine ⟨5416388703449263580552317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7221851604599018107403089 5416388703449263580552317)
      ·
        refine ⟨2031145763793473842707119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5416388703449263580552317 2031145763793473842707119)
        ·
          refine ⟨3046718645690210764060679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2031145763793473842707119 3046718645690210764060679)
          ·
            refine ⟨4570077968535316146091019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3046718645690210764060679 4570077968535316146091019)
            ·
              refine ⟨6855116952802974219136529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4570077968535316146091019 6855116952802974219136529)
              ·
                refine ⟨5141337714602230664352397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6855116952802974219136529 5141337714602230664352397)
                ·
                  refine ⟨1928001642975836499132149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5141337714602230664352397 1928001642975836499132149)
                  ·
                    refine ⟨180750154028984671793639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1928001642975836499132149 180750154028984671793639)
                    ·
                      rfl

theorem cell23_1056029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_1056029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056029 prefixEnd_1056029 := by exact prefixLift 1056029
  have htrace : WordTrace (prefixWord ++ tailWord_1056029) baseStart_1056029 baseEnd_1056029 := by
    simpa [prefixWord, tailWord_1056029, baseEnd_1056029] using wordTrace_append hprefix tailTrace_1056029
  have hstable : (prefixWord ++ tailWord_1056029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056029).length < 2 ^ (prefixWord ++ tailWord_1056029).sum := by decide
  have hdescent : baseEnd_1056029 < baseStart_1056029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056049 : List Nat := [1, 2, 2, 3, 3, 1, 2, 1, 3, 1, 4]
def baseStart_1056049 : Nat := 118140960795 + 1056049 * 2 ^ 59
def prefixEnd_1056049 : Nat := 4983230072969 + 3 ^ 40 * 1056049 * 2
def baseEnd_1056049 : Nat := 542260731700043937130825

theorem tailTrace_1056049 : CollatzResearch.WordTrace tailWord_1056049 prefixEnd_1056049 542260731700043937130825 := by
  unfold tailWord_1056049
  simp only [CollatzResearch.WordTrace]
  refine ⟨38517271351122306655211201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25678180900748204436807467 38517271351122306655211201)
  ·
    refine ⟨28887953513341729991408401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38517271351122306655211201 28887953513341729991408401)
    ·
      refine ⟨21665965135006297493556301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28887953513341729991408401 21665965135006297493556301)
      ·
        refine ⟨8124736925627361560083613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21665965135006297493556301 8124736925627361560083613)
        ·
          refine ⟨3046776347110260585031355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8124736925627361560083613 3046776347110260585031355)
          ·
            refine ⟨4570164520665390877547033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3046776347110260585031355 4570164520665390877547033)
            ·
              refine ⟨3427623390499043158160275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4570164520665390877547033 3427623390499043158160275)
              ·
                refine ⟨5141435085748564737240413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3427623390499043158160275 5141435085748564737240413)
                ·
                  refine ⟨1928038157155711776465155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5141435085748564737240413 1928038157155711776465155)
                  ·
                    refine ⟨2892057235733567664697733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1928038157155711776465155 2892057235733567664697733)
                    ·
                      refine ⟨542260731700043937130825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2892057235733567664697733 542260731700043937130825)
                      ·
                        rfl

theorem cell23_1056049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_1056049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056049 prefixEnd_1056049 := by exact prefixLift 1056049
  have htrace : WordTrace (prefixWord ++ tailWord_1056049) baseStart_1056049 baseEnd_1056049 := by
    simpa [prefixWord, tailWord_1056049, baseEnd_1056049] using wordTrace_append hprefix tailTrace_1056049
  have hstable : (prefixWord ++ tailWord_1056049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056049).length < 2 ^ (prefixWord ++ tailWord_1056049).sum := by decide
  have hdescent : baseEnd_1056049 < baseStart_1056049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056053 : List Nat := [1, 3, 3, 1, 2, 4, 1, 1, 2, 3, 2]
def baseStart_1056053 : Nat := 118140960795 + 1056053 * 2 ^ 59
def prefixEnd_1056053 : Nat := 4983230072969 + 3 ^ 40 * 1056053 * 2
def baseEnd_1056053 : Nat := 542262785622661921480807

theorem tailTrace_1056053 : CollatzResearch.WordTrace tailWord_1056053 prefixEnd_1056053 542262785622661921480807 := by
  unfold tailWord_1056053
  simp only [CollatzResearch.WordTrace]
  refine ⟨38517417243107815338356813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25678278162071876892237875 38517417243107815338356813)
  ·
    refine ⟨14444031466165430751883805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38517417243107815338356813 14444031466165430751883805)
    ·
      refine ⟨5416511799812036531956427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14444031466165430751883805 5416511799812036531956427)
      ·
        refine ⟨8124767699718054797934641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5416511799812036531956427 8124767699718054797934641)
        ·
          refine ⟨6093575774788541098450981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8124767699718054797934641 6093575774788541098450981)
          ·
            refine ⟨1142545457772851455959559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6093575774788541098450981 1142545457772851455959559)
            ·
              refine ⟨1713818186659277183939339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1142545457772851455959559 1713818186659277183939339)
              ·
                refine ⟨2570727279988915775909009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1713818186659277183939339 2570727279988915775909009)
                ·
                  refine ⟨1928045459991686831931757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2570727279988915775909009 1928045459991686831931757)
                  ·
                    refine ⟨723017047496882561974409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1928045459991686831931757 723017047496882561974409)
                    ·
                      refine ⟨542262785622661921480807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 723017047496882561974409 542262785622661921480807)
                      ·
                        rfl

theorem cell23_1056053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_1056053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056053 prefixEnd_1056053 := by exact prefixLift 1056053
  have htrace : WordTrace (prefixWord ++ tailWord_1056053) baseStart_1056053 baseEnd_1056053 := by
    simpa [prefixWord, tailWord_1056053, baseEnd_1056053] using wordTrace_append hprefix tailTrace_1056053
  have hstable : (prefixWord ++ tailWord_1056053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056053).length < 2 ^ (prefixWord ++ tailWord_1056053).sum := by decide
  have hdescent : baseEnd_1056053 < baseStart_1056053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056076 : List Nat := [2, 2, 1, 3, 2, 2, 3, 2, 2, 4]
def baseStart_1056076 : Nat := 118140960795 + 1056076 * 2 ^ 59
def prefixEnd_1056076 : Nat := 4983230072969 + 3 ^ 40 * 1056076 * 2
def baseEnd_1056076 : Nat := 180758198559238443831067

theorem tailTrace_1056076 : CollatzResearch.WordTrace tailWord_1056076 prefixEnd_1056076 180758198559238443831067 := by
  unfold tailWord_1056076
  simp only [CollatzResearch.WordTrace]
  refine ⟨19259128061012245133222041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25678837414682993510962721 19259128061012245133222041)
  ·
    refine ⟨14444346045759183849916531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19259128061012245133222041 14444346045759183849916531)
    ·
      refine ⟨21666519068638775774874797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14444346045759183849916531 21666519068638775774874797)
      ·
        refine ⟨8124944650739540915578049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21666519068638775774874797 8124944650739540915578049)
        ·
          refine ⟨6093708488054655686683537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8124944650739540915578049 6093708488054655686683537)
          ·
            refine ⟨4570281366040991765012653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6093708488054655686683537 4570281366040991765012653)
            ·
              refine ⟨1713855512265371911879745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4570281366040991765012653 1713855512265371911879745)
              ·
                refine ⟨1285391634199028933909809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1713855512265371911879745 1285391634199028933909809)
                ·
                  refine ⟨964043725649271700432357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1285391634199028933909809 964043725649271700432357)
                  ·
                    refine ⟨180758198559238443831067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 964043725649271700432357 180758198559238443831067)
                    ·
                      rfl

theorem cell23_1056076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 2, 4].length) (baseStart_1056076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056076 prefixEnd_1056076 := by exact prefixLift 1056076
  have htrace : WordTrace (prefixWord ++ tailWord_1056076) baseStart_1056076 baseEnd_1056076 := by
    simpa [prefixWord, tailWord_1056076, baseEnd_1056076] using wordTrace_append hprefix tailTrace_1056076
  have hstable : (prefixWord ++ tailWord_1056076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056076).length < 2 ^ (prefixWord ++ tailWord_1056076).sum := by decide
  have hdescent : baseEnd_1056076 < baseStart_1056076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056082 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7]
def baseStart_1056082 : Nat := 118140960795 + 1056082 * 2 ^ 59
def prefixEnd_1056082 : Nat := 4983230072969 + 3 ^ 40 * 1056082 * 2
def baseEnd_1056082 : Nat := 542277676561642308018173

theorem tailTrace_1056082 : CollatzResearch.WordTrace tailWord_1056082 prefixEnd_1056082 542277676561642308018173 := by
  unfold tailWord_1056082
  simp only [CollatzResearch.WordTrace]
  refine ⟨9629618740000688322790625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25678983306668502194108333 9629618740000688322790625)
  ·
    refine ⟨7222214055000516242092969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9629618740000688322790625 7222214055000516242092969)
    ·
      refine ⟨5416660541250387181569727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7222214055000516242092969 5416660541250387181569727)
      ·
        refine ⟨8124990811875580772354591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5416660541250387181569727 8124990811875580772354591)
        ·
          refine ⟨12187486217813371158531887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8124990811875580772354591 12187486217813371158531887)
          ·
            refine ⟨18281229326720056737797831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12187486217813371158531887 18281229326720056737797831)
            ·
              refine ⟨27421843990080085106696747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18281229326720056737797831 27421843990080085106696747)
              ·
                refine ⟨41132765985120127660045121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27421843990080085106696747 41132765985120127660045121)
                ·
                  refine ⟨30849574488840095745033841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41132765985120127660045121 30849574488840095745033841)
                  ·
                    refine ⟨23137180866630071808775381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30849574488840095745033841 23137180866630071808775381)
                    ·
                      refine ⟨542277676561642308018173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 23137180866630071808775381 542277676561642308018173)
                      ·
                        rfl

theorem cell23_1056082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_1056082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056082 prefixEnd_1056082 := by exact prefixLift 1056082
  have htrace : WordTrace (prefixWord ++ tailWord_1056082) baseStart_1056082 baseEnd_1056082 := by
    simpa [prefixWord, tailWord_1056082, baseEnd_1056082] using wordTrace_append hprefix tailTrace_1056082
  have hstable : (prefixWord ++ tailWord_1056082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056082).length < 2 ^ (prefixWord ++ tailWord_1056082).sum := by decide
  have hdescent : baseEnd_1056082 < baseStart_1056082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056083 : List Nat := [1, 1, 1, 2, 1, 1, 5, 6, 1, 2, 2]
def baseStart_1056083 : Nat := 118140960795 + 1056083 * 2 ^ 59
def prefixEnd_1056083 : Nat := 4983230072969 + 3 ^ 40 * 1056083 * 2
def baseEnd_1056083 : Nat := 542278190042296804105669

theorem tailTrace_1056083 : CollatzResearch.WordTrace tailWord_1056083 prefixEnd_1056083 542278190042296804105669 := by
  unfold tailWord_1056083
  simp only [CollatzResearch.WordTrace]
  refine ⟨38518511432999130461948903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25679007621999420307965935 38518511432999130461948903)
  ·
    refine ⟨57777767149498695692923355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38518511432999130461948903 57777767149498695692923355)
    ·
      refine ⟨86666650724248043539385033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57777767149498695692923355 86666650724248043539385033)
      ·
        refine ⟨64999988043186032654538775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86666650724248043539385033 64999988043186032654538775)
        ·
          refine ⟨97499982064779048981808163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64999988043186032654538775 97499982064779048981808163)
          ·
            refine ⟨146249973097168573472712245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97499982064779048981808163 146249973097168573472712245)
            ·
              refine ⟨13710934977859553763066773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 146249973097168573472712245 13710934977859553763066773)
              ·
                refine ⟨642700077087166582643755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13710934977859553763066773 642700077087166582643755)
                ·
                  refine ⟨964050115630749873965633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 642700077087166582643755 964050115630749873965633)
                  ·
                    refine ⟨723037586723062405474225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 964050115630749873965633 723037586723062405474225)
                    ·
                      refine ⟨542278190042296804105669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 723037586723062405474225 542278190042296804105669)
                      ·
                        rfl

theorem cell23_1056083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 6, 1, 2, 2].length) (baseStart_1056083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056083 prefixEnd_1056083 := by exact prefixLift 1056083
  have htrace : WordTrace (prefixWord ++ tailWord_1056083) baseStart_1056083 baseEnd_1056083 := by
    simpa [prefixWord, tailWord_1056083, baseEnd_1056083] using wordTrace_append hprefix tailTrace_1056083
  have hstable : (prefixWord ++ tailWord_1056083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056083).length < 2 ^ (prefixWord ++ tailWord_1056083).sum := by decide
  have hdescent : baseEnd_1056083 < baseStart_1056083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056096 : List Nat := [2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 4]
def baseStart_1056096 : Nat := 118140960795 + 1056096 * 2 ^ 59
def prefixEnd_1056096 : Nat := 4983230072969 + 3 ^ 40 * 1056096 * 2
def baseEnd_1056096 : Nat := 542284865290805253243109

theorem tailTrace_1056096 : CollatzResearch.WordTrace tailWord_1056096 prefixEnd_1056096 542284865290805253243109 := by
  unfold tailWord_1056096
  simp only [CollatzResearch.WordTrace]
  refine ⟨19259492790976016841086071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25679323721301355788114761 19259492790976016841086071)
  ·
    refine ⟨28889239186464025261629107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19259492790976016841086071 28889239186464025261629107)
    ·
      refine ⟨43333858779696037892443661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28889239186464025261629107 43333858779696037892443661)
      ·
        refine ⟨16250197042386014209666373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43333858779696037892443661 16250197042386014209666373)
        ·
          refine ⟨3046911945447377664312445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16250197042386014209666373 3046911945447377664312445)
          ·
            refine ⟨1142591979542766624117167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3046911945447377664312445 1142591979542766624117167)
            ·
              refine ⟨1713887969314149936175751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1142591979542766624117167 1713887969314149936175751)
              ·
                refine ⟨2570831953971224904263627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1713887969314149936175751 2570831953971224904263627)
                ·
                  refine ⟨3856247930956837356395441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2570831953971224904263627 3856247930956837356395441)
                  ·
                    refine ⟨2892185948217628017296581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3856247930956837356395441 2892185948217628017296581)
                    ·
                      refine ⟨542284865290805253243109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2892185948217628017296581 542284865290805253243109)
                      ·
                        rfl

theorem cell23_1056096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_1056096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056096 prefixEnd_1056096 := by exact prefixLift 1056096
  have htrace : WordTrace (prefixWord ++ tailWord_1056096) baseStart_1056096 baseEnd_1056096 := by
    simpa [prefixWord, tailWord_1056096, baseEnd_1056096] using wordTrace_append hprefix tailTrace_1056096
  have hstable : (prefixWord ++ tailWord_1056096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056096).length < 2 ^ (prefixWord ++ tailWord_1056096).sum := by decide
  have hdescent : baseEnd_1056096 < baseStart_1056096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056103 : List Nat := [1, 1, 5, 1, 4, 1, 2, 2, 1, 2, 3]
def baseStart_1056103 : Nat := 118140960795 + 1056103 * 2 ^ 59
def prefixEnd_1056103 : Nat := 4983230072969 + 3 ^ 40 * 1056103 * 2
def baseEnd_1056103 : Nat := 542288459655386725855577

theorem tailTrace_1056103 : CollatzResearch.WordTrace tailWord_1056103 prefixEnd_1056103 542288459655386725855577 := by
  unfold tailWord_1056103
  simp only [CollatzResearch.WordTrace]
  refine ⟨38519240892926673877676963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25679493928617782585117975 38519240892926673877676963)
  ·
    refine ⟨57778861339390010816515445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38519240892926673877676963 57778861339390010816515445)
    ·
      refine ⟨5416768250567813514048323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57778861339390010816515445 5416768250567813514048323)
      ·
        refine ⟨8125152375851720271072485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5416768250567813514048323 8125152375851720271072485)
        ·
          refine ⟨1523466070472197550826091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8125152375851720271072485 1523466070472197550826091)
          ·
            refine ⟨2285199105708296326239137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1523466070472197550826091 2285199105708296326239137)
            ·
              refine ⟨1713899329281222244679353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2285199105708296326239137 1713899329281222244679353)
              ·
                refine ⟨1285424496960916683509515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1713899329281222244679353 1285424496960916683509515)
                ·
                  refine ⟨1928136745441375025264273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1285424496960916683509515 1928136745441375025264273)
                  ·
                    refine ⟨1446102559081031268948205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1928136745441375025264273 1446102559081031268948205)
                    ·
                      refine ⟨542288459655386725855577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1446102559081031268948205 542288459655386725855577)
                      ·
                        rfl

theorem cell23_1056103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_1056103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056103 prefixEnd_1056103 := by exact prefixLift 1056103
  have htrace : WordTrace (prefixWord ++ tailWord_1056103) baseStart_1056103 baseEnd_1056103 := by
    simpa [prefixWord, tailWord_1056103, baseEnd_1056103] using wordTrace_append hprefix tailTrace_1056103
  have hstable : (prefixWord ++ tailWord_1056103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056103).length < 2 ^ (prefixWord ++ tailWord_1056103).sum := by decide
  have hdescent : baseEnd_1056103 < baseStart_1056103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056112 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 5]
def baseStart_1056112 : Nat := 118140960795 + 1056112 * 2 ^ 59
def prefixEnd_1056112 : Nat := 4983230072969 + 3 ^ 40 * 1056112 * 2
def baseEnd_1056112 : Nat := 542293080981277190643035

theorem tailTrace_1056112 : CollatzResearch.WordTrace tailWord_1056112 prefixEnd_1056112 542293080981277190643035 := by
  unfold tailWord_1056112
  simp only [CollatzResearch.WordTrace]
  refine ⟨19259784574947034207377295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25679712766596045609836393 19259784574947034207377295)
  ·
    refine ⟨28889676862420551311065943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19259784574947034207377295 28889676862420551311065943)
    ·
      refine ⟨43334515293630826966598915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28889676862420551311065943 43334515293630826966598915)
      ·
        refine ⟨65001772940446240449898373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43334515293630826966598915 65001772940446240449898373)
        ·
          refine ⟨12187832426333670084355945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65001772940446240449898373 12187832426333670084355945)
          ·
            refine ⟨9140874319750252563266959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12187832426333670084355945 9140874319750252563266959)
            ·
              refine ⟨13711311479625378844900439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9140874319750252563266959 13711311479625378844900439)
              ·
                refine ⟨20566967219438068267350659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13711311479625378844900439 20566967219438068267350659)
                ·
                  refine ⟨30850450829157102401025989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20566967219438068267350659 30850450829157102401025989)
                  ·
                    refine ⟨5784459530466956700192373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30850450829157102401025989 5784459530466956700192373)
                    ·
                      refine ⟨542293080981277190643035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5784459530466956700192373 542293080981277190643035)
                      ·
                        rfl

theorem cell23_1056112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 5].length) (baseStart_1056112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056112 prefixEnd_1056112 := by exact prefixLift 1056112
  have htrace : WordTrace (prefixWord ++ tailWord_1056112) baseStart_1056112 baseEnd_1056112 := by
    simpa [prefixWord, tailWord_1056112, baseEnd_1056112] using wordTrace_append hprefix tailTrace_1056112
  have hstable : (prefixWord ++ tailWord_1056112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056112).length < 2 ^ (prefixWord ++ tailWord_1056112).sum := by decide
  have hdescent : baseEnd_1056112 < baseStart_1056112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056159 : List Nat := [1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 5]
def baseStart_1056159 : Nat := 118140960795 + 1056159 * 2 ^ 59
def prefixEnd_1056159 : Nat := 4983230072969 + 3 ^ 40 * 1056159 * 2
def baseEnd_1056159 : Nat := 542317214572038506755319

theorem tailTrace_1056159 : CollatzResearch.WordTrace tailWord_1056159 prefixEnd_1056159 542317214572038506755319 := by
  unfold tailWord_1056159
  simp only [CollatzResearch.WordTrace]
  refine ⟨38521283380723795441715531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25680855587149196961143687 38521283380723795441715531)
  ·
    refine ⟨57781925071085693162573297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38521283380723795441715531 57781925071085693162573297)
    ·
      refine ⟨43336443803314269871929973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57781925071085693162573297 43336443803314269871929973)
      ·
        refine ⟨4062791606560712800493435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43336443803314269871929973 4062791606560712800493435)
        ·
          refine ⟨6094187409841069200740153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4062791606560712800493435 6094187409841069200740153)
          ·
            refine ⟨4570640557380801900555115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6094187409841069200740153 4570640557380801900555115)
            ·
              refine ⟨6855960836071202850832673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4570640557380801900555115 6855960836071202850832673)
              ·
                refine ⟨5141970627053402138124505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6855960836071202850832673 5141970627053402138124505)
                ·
                  refine ⟨3856477970290051603593379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5141970627053402138124505 3856477970290051603593379)
                  ·
                    refine ⟨5784716955435077405390069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3856477970290051603593379 5784716955435077405390069)
                    ·
                      refine ⟨542317214572038506755319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5784716955435077405390069 542317214572038506755319)
                      ·
                        rfl

theorem cell23_1056159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_1056159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056159 prefixEnd_1056159 := by exact prefixLift 1056159
  have htrace : WordTrace (prefixWord ++ tailWord_1056159) baseStart_1056159 baseEnd_1056159 := by
    simpa [prefixWord, tailWord_1056159, baseEnd_1056159] using wordTrace_append hprefix tailTrace_1056159
  have hstable : (prefixWord ++ tailWord_1056159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056159).length < 2 ^ (prefixWord ++ tailWord_1056159).sum := by decide
  have hdescent : baseEnd_1056159 < baseStart_1056159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056173 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 3, 4, 2]
def baseStart_1056173 : Nat := 118140960795 + 1056173 * 2 ^ 59
def prefixEnd_1056173 : Nat := 4983230072969 + 3 ^ 40 * 1056173 * 2
def baseEnd_1056173 : Nat := 542324403301201451980255

theorem tailTrace_1056173 : CollatzResearch.WordTrace tailWord_1056173 prefixEnd_1056173 542324403301201451980255 := by
  unfold tailWord_1056173
  simp only [CollatzResearch.WordTrace]
  refine ⟨38521794002673075832725173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25681196001782050555150115 38521794002673075832725173)
  ·
    refine ⟨3611418187750600859317985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38521794002673075832725173 3611418187750600859317985)
    ·
      refine ⟨2708563640812950644488489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3611418187750600859317985 2708563640812950644488489)
      ·
        refine ⟨2031422730609712983366367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2708563640812950644488489 2031422730609712983366367)
        ·
          refine ⟨3047134095914569475049551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2031422730609712983366367 3047134095914569475049551)
          ·
            refine ⟨4570701143871854212574327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3047134095914569475049551 4570701143871854212574327)
            ·
              refine ⟨6856051715807781318861491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4570701143871854212574327 6856051715807781318861491)
              ·
                refine ⟨10284077573711671978292237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6856051715807781318861491 10284077573711671978292237)
                ·
                  refine ⟨3856529090141876991859589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10284077573711671978292237 3856529090141876991859589)
                  ·
                    refine ⟨723099204401601935973673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3856529090141876991859589 723099204401601935973673)
                    ·
                      refine ⟨542324403301201451980255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 723099204401601935973673 542324403301201451980255)
                      ·
                        rfl

theorem cell23_1056173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_1056173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056173 prefixEnd_1056173 := by exact prefixLift 1056173
  have htrace : WordTrace (prefixWord ++ tailWord_1056173) baseStart_1056173 baseEnd_1056173 := by
    simpa [prefixWord, tailWord_1056173, baseEnd_1056173] using wordTrace_append hprefix tailTrace_1056173
  have hstable : (prefixWord ++ tailWord_1056173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056173).length < 2 ^ (prefixWord ++ tailWord_1056173).sum := by decide
  have hdescent : baseEnd_1056173 < baseStart_1056173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056263 : List Nat := [1, 1, 4, 3, 2, 1, 2, 1, 2, 4, 2]
def baseStart_1056263 : Nat := 118140960795 + 1056263 * 2 ^ 59
def prefixEnd_1056263 : Nat := 4983230072969 + 3 ^ 40 * 1056263 * 2
def baseEnd_1056263 : Nat := 542370616560106099854841

theorem tailTrace_1056263 : CollatzResearch.WordTrace tailWord_1056263 prefixEnd_1056263 542370616560106099854841 := by
  unfold tailWord_1056263
  simp only [CollatzResearch.WordTrace]
  refine ⟨38525076572347021203501443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25683384381564680802334295 38525076572347021203501443)
  ·
    refine ⟨57787614858520531805252165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38525076572347021203501443 57787614858520531805252165)
    ·
      refine ⟨10835177785972599713484781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57787614858520531805252165 10835177785972599713484781)
      ·
        refine ⟨4063191669739724892556793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10835177785972599713484781 4063191669739724892556793)
        ·
          refine ⟨3047393752304793669417595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4063191669739724892556793 3047393752304793669417595)
          ·
            refine ⟨4571090628457190504126393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3047393752304793669417595 4571090628457190504126393)
            ·
              refine ⟨3428317971342892878094795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4571090628457190504126393 3428317971342892878094795)
              ·
                refine ⟨5142476957014339317142193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3428317971342892878094795 5142476957014339317142193)
                ·
                  refine ⟨3856857717760754487856645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5142476957014339317142193 3856857717760754487856645)
                  ·
                    refine ⟨723160822080141466473121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3856857717760754487856645 723160822080141466473121)
                    ·
                      refine ⟨542370616560106099854841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 723160822080141466473121 542370616560106099854841)
                      ·
                        rfl

theorem cell23_1056263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_1056263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056263 prefixEnd_1056263 := by exact prefixLift 1056263
  have htrace : WordTrace (prefixWord ++ tailWord_1056263) baseStart_1056263 baseEnd_1056263 := by
    simpa [prefixWord, tailWord_1056263, baseEnd_1056263] using wordTrace_append hprefix tailTrace_1056263
  have hstable : (prefixWord ++ tailWord_1056263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056263).length < 2 ^ (prefixWord ++ tailWord_1056263).sum := by decide
  have hdescent : baseEnd_1056263 < baseStart_1056263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056266 : List Nat := [3, 1, 2, 2, 2, 2, 1, 2, 1, 4, 3]
def baseStart_1056266 : Nat := 118140960795 + 1056266 * 2 ^ 59
def prefixEnd_1056266 : Nat := 4983230072969 + 3 ^ 40 * 1056266 * 2
def baseEnd_1056266 : Nat := 542372157002069588117327

theorem tailTrace_1056266 : CollatzResearch.WordTrace tailWord_1056266 prefixEnd_1056266 542372157002069588117327 := by
  unfold tailWord_1056266
  simp only [CollatzResearch.WordTrace]
  refine ⟨9631296497834038178965163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25683457327557435143907101 9631296497834038178965163)
  ·
    refine ⟨14446944746751057268447745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9631296497834038178965163 14446944746751057268447745)
    ·
      refine ⟨10835208560063292951335809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14446944746751057268447745 10835208560063292951335809)
      ·
        refine ⟨8126406420047469713501857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10835208560063292951335809 8126406420047469713501857)
        ·
          refine ⟨6094804815035602285126393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8126406420047469713501857 6094804815035602285126393)
          ·
            refine ⟨4571103611276701713844795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6094804815035602285126393 4571103611276701713844795)
            ·
              refine ⟨6856655416915052570767193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4571103611276701713844795 6856655416915052570767193)
              ·
                refine ⟨5142491562686289428075395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6856655416915052570767193 5142491562686289428075395)
                ·
                  refine ⟨7713737344029434142113093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5142491562686289428075395 7713737344029434142113093)
                  ·
                    refine ⟨1446325752005518901646205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7713737344029434142113093 1446325752005518901646205)
                    ·
                      refine ⟨542372157002069588117327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1446325752005518901646205 542372157002069588117327)
                      ·
                        rfl

theorem cell23_1056266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_1056266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056266 prefixEnd_1056266 := by exact prefixLift 1056266
  have htrace : WordTrace (prefixWord ++ tailWord_1056266) baseStart_1056266 baseEnd_1056266 := by
    simpa [prefixWord, tailWord_1056266, baseEnd_1056266] using wordTrace_append hprefix tailTrace_1056266
  have hstable : (prefixWord ++ tailWord_1056266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056266).length < 2 ^ (prefixWord ++ tailWord_1056266).sum := by decide
  have hdescent : baseEnd_1056266 < baseStart_1056266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056290 : List Nat := [3, 3, 1, 1, 1, 1, 5, 3, 1, 4]
def baseStart_1056290 : Nat := 118140960795 + 1056290 * 2 ^ 59
def prefixEnd_1056290 : Nat := 4983230072969 + 3 ^ 40 * 1056290 * 2
def baseEnd_1056290 : Nat := 180794826845925831405739

theorem tailTrace_1056290 : CollatzResearch.WordTrace tailWord_1056290 prefixEnd_1056290 180794826845925831405739 := by
  unfold tailWord_1056290
  simp only [CollatzResearch.WordTrace]
  refine ⟨9631515335812301203683581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25684040895499469876489549 9631515335812301203683581)
  ·
    refine ⟨3611818250929612951381343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9631515335812301203683581 3611818250929612951381343)
    ·
      refine ⟨5417727376394419427072015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3611818250929612951381343 5417727376394419427072015)
      ·
        refine ⟨8126591064591629140608023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5417727376394419427072015 8126591064591629140608023)
        ·
          refine ⟨12189886596887443710912035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8126591064591629140608023 12189886596887443710912035)
          ·
            refine ⟨18284829895331165566368053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12189886596887443710912035 18284829895331165566368053)
            ·
              refine ⟨1714202802687296771847005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18284829895331165566368053 1714202802687296771847005)
              ·
                refine ⟨642826051007736289442627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1714202802687296771847005 642826051007736289442627)
                ·
                  refine ⟨964239076511604434163941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 642826051007736289442627 964239076511604434163941)
                  ·
                    refine ⟨180794826845925831405739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 964239076511604434163941 180794826845925831405739)
                    ·
                      rfl

theorem cell23_1056290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_1056290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056290 prefixEnd_1056290 := by exact prefixLift 1056290
  have htrace : WordTrace (prefixWord ++ tailWord_1056290) baseStart_1056290 baseEnd_1056290 := by
    simpa [prefixWord, tailWord_1056290, baseEnd_1056290] using wordTrace_append hprefix tailTrace_1056290
  have hstable : (prefixWord ++ tailWord_1056290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056290).length < 2 ^ (prefixWord ++ tailWord_1056290).sum := by decide
  have hdescent : baseEnd_1056290 < baseStart_1056290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056299 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 7, 5]
def baseStart_1056299 : Nat := 118140960795 + 1056299 * 2 ^ 59
def prefixEnd_1056299 : Nat := 4983230072969 + 3 ^ 40 * 1056299 * 2
def baseEnd_1056299 : Nat := 180796367287889319668225

theorem tailTrace_1056299 : CollatzResearch.WordTrace tailWord_1056299 prefixEnd_1056299 180796367287889319668225 := by
  unfold tailWord_1056299
  simp only [CollatzResearch.WordTrace]
  refine ⟨38526389600216599351811951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25684259733477732901207967 38526389600216599351811951)
  ·
    refine ⟨57789584400324899027717927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38526389600216599351811951 57789584400324899027717927)
    ·
      refine ⟨86684376600487348541576891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57789584400324899027717927 86684376600487348541576891)
      ·
        refine ⟨130026564900731022812365337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86684376600487348541576891 130026564900731022812365337)
        ·
          refine ⟨97519923675548267109274003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130026564900731022812365337 97519923675548267109274003)
          ·
            refine ⟨146279885513322400663911005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97519923675548267109274003 146279885513322400663911005)
            ·
              refine ⟨54854957067495900248966627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 146279885513322400663911005 54854957067495900248966627)
              ·
                refine ⟨82282435601243850373449941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54854957067495900248966627 82282435601243850373449941)
                ·
                  refine ⟨1928494584404152743127733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 82282435601243850373449941 1928494584404152743127733)
                  ·
                    refine ⟨180796367287889319668225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1928494584404152743127733 180796367287889319668225)
                    ·
                      rfl

theorem cell23_1056299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 5].length) (baseStart_1056299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056299 prefixEnd_1056299 := by exact prefixLift 1056299
  have htrace : WordTrace (prefixWord ++ tailWord_1056299) baseStart_1056299 baseEnd_1056299 := by
    simpa [prefixWord, tailWord_1056299, baseEnd_1056299] using wordTrace_append hprefix tailTrace_1056299
  have hstable : (prefixWord ++ tailWord_1056299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056299).length < 2 ^ (prefixWord ++ tailWord_1056299).sum := by decide
  have hdescent : baseEnd_1056299 < baseStart_1056299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056329 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 5, 6]
def baseStart_1056329 : Nat := 118140960795 + 1056329 * 2 ^ 59
def prefixEnd_1056329 : Nat := 4983230072969 + 3 ^ 40 * 1056329 * 2
def baseEnd_1056329 : Nat := 180801502094434280543179

theorem tailTrace_1056329 : CollatzResearch.WordTrace tailWord_1056329 prefixEnd_1056329 180801502094434280543179 := by
  unfold tailWord_1056329
  simp only [CollatzResearch.WordTrace]
  refine ⟨38527483790107914475404041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25684989193405276316936027 38527483790107914475404041)
  ·
    refine ⟨28895612842580935856553031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38527483790107914475404041 28895612842580935856553031)
    ·
      refine ⟨43343419263871403784829547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28895612842580935856553031 43343419263871403784829547)
      ·
        refine ⟨65015128895807105677244321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43343419263871403784829547 65015128895807105677244321)
        ·
          refine ⟨48761346671855329257933241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65015128895807105677244321 48761346671855329257933241)
          ·
            refine ⟨36571010003891496943449931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48761346671855329257933241 36571010003891496943449931)
            ·
              refine ⟨54856515005837245415174897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36571010003891496943449931 54856515005837245415174897)
              ·
                refine ⟨41142386254377934061381173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54856515005837245415174897 41142386254377934061381173)
                ·
                  refine ⟨3857098711347931318254485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41142386254377934061381173 3857098711347931318254485)
                  ·
                    refine ⟨180801502094434280543179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3857098711347931318254485 180801502094434280543179)
                    ·
                      rfl

theorem cell23_1056329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 6].length) (baseStart_1056329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056329 prefixEnd_1056329 := by exact prefixLift 1056329
  have htrace : WordTrace (prefixWord ++ tailWord_1056329) baseStart_1056329 baseEnd_1056329 := by
    simpa [prefixWord, tailWord_1056329, baseEnd_1056329] using wordTrace_append hprefix tailTrace_1056329
  have hstable : (prefixWord ++ tailWord_1056329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056329).length < 2 ^ (prefixWord ++ tailWord_1056329).sum := by decide
  have hdescent : baseEnd_1056329 < baseStart_1056329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056336 : List Nat := [2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 4]
def baseStart_1056336 : Nat := 118140960795 + 1056336 * 2 ^ 59
def prefixEnd_1056336 : Nat := 4983230072969 + 3 ^ 40 * 1056336 * 2
def baseEnd_1056336 : Nat := 542408100647884314242005

theorem tailTrace_1056336 : CollatzResearch.WordTrace tailWord_1056336 prefixEnd_1056336 542408100647884314242005 := by
  unfold tailWord_1056336
  simp only [CollatzResearch.WordTrace]
  refine ⟨19263869550541277335454431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25685159400721703113939241 19263869550541277335454431)
  ·
    refine ⟨28895804325811916003181647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19263869550541277335454431 28895804325811916003181647)
    ·
      refine ⟨43343706488717874004772471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28895804325811916003181647 43343706488717874004772471)
      ·
        refine ⟨65015559733076811007158707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43343706488717874004772471 65015559733076811007158707)
        ·
          refine ⟨97523339599615216510738061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65015559733076811007158707 97523339599615216510738061)
          ·
            refine ⟨36571252349855706191526773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97523339599615216510738061 36571252349855706191526773)
            ·
              refine ⟨3428554907798972455455635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36571252349855706191526773 3428554907798972455455635)
              ·
                refine ⟨5142832361698458683183453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3428554907798972455455635 5142832361698458683183453)
                ·
                  refine ⟨1928562135636922006193795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5142832361698458683183453 1928562135636922006193795)
                  ·
                    refine ⟨2892843203455383009290693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1928562135636922006193795 2892843203455383009290693)
                    ·
                      refine ⟨542408100647884314242005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2892843203455383009290693 542408100647884314242005)
                      ·
                        rfl

theorem cell23_1056336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 4].length) (baseStart_1056336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056336 prefixEnd_1056336 := by exact prefixLift 1056336
  have htrace : WordTrace (prefixWord ++ tailWord_1056336) baseStart_1056336 baseEnd_1056336 := by
    simpa [prefixWord, tailWord_1056336, baseEnd_1056336] using wordTrace_append hprefix tailTrace_1056336
  have hstable : (prefixWord ++ tailWord_1056336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056336).length < 2 ^ (prefixWord ++ tailWord_1056336).sum := by decide
  have hdescent : baseEnd_1056336 < baseStart_1056336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056340 : List Nat := [2, 4, 1, 1, 1, 2, 4, 1, 2, 3, 2]
def baseStart_1056340 : Nat := 118140960795 + 1056340 * 2 ^ 59
def prefixEnd_1056340 : Nat := 4983230072969 + 3 ^ 40 * 1056340 * 2
def baseEnd_1056340 : Nat := 542410154570502298591987

theorem tailTrace_1056340 : CollatzResearch.WordTrace tailWord_1056340 prefixEnd_1056340 542410154570502298591987 := by
  unfold tailWord_1056340
  simp only [CollatzResearch.WordTrace]
  refine ⟨19263942496534031677027237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25685256662045375569369649 19263942496534031677027237)
  ·
    refine ⟨3611989218100130939442607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19263942496534031677027237 3611989218100130939442607)
    ·
      refine ⟨5417983827150196409163911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3611989218100130939442607 5417983827150196409163911)
      ·
        refine ⟨8126975740725294613745867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5417983827150196409163911 8126975740725294613745867)
        ·
          refine ⟨12190463611087941920618801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8126975740725294613745867 12190463611087941920618801)
          ·
            refine ⟨9142847708315956440464101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12190463611087941920618801 9142847708315956440464101)
            ·
              refine ⟨1714283945309241832587019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9142847708315956440464101 1714283945309241832587019)
              ·
                refine ⟨2571425917963862748880529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1714283945309241832587019 2571425917963862748880529)
                ·
                  refine ⟨1928569438472897061660397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2571425917963862748880529 1928569438472897061660397)
                  ·
                    refine ⟨723213539427336398122649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1928569438472897061660397 723213539427336398122649)
                    ·
                      refine ⟨542410154570502298591987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 723213539427336398122649 542410154570502298591987)
                      ·
                        rfl

theorem cell23_1056340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_1056340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056340 prefixEnd_1056340 := by exact prefixLift 1056340
  have htrace : WordTrace (prefixWord ++ tailWord_1056340) baseStart_1056340 baseEnd_1056340 := by
    simpa [prefixWord, tailWord_1056340, baseEnd_1056340] using wordTrace_append hprefix tailTrace_1056340
  have hstable : (prefixWord ++ tailWord_1056340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056340).length < 2 ^ (prefixWord ++ tailWord_1056340).sum := by decide
  have hdescent : baseEnd_1056340 < baseStart_1056340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056346 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 6, 4]
def baseStart_1056346 : Nat := 118140960795 + 1056346 * 2 ^ 59
def prefixEnd_1056346 : Nat := 4983230072969 + 3 ^ 40 * 1056346 * 2
def baseEnd_1056346 : Nat := 180804411818143091705653

theorem tailTrace_1056346 : CollatzResearch.WordTrace tailWord_1056346 prefixEnd_1056346 180804411818143091705653 := by
  unfold tailWord_1056346
  simp only [CollatzResearch.WordTrace]
  refine ⟨9632025957761581594693223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25685402554030884252515261 9632025957761581594693223)
  ·
    refine ⟨14448038936642372392039835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9632025957761581594693223 14448038936642372392039835)
    ·
      refine ⟨21672058404963558588059753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14448038936642372392039835 21672058404963558588059753)
      ·
        refine ⟨16254043803722668941044815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21672058404963558588059753 16254043803722668941044815)
        ·
          refine ⟨24381065705584003411567223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16254043803722668941044815 24381065705584003411567223)
          ·
            refine ⟨36571598558376005117350835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24381065705584003411567223 36571598558376005117350835)
            ·
              refine ⟨54857397837564007676026253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36571598558376005117350835 54857397837564007676026253)
              ·
                refine ⟨20571524189086502878509845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54857397837564007676026253 20571524189086502878509845)
                ·
                  refine ⟨964290196363429822430149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20571524189086502878509845 964290196363429822430149)
                  ·
                    refine ⟨180804411818143091705653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 964290196363429822430149 180804411818143091705653)
                    ·
                      rfl

theorem cell23_1056346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 6, 4].length) (baseStart_1056346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056346 prefixEnd_1056346 := by exact prefixLift 1056346
  have htrace : WordTrace (prefixWord ++ tailWord_1056346) baseStart_1056346 baseEnd_1056346 := by
    simpa [prefixWord, tailWord_1056346, baseEnd_1056346] using wordTrace_append hprefix tailTrace_1056346
  have hstable : (prefixWord ++ tailWord_1056346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056346).length < 2 ^ (prefixWord ++ tailWord_1056346).sum := by decide
  have hdescent : baseEnd_1056346 < baseStart_1056346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056404 : List Nat := [2, 4, 2, 2, 2, 2, 2, 1, 1, 1, 4]
def baseStart_1056404 : Nat := 118140960795 + 1056404 * 2 ^ 59
def prefixEnd_1056404 : Nat := 4983230072969 + 3 ^ 40 * 1056404 * 2
def baseEnd_1056404 : Nat := 542443017332390048191693

theorem tailTrace_1056404 : CollatzResearch.WordTrace tailWord_1056404 prefixEnd_1056404 542443017332390048191693 := by
  unfold tailWord_1056404
  simp only [CollatzResearch.WordTrace]
  refine ⟨19265109632418101142192133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25686812843224134856256177 19265109632418101142192133)
  ·
    refine ⟨3612208056078393964161025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19265109632418101142192133 3612208056078393964161025)
    ·
      refine ⟨2709156042058795473120769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3612208056078393964161025 2709156042058795473120769)
      ·
        refine ⟨2031867031544096604840577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2709156042058795473120769 2031867031544096604840577)
        ·
          refine ⟨1523900273658072453630433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2031867031544096604840577 1523900273658072453630433)
          ·
            refine ⟨1142925205243554340222825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1523900273658072453630433 1142925205243554340222825)
            ·
              refine ⟨857193903932665755167119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1142925205243554340222825 857193903932665755167119)
              ·
                refine ⟨1285790855898998632750679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 857193903932665755167119 1285790855898998632750679)
                ·
                  refine ⟨1928686283848497949126019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1285790855898998632750679 1928686283848497949126019)
                  ·
                    refine ⟨2893029425772746923689029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1928686283848497949126019 2893029425772746923689029)
                    ·
                      refine ⟨542443017332390048191693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2893029425772746923689029 542443017332390048191693)
                      ·
                        rfl

theorem cell23_1056404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_1056404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056404 prefixEnd_1056404 := by exact prefixLift 1056404
  have htrace : WordTrace (prefixWord ++ tailWord_1056404) baseStart_1056404 baseEnd_1056404 := by
    simpa [prefixWord, tailWord_1056404, baseEnd_1056404] using wordTrace_append hprefix tailTrace_1056404
  have hstable : (prefixWord ++ tailWord_1056404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056404).length < 2 ^ (prefixWord ++ tailWord_1056404).sum := by decide
  have hdescent : baseEnd_1056404 < baseStart_1056404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056407 : List Nat := [1, 1, 3, 3, 2, 4, 2, 1, 1, 2, 3]
def baseStart_1056407 : Nat := 118140960795 + 1056407 * 2 ^ 59
def prefixEnd_1056407 : Nat := 4983230072969 + 3 ^ 40 * 1056407 * 2
def baseEnd_1056407 : Nat := 542444557774353536454179

theorem tailTrace_1056407 : CollatzResearch.WordTrace tailWord_1056407 prefixEnd_1056407 542444557774353536454179 := by
  unfold tailWord_1056407
  simp only [CollatzResearch.WordTrace]
  refine ⟨38530328683825333796743475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25686885789216889197828983 38530328683825333796743475)
  ·
    refine ⟨57795493025738000695115213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38530328683825333796743475 57795493025738000695115213)
    ·
      refine ⟨21673309884651750260668205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57795493025738000695115213 21673309884651750260668205)
      ·
        refine ⟨8127491206744406347750577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21673309884651750260668205 8127491206744406347750577)
        ·
          refine ⟨6095618405058304760812933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8127491206744406347750577 6095618405058304760812933)
          ·
            refine ⟨1142928450948432142652425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6095618405058304760812933 1142928450948432142652425)
            ·
              refine ⟨857196338211324106989319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1142928450948432142652425 857196338211324106989319)
              ·
                refine ⟨1285794507316986160483979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 857196338211324106989319 1285794507316986160483979)
                ·
                  refine ⟨1928691760975479240725969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1285794507316986160483979 1928691760975479240725969)
                  ·
                    refine ⟨1446518820731609430544477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1928691760975479240725969 1446518820731609430544477)
                    ·
                      refine ⟨542444557774353536454179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1446518820731609430544477 542444557774353536454179)
                      ·
                        rfl

theorem cell23_1056407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_1056407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056407 prefixEnd_1056407 := by exact prefixLift 1056407
  have htrace : WordTrace (prefixWord ++ tailWord_1056407) baseStart_1056407 baseEnd_1056407 := by
    simpa [prefixWord, tailWord_1056407, baseEnd_1056407] using wordTrace_append hprefix tailTrace_1056407
  have hstable : (prefixWord ++ tailWord_1056407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056407).length < 2 ^ (prefixWord ++ tailWord_1056407).sum := by decide
  have hdescent : baseEnd_1056407 < baseStart_1056407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056420 : List Nat := [2, 3, 1, 2, 2, 3, 1, 1, 4, 1, 3]
def baseStart_1056420 : Nat := 118140960795 + 1056420 * 2 ^ 59
def prefixEnd_1056420 : Nat := 4983230072969 + 3 ^ 40 * 1056420 * 2
def baseEnd_1056420 : Nat := 542451233022861985591619

theorem tailTrace_1056420 : CollatzResearch.WordTrace tailWord_1056420 prefixEnd_1056420 542451233022861985591619 := by
  unfold tailWord_1056420
  simp only [CollatzResearch.WordTrace]
  refine ⟨19265401416389118508483357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25687201888518824677977809 19265401416389118508483357)
  ·
    refine ⟨7224525531145919440681259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19265401416389118508483357 7224525531145919440681259)
    ·
      refine ⟨10836788296718879161021889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7224525531145919440681259 10836788296718879161021889)
      ·
        refine ⟨8127591222539159370766417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10836788296718879161021889 8127591222539159370766417)
        ·
          refine ⟨6095693416904369528074813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8127591222539159370766417 6095693416904369528074813)
          ·
            refine ⟨2285885031339138573028055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6095693416904369528074813 2285885031339138573028055)
            ·
              refine ⟨3428827547008707859542083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2285885031339138573028055 3428827547008707859542083)
              ·
                refine ⟨5143241320513061789313125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3428827547008707859542083 5143241320513061789313125)
                ·
                  refine ⟨964357747596199085496211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5143241320513061789313125 964357747596199085496211)
                  ·
                    refine ⟨1446536621394298628244317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 964357747596199085496211 1446536621394298628244317)
                    ·
                      refine ⟨542451233022861985591619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1446536621394298628244317 542451233022861985591619)
                      ·
                        rfl

theorem cell23_1056420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_1056420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056420 prefixEnd_1056420 := by exact prefixLift 1056420
  have htrace : WordTrace (prefixWord ++ tailWord_1056420) baseStart_1056420 baseEnd_1056420 := by
    simpa [prefixWord, tailWord_1056420, baseEnd_1056420] using wordTrace_append hprefix tailTrace_1056420
  have hstable : (prefixWord ++ tailWord_1056420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056420).length < 2 ^ (prefixWord ++ tailWord_1056420).sum := by decide
  have hdescent : baseEnd_1056420 < baseStart_1056420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056437 : List Nat := [1, 3, 3, 3, 2, 2, 1, 1, 1, 3, 3]
def baseStart_1056437 : Nat := 118140960795 + 1056437 * 2 ^ 59
def prefixEnd_1056437 : Nat := 4983230072969 + 3 ^ 40 * 1056437 * 2
def baseEnd_1056437 : Nat := 542459962193988419079041

theorem tailTrace_1056437 : CollatzResearch.WordTrace tailWord_1056437 prefixEnd_1056437 542459962193988419079041 := by
  unfold tailWord_1056437
  simp only [CollatzResearch.WordTrace]
  refine ⟨38531422873716648920335565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25687615249144432613557043 38531422873716648920335565)
  ·
    refine ⟨14449283577643743345125837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38531422873716648920335565 14449283577643743345125837)
    ·
      refine ⟨5418481341616403754422189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14449283577643743345125837 5418481341616403754422189)
      ·
        refine ⟨2031930503106151407908321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5418481341616403754422189 2031930503106151407908321)
        ·
          refine ⟨1523947877329613555931241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2031930503106151407908321 1523947877329613555931241)
          ·
            refine ⟨1142960907997210166948431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1523947877329613555931241 1142960907997210166948431)
            ·
              refine ⟨1714441361995815250422647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1142960907997210166948431 1714441361995815250422647)
              ·
                refine ⟨2571662042993722875633971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1714441361995815250422647 2571662042993722875633971)
                ·
                  refine ⟨3857493064490584313450957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2571662042993722875633971 3857493064490584313450957)
                  ·
                    refine ⟨1446559899183969117544109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3857493064490584313450957 1446559899183969117544109)
                    ·
                      refine ⟨542459962193988419079041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1446559899183969117544109 542459962193988419079041)
                      ·
                        rfl

theorem cell23_1056437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_1056437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056437 prefixEnd_1056437 := by exact prefixLift 1056437
  have htrace : WordTrace (prefixWord ++ tailWord_1056437) baseStart_1056437 baseEnd_1056437 := by
    simpa [prefixWord, tailWord_1056437, baseEnd_1056437] using wordTrace_append hprefix tailTrace_1056437
  have hstable : (prefixWord ++ tailWord_1056437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056437).length < 2 ^ (prefixWord ++ tailWord_1056437).sum := by decide
  have hdescent : baseEnd_1056437 < baseStart_1056437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056454 : List Nat := [6, 1, 2, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_1056454 : Nat := 118140960795 + 1056454 * 2 ^ 59
def prefixEnd_1056454 : Nat := 4983230072969 + 3 ^ 40 * 1056454 * 2
def baseEnd_1056454 : Nat := 542468691365114852566463

theorem tailTrace_1056454 : CollatzResearch.WordTrace tailWord_1056454 prefixEnd_1056454 542468691365114852566463 := by
  unfold tailWord_1056454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1204126341082970650740763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25688028609770040549136277 1204126341082970650740763)
  ·
    refine ⟨1806189511624455976111145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1204126341082970650740763 1806189511624455976111145)
    ·
      refine ⟨1354642133718341982083359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1806189511624455976111145 1354642133718341982083359)
      ·
        refine ⟨2031963200577512973125039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1354642133718341982083359 2031963200577512973125039)
        ·
          refine ⟨3047944800866269459687559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2031963200577512973125039 3047944800866269459687559)
          ·
            refine ⟨4571917201299404189531339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3047944800866269459687559 4571917201299404189531339)
            ·
              refine ⟨6857875801949106284297009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4571917201299404189531339 6857875801949106284297009)
              ·
                refine ⟨5143406851461829713222757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6857875801949106284297009 5143406851461829713222757)
                ·
                  refine ⟨964388784649093071229267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5143406851461829713222757 964388784649093071229267)
                  ·
                    refine ⟨1446583176973639606843901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 964388784649093071229267 1446583176973639606843901)
                    ·
                      refine ⟨542468691365114852566463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1446583176973639606843901 542468691365114852566463)
                      ·
                        rfl

theorem cell23_1056454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_1056454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056454 prefixEnd_1056454 := by exact prefixLift 1056454
  have htrace : WordTrace (prefixWord ++ tailWord_1056454) baseStart_1056454 baseEnd_1056454 := by
    simpa [prefixWord, tailWord_1056454, baseEnd_1056454] using wordTrace_append hprefix tailTrace_1056454
  have hstable : (prefixWord ++ tailWord_1056454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056454).length < 2 ^ (prefixWord ++ tailWord_1056454).sum := by decide
  have hdescent : baseEnd_1056454 < baseStart_1056454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056496 : List Nat := [2, 1, 1, 1, 3, 1, 2, 4, 1, 7]
def baseStart_1056496 : Nat := 118140960795 + 1056496 * 2 ^ 59
def prefixEnd_1056496 : Nat := 4983230072969 + 3 ^ 40 * 1056496 * 2
def baseEnd_1056496 : Nat := 180830085850867896080423

theorem tailTrace_1056496 : CollatzResearch.WordTrace tailWord_1056496 prefixEnd_1056496 180830085850867896080423 := by
  unfold tailWord_1056496
  simp only [CollatzResearch.WordTrace]
  refine ⟨19266787390251450998366671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25689049853668601331155561 19266787390251450998366671)
  ·
    refine ⟨28900181085377176497550007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19266787390251450998366671 28900181085377176497550007)
    ·
      refine ⟨43350271628065764746325011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28900181085377176497550007 43350271628065764746325011)
      ·
        refine ⟨65025407442098647119487517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43350271628065764746325011 65025407442098647119487517)
        ·
          refine ⟨24384527790786992669807819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65025407442098647119487517 24384527790786992669807819)
          ·
            refine ⟨36576791686180489004711729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24384527790786992669807819 36576791686180489004711729)
            ·
              refine ⟨27432593764635366753533797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36576791686180489004711729 27432593764635366753533797)
              ·
                refine ⟨5143611330869131266287587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27432593764635366753533797 5143611330869131266287587)
                ·
                  refine ⟨7715416996303696899431381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5143611330869131266287587 7715416996303696899431381)
                  ·
                    refine ⟨180830085850867896080423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7715416996303696899431381 180830085850867896080423)
                    ·
                      rfl

theorem cell23_1056496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 1, 7].length) (baseStart_1056496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056496 prefixEnd_1056496 := by exact prefixLift 1056496
  have htrace : WordTrace (prefixWord ++ tailWord_1056496) baseStart_1056496 baseEnd_1056496 := by
    simpa [prefixWord, tailWord_1056496, baseEnd_1056496] using wordTrace_append hprefix tailTrace_1056496
  have hstable : (prefixWord ++ tailWord_1056496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056496).length < 2 ^ (prefixWord ++ tailWord_1056496).sum := by decide
  have hdescent : baseEnd_1056496 < baseStart_1056496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056506 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 3, 1, 7]
def baseStart_1056506 : Nat := 118140960795 + 1056506 * 2 ^ 59
def prefixEnd_1056506 : Nat := 4983230072969 + 3 ^ 40 * 1056506 * 2
def baseEnd_1056506 : Nat := 542495392359148649116223

theorem tailTrace_1056506 : CollatzResearch.WordTrace tailWord_1056506 prefixEnd_1056506 542495392359148649116223 := by
  unfold tailWord_1056506
  simp only [CollatzResearch.WordTrace]
  refine ⟨9633484877616668426149343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25689293006977782469731581 9633484877616668426149343)
  ·
    refine ⟨14450227316425002639224015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9633484877616668426149343 14450227316425002639224015)
    ·
      refine ⟨21675340974637503958836023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14450227316425002639224015 21675340974637503958836023)
      ·
        refine ⟨32513011461956255938254035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21675340974637503958836023 32513011461956255938254035)
        ·
          refine ⟨48769517192934383907381053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32513011461956255938254035 48769517192934383907381053)
          ·
            refine ⟨18288568947350393965267895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48769517192934383907381053 18288568947350393965267895)
            ·
              refine ⟨27432853421025590947901843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18288568947350393965267895 27432853421025590947901843)
              ·
                refine ⟨41149280131538386421852765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27432853421025590947901843 41149280131538386421852765)
                ·
                  refine ⟨15430980049326894908194787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41149280131538386421852765 15430980049326894908194787)
                  ·
                    refine ⟨23146470073990342362292181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15430980049326894908194787 23146470073990342362292181)
                    ·
                      refine ⟨542495392359148649116223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 23146470073990342362292181 542495392359148649116223)
                      ·
                        rfl

theorem cell23_1056506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_1056506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056506 prefixEnd_1056506 := by exact prefixLift 1056506
  have htrace : WordTrace (prefixWord ++ tailWord_1056506) baseStart_1056506 baseEnd_1056506 := by
    simpa [prefixWord, tailWord_1056506, baseEnd_1056506] using wordTrace_append hprefix tailTrace_1056506
  have hstable : (prefixWord ++ tailWord_1056506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056506).length < 2 ^ (prefixWord ++ tailWord_1056506).sum := by decide
  have hdescent : baseEnd_1056506 < baseStart_1056506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056513 : List Nat := [1, 2, 4, 1, 1, 1, 3, 3, 2, 5]
def baseStart_1056513 : Nat := 118140960795 + 1056513 * 2 ^ 59
def prefixEnd_1056513 : Nat := 4983230072969 + 3 ^ 40 * 1056513 * 2
def baseEnd_1056513 : Nat := 180832995574576707242897

theorem tailTrace_1056513 : CollatzResearch.WordTrace tailWord_1056513 prefixEnd_1056513 180832995574576707242897 := by
  unfold tailWord_1056513
  simp only [CollatzResearch.WordTrace]
  refine ⟨38534194821441313900102193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25689463214294209266734795 38534194821441313900102193)
  ·
    refine ⟨28900646116080985425076645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38534194821441313900102193 28900646116080985425076645)
    ·
      refine ⟨5418871146765184767201871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28900646116080985425076645 5418871146765184767201871)
      ·
        refine ⟨8128306720147777150802807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5418871146765184767201871 8128306720147777150802807)
        ·
          refine ⟨12192460080221665726204211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8128306720147777150802807 12192460080221665726204211)
          ·
            refine ⟨18288690120332498589306317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12192460080221665726204211 18288690120332498589306317)
            ·
              refine ⟨6858258795124686970989869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18288690120332498589306317 6858258795124686970989869)
              ·
                refine ⟨2571847048171757614121201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6858258795124686970989869 2571847048171757614121201)
                ·
                  refine ⟨1928885286128818210590901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2571847048171757614121201 1928885286128818210590901)
                  ·
                    refine ⟨180832995574576707242897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1928885286128818210590901 180832995574576707242897)
                    ·
                      rfl

theorem cell23_1056513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_1056513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056513 prefixEnd_1056513 := by exact prefixLift 1056513
  have htrace : WordTrace (prefixWord ++ tailWord_1056513) baseStart_1056513 baseEnd_1056513 := by
    simpa [prefixWord, tailWord_1056513, baseEnd_1056513] using wordTrace_append hprefix tailTrace_1056513
  have hstable : (prefixWord ++ tailWord_1056513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056513).length < 2 ^ (prefixWord ++ tailWord_1056513).sum := by decide
  have hdescent : baseEnd_1056513 < baseStart_1056513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056570 : List Nat := [3, 1, 1, 1, 5, 2, 1, 1, 1, 4, 3]
def baseStart_1056570 : Nat := 118140960795 + 1056570 * 2 ^ 59
def prefixEnd_1056570 : Nat := 4983230072969 + 3 ^ 40 * 1056570 * 2
def baseEnd_1056570 : Nat := 542528255121036398715929

theorem tailTrace_1056570 : CollatzResearch.WordTrace tailWord_1056570 prefixEnd_1056570 542528255121036398715929 := by
  unfold tailWord_1056570
  simp only [CollatzResearch.WordTrace]
  refine ⟨9634068445558703158731791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25690849188156541756618109 9634068445558703158731791)
  ·
    refine ⟨14451102668338054738097687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9634068445558703158731791 14451102668338054738097687)
    ·
      refine ⟨21676654002507082107146531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14451102668338054738097687 21676654002507082107146531)
      ·
        refine ⟨32514981003760623160719797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21676654002507082107146531 32514981003760623160719797)
        ·
          refine ⟨3048279469102558421317481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32514981003760623160719797 3048279469102558421317481)
          ·
            refine ⟨2286209601826918815988111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3048279469102558421317481 2286209601826918815988111)
            ·
              refine ⟨3429314402740378223982167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2286209601826918815988111 3429314402740378223982167)
              ·
                refine ⟨5143971604110567335973251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3429314402740378223982167 5143971604110567335973251)
                ·
                  refine ⟨7715957406165851003959877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5143971604110567335973251 7715957406165851003959877)
                  ·
                    refine ⟨1446742013656097063242477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7715957406165851003959877 1446742013656097063242477)
                    ·
                      refine ⟨542528255121036398715929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1446742013656097063242477 542528255121036398715929)
                      ·
                        rfl

theorem cell23_1056570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 1, 4, 3].length) (baseStart_1056570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056570 prefixEnd_1056570 := by exact prefixLift 1056570
  have htrace : WordTrace (prefixWord ++ tailWord_1056570) baseStart_1056570 baseEnd_1056570 := by
    simpa [prefixWord, tailWord_1056570, baseEnd_1056570] using wordTrace_append hprefix tailTrace_1056570
  have hstable : (prefixWord ++ tailWord_1056570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056570).length < 2 ^ (prefixWord ++ tailWord_1056570).sum := by decide
  have hdescent : baseEnd_1056570 < baseStart_1056570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056593 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 1, 2, 6]
def baseStart_1056593 : Nat := 118140960795 + 1056593 * 2 ^ 59
def prefixEnd_1056593 : Nat := 4983230072969 + 3 ^ 40 * 1056593 * 2
def baseEnd_1056593 : Nat := 542540065176089808728323

theorem tailTrace_1056593 : CollatzResearch.WordTrace tailWord_1056593 prefixEnd_1056593 542540065176089808728323 := by
  unfold tailWord_1056593
  simp only [CollatzResearch.WordTrace]
  refine ⟨38537112661151487563014433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25691408440767658375342955 38537112661151487563014433)
  ·
    refine ⟨28902834495863615672260825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38537112661151487563014433 28902834495863615672260825)
    ·
      refine ⟨21677125871897711754195619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28902834495863615672260825 21677125871897711754195619)
      ·
        refine ⟨32515688807846567631293429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21677125871897711754195619 32515688807846567631293429)
        ·
          refine ⟨3048345825735615715433759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32515688807846567631293429 3048345825735615715433759)
          ·
            refine ⟨4572518738603423573150639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3048345825735615715433759 4572518738603423573150639)
            ·
              refine ⟨6858778107905135359725959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4572518738603423573150639 6858778107905135359725959)
              ·
                refine ⟨10288167161857703039588939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6858778107905135359725959 10288167161857703039588939)
                ·
                  refine ⟨15432250742786554559383409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10288167161857703039588939 15432250742786554559383409)
                  ·
                    refine ⟨11574188057089915919537557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15432250742786554559383409 11574188057089915919537557)
                    ·
                      refine ⟨542540065176089808728323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11574188057089915919537557 542540065176089808728323)
                      ·
                        rfl

theorem cell23_1056593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_1056593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056593 prefixEnd_1056593 := by exact prefixLift 1056593
  have htrace : WordTrace (prefixWord ++ tailWord_1056593) baseStart_1056593 baseEnd_1056593 := by
    simpa [prefixWord, tailWord_1056593, baseEnd_1056593] using wordTrace_append hprefix tailTrace_1056593
  have hstable : (prefixWord ++ tailWord_1056593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056593).length < 2 ^ (prefixWord ++ tailWord_1056593).sum := by decide
  have hdescent : baseEnd_1056593 < baseStart_1056593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056620 : List Nat := [2, 2, 1, 1, 4, 2, 1, 4, 1, 5]
def baseStart_1056620 : Nat := 118140960795 + 1056620 * 2 ^ 59
def prefixEnd_1056620 : Nat := 4983230072969 + 3 ^ 40 * 1056620 * 2
def baseEnd_1056620 : Nat := 180851309717920401030233

theorem tailTrace_1056620 : CollatzResearch.WordTrace tailWord_1056620 prefixEnd_1056620 180851309717920401030233 := by
  unfold tailWord_1056620
  simp only [CollatzResearch.WordTrace]
  refine ⟨19269048716026835587123657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25692064954702447449498209 19269048716026835587123657)
  ·
    refine ⟨14451786537020126690342743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19269048716026835587123657 14451786537020126690342743)
    ·
      refine ⟨21677679805530190035514115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14451786537020126690342743 21677679805530190035514115)
      ·
        refine ⟨32516519708295285053271173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21677679805530190035514115 32516519708295285053271173)
        ·
          refine ⟨6096847445305365947488345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32516519708295285053271173 6096847445305365947488345)
          ·
            refine ⟨4572635583979024460616259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6096847445305365947488345 4572635583979024460616259)
            ·
              refine ⟨6858953375968536690924389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4572635583979024460616259 6858953375968536690924389)
              ·
                refine ⟨1286053757994100629548323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6858953375968536690924389 1286053757994100629548323)
                ·
                  refine ⟨1929080636991150944322485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1286053757994100629548323 1929080636991150944322485)
                  ·
                    refine ⟨180851309717920401030233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1929080636991150944322485 180851309717920401030233)
                    ·
                      rfl

theorem cell23_1056620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 5].length) (baseStart_1056620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056620 prefixEnd_1056620 := by exact prefixLift 1056620
  have htrace : WordTrace (prefixWord ++ tailWord_1056620) baseStart_1056620 baseEnd_1056620 := by
    simpa [prefixWord, tailWord_1056620, baseEnd_1056620] using wordTrace_append hprefix tailTrace_1056620
  have hstable : (prefixWord ++ tailWord_1056620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056620).length < 2 ^ (prefixWord ++ tailWord_1056620).sum := by decide
  have hdescent : baseEnd_1056620 < baseStart_1056620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056633 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 3, 6]
def baseStart_1056633 : Nat := 118140960795 + 1056633 * 2 ^ 59
def prefixEnd_1056633 : Nat := 4983230072969 + 3 ^ 40 * 1056633 * 2
def baseEnd_1056633 : Nat := 180853534800756550742713

theorem tailTrace_1056633 : CollatzResearch.WordTrace tailWord_1056633 prefixEnd_1056633 180853534800756550742713 := by
  unfold tailWord_1056633
  simp only [CollatzResearch.WordTrace]
  refine ⟨38538571581006574394470553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25692381054004382929647035 38538571581006574394470553)
  ·
    refine ⟨28903928685754930795852915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38538571581006574394470553 28903928685754930795852915)
    ·
      refine ⟨43355893028632396193779373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28903928685754930795852915 43355893028632396193779373)
      ·
        refine ⟨16258459885737148572667265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43355893028632396193779373 16258459885737148572667265)
        ·
          refine ⟨12193844914302861429500449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16258459885737148572667265 12193844914302861429500449)
          ·
            refine ⟨9145383685727146072125337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12193844914302861429500449 9145383685727146072125337)
            ·
              refine ⟨6859037764295359554094003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9145383685727146072125337 6859037764295359554094003)
              ·
                refine ⟨10288556646443039331141005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6859037764295359554094003 10288556646443039331141005)
                ·
                  refine ⟨3858208742416139749177877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10288556646443039331141005 3858208742416139749177877)
                  ·
                    refine ⟨180853534800756550742713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3858208742416139749177877 180853534800756550742713)
                    ·
                      rfl

theorem cell23_1056633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 6].length) (baseStart_1056633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056633 prefixEnd_1056633 := by exact prefixLift 1056633
  have htrace : WordTrace (prefixWord ++ tailWord_1056633) baseStart_1056633 baseEnd_1056633 := by
    simpa [prefixWord, tailWord_1056633, baseEnd_1056633] using wordTrace_append hprefix tailTrace_1056633
  have hstable : (prefixWord ++ tailWord_1056633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056633).length < 2 ^ (prefixWord ++ tailWord_1056633).sum := by decide
  have hdescent : baseEnd_1056633 < baseStart_1056633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056634 : List Nat := [3, 1, 1, 1, 1, 1, 7, 3, 1, 1, 3]
def baseStart_1056634 : Nat := 118140960795 + 1056634 * 2 ^ 59
def prefixEnd_1056634 : Nat := 4983230072969 + 3 ^ 40 * 1056634 * 2
def baseEnd_1056634 : Nat := 542561117882924148315635

theorem tailTrace_1056634 : CollatzResearch.WordTrace tailWord_1056634 prefixEnd_1056634 542561117882924148315635 := by
  unfold tailWord_1056634
  simp only [CollatzResearch.WordTrace]
  refine ⟨9634652013500737891314239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25692405369335301043504637 9634652013500737891314239)
  ·
    refine ⟨14451978020251106836971359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9634652013500737891314239 14451978020251106836971359)
    ·
      refine ⟨21677967030376660255457039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14451978020251106836971359 21677967030376660255457039)
      ·
        refine ⟨32516950545564990383185559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21677967030376660255457039 32516950545564990383185559)
        ·
          refine ⟨48775425818347485574778339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32516950545564990383185559 48775425818347485574778339)
          ·
            refine ⟨73163138727521228362167509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48775425818347485574778339 73163138727521228362167509)
            ·
              refine ⟨1714761063926278789738301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 73163138727521228362167509 1714761063926278789738301)
              ·
                refine ⟨643035398972354546151863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1714761063926278789738301 643035398972354546151863)
                ·
                  refine ⟨964553098458531819227795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 643035398972354546151863 964553098458531819227795)
                  ·
                    refine ⟨1446829647687797728841693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 964553098458531819227795 1446829647687797728841693)
                    ·
                      refine ⟨542561117882924148315635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1446829647687797728841693 542561117882924148315635)
                      ·
                        rfl

theorem cell23_1056634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 3, 1, 1, 3].length) (baseStart_1056634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056634 prefixEnd_1056634 := by exact prefixLift 1056634
  have htrace : WordTrace (prefixWord ++ tailWord_1056634) baseStart_1056634 baseEnd_1056634 := by
    simpa [prefixWord, tailWord_1056634, baseEnd_1056634] using wordTrace_append hprefix tailTrace_1056634
  have hstable : (prefixWord ++ tailWord_1056634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056634).length < 2 ^ (prefixWord ++ tailWord_1056634).sum := by decide
  have hdescent : baseEnd_1056634 < baseStart_1056634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056640 : List Nat := [2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 4]
def baseStart_1056640 : Nat := 118140960795 + 1056640 * 2 ^ 59
def prefixEnd_1056640 : Nat := 4983230072969 + 3 ^ 40 * 1056640 * 2
def baseEnd_1056640 : Nat := 542564198766851124840607

theorem tailTrace_1056640 : CollatzResearch.WordTrace tailWord_1056640 prefixEnd_1056640 542564198766851124840607 := by
  unfold tailWord_1056640
  simp only [CollatzResearch.WordTrace]
  refine ⟨19269413445990607294987687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25692551261320809726650249 19269413445990607294987687)
  ·
    refine ⟨28904120168985910942481531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19269413445990607294987687 28904120168985910942481531)
    ·
      refine ⟨43356180253478866413722297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28904120168985910942481531 43356180253478866413722297)
      ·
        refine ⟨32517135190109149810291723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43356180253478866413722297 32517135190109149810291723)
        ·
          refine ⟨48775702785163724715437585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32517135190109149810291723 48775702785163724715437585)
          ·
            refine ⟨36581777088872793536578189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48775702785163724715437585 36581777088872793536578189)
            ·
              refine ⟨13718166408327297576216821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36581777088872793536578189 13718166408327297576216821)
              ·
                refine ⟨1286078100780684147770327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13718166408327297576216821 1286078100780684147770327)
                ·
                  refine ⟨1929117151171026221655491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1286078100780684147770327 1929117151171026221655491)
                  ·
                    refine ⟨2893675726756539332483237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1929117151171026221655491 2893675726756539332483237)
                    ·
                      refine ⟨542564198766851124840607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2893675726756539332483237 542564198766851124840607)
                      ·
                        rfl

theorem cell23_1056640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 4].length) (baseStart_1056640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056640 prefixEnd_1056640 := by exact prefixLift 1056640
  have htrace : WordTrace (prefixWord ++ tailWord_1056640) baseStart_1056640 baseEnd_1056640 := by
    simpa [prefixWord, tailWord_1056640, baseEnd_1056640] using wordTrace_append hprefix tailTrace_1056640
  have hstable : (prefixWord ++ tailWord_1056640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056640).length < 2 ^ (prefixWord ++ tailWord_1056640).sum := by decide
  have hdescent : baseEnd_1056640 < baseStart_1056640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056663 : List Nat := [1, 1, 3, 3, 1, 3, 1, 10]
def baseStart_1056663 : Nat := 118140960795 + 1056663 * 2 ^ 59
def prefixEnd_1056663 : Nat := 4983230072969 + 3 ^ 40 * 1056663 * 2
def baseEnd_1056663 : Nat := 20095407734144612401963

theorem tailTrace_1056663 : CollatzResearch.WordTrace tailWord_1056663 prefixEnd_1056663 20095407734144612401963 := by
  unfold tailWord_1056663
  simp only [CollatzResearch.WordTrace]
  refine ⟨38539665770897889518062643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25693110513931926345375095 38539665770897889518062643)
  ·
    refine ⟨57809498656346834277093965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38539665770897889518062643 57809498656346834277093965)
    ·
      refine ⟨21678561996130062853910237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57809498656346834277093965 21678561996130062853910237)
      ·
        refine ⟨8129460748548773570216339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21678561996130062853910237 8129460748548773570216339)
        ·
          refine ⟨12194191122823160355324509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8129460748548773570216339 12194191122823160355324509)
          ·
            refine ⟨4572821671058685133246691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12194191122823160355324509 4572821671058685133246691)
            ·
              refine ⟨6859232506588027699870037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4572821671058685133246691 6859232506588027699870037)
              ·
                refine ⟨20095407734144612401963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 6859232506588027699870037 20095407734144612401963)
                ·
                  rfl

theorem cell23_1056663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 10].length) (baseStart_1056663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056663 prefixEnd_1056663 := by exact prefixLift 1056663
  have htrace : WordTrace (prefixWord ++ tailWord_1056663) baseStart_1056663 baseEnd_1056663 := by
    simpa [prefixWord, tailWord_1056663, baseEnd_1056663] using wordTrace_append hprefix tailTrace_1056663
  have hstable : (prefixWord ++ tailWord_1056663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056663).length < 2 ^ (prefixWord ++ tailWord_1056663).sum := by decide
  have hdescent : baseEnd_1056663 < baseStart_1056663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056724 : List Nat := [2, 4, 1, 2, 1, 1, 1, 5, 2, 1, 3]
def baseStart_1056724 : Nat := 118140960795 + 1056724 * 2 ^ 59
def prefixEnd_1056724 : Nat := 4983230072969 + 3 ^ 40 * 1056724 * 2
def baseEnd_1056724 : Nat := 542607331141828796190221

theorem tailTrace_1056724 : CollatzResearch.WordTrace tailWord_1056724 prefixEnd_1056724 542607331141828796190221 := by
  unfold tailWord_1056724
  simp only [CollatzResearch.WordTrace]
  refine ⟨19270945311838448468016613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25694593749117931290688817 19270945311838448468016613)
  ·
    refine ⟨3613302245969709087753115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19270945311838448468016613 3613302245969709087753115)
    ·
      refine ⟨5419953368954563631629673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3613302245969709087753115 5419953368954563631629673)
      ·
        refine ⟨4064965026715922723722255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5419953368954563631629673 4064965026715922723722255)
        ·
          refine ⟨6097447540073884085583383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4064965026715922723722255 6097447540073884085583383)
          ·
            refine ⟨9146171310110826128375075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6097447540073884085583383 9146171310110826128375075)
            ·
              refine ⟨13719256965166239192562613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9146171310110826128375075 13719256965166239192562613)
              ·
                refine ⟨1286180340484334924302745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13719256965166239192562613 1286180340484334924302745)
                ·
                  refine ⟨964635255363251193227059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1286180340484334924302745 964635255363251193227059)
                  ·
                    refine ⟨1446952883044876789840589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 964635255363251193227059 1446952883044876789840589)
                    ·
                      refine ⟨542607331141828796190221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1446952883044876789840589 542607331141828796190221)
                      ·
                        rfl

theorem cell23_1056724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_1056724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056724 prefixEnd_1056724 := by exact prefixLift 1056724
  have htrace : WordTrace (prefixWord ++ tailWord_1056724) baseStart_1056724 baseEnd_1056724 := by
    simpa [prefixWord, tailWord_1056724, baseEnd_1056724] using wordTrace_append hprefix tailTrace_1056724
  have hstable : (prefixWord ++ tailWord_1056724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056724).length < 2 ^ (prefixWord ++ tailWord_1056724).sum := by decide
  have hdescent : baseEnd_1056724 < baseStart_1056724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056758 : List Nat := [5, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3]
def baseStart_1056758 : Nat := 118140960795 + 1056758 * 2 ^ 59
def prefixEnd_1056758 : Nat := 4983230072969 + 3 ^ 40 * 1056758 * 2
def baseEnd_1056758 : Nat := 542624789484081663165065

theorem tailTrace_1056758 : CollatzResearch.WordTrace tailWord_1056758 prefixEnd_1056758 542624789484081663165065 := by
  unfold tailWord_1056758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2408945669097107546423183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25695420470369147161847285 2408945669097107546423183)
  ·
    refine ⟨3613418503645661319634775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2408945669097107546423183 3613418503645661319634775)
    ·
      refine ⟨5420127755468491979452163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3613418503645661319634775 5420127755468491979452163)
      ·
        refine ⟨8130191633202737969178245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5420127755468491979452163 8130191633202737969178245)
        ·
          refine ⟨1524410931225513369220921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8130191633202737969178245 1524410931225513369220921)
          ·
            refine ⟨1143308198419135026915691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1524410931225513369220921 1143308198419135026915691)
            ·
              refine ⟨1714962297628702540373537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1143308198419135026915691 1714962297628702540373537)
              ·
                refine ⟨1286221723221526905280153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1714962297628702540373537 1286221723221526905280153)
                ·
                  refine ⟨964666292416145178960115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1286221723221526905280153 964666292416145178960115)
                  ·
                    refine ⟨1446999438624217768440173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 964666292416145178960115 1446999438624217768440173)
                    ·
                      refine ⟨542624789484081663165065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1446999438624217768440173 542624789484081663165065)
                      ·
                        rfl

theorem cell23_1056758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_1056758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056758 prefixEnd_1056758 := by exact prefixLift 1056758
  have htrace : WordTrace (prefixWord ++ tailWord_1056758) baseStart_1056758 baseEnd_1056758 := by
    simpa [prefixWord, tailWord_1056758, baseEnd_1056758] using wordTrace_append hprefix tailTrace_1056758
  have hstable : (prefixWord ++ tailWord_1056758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056758).length < 2 ^ (prefixWord ++ tailWord_1056758).sum := by decide
  have hdescent : baseEnd_1056758 < baseStart_1056758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056760 : List Nat := [2, 1, 2, 1, 1, 3, 3, 2, 2, 2, 4]
def baseStart_1056760 : Nat := 118140960795 + 1056760 * 2 ^ 59
def prefixEnd_1056760 : Nat := 4983230072969 + 3 ^ 40 * 1056760 * 2
def baseEnd_1056760 : Nat := 542625816445390655340055

theorem tailTrace_1056760 : CollatzResearch.WordTrace tailWord_1056760 prefixEnd_1056760 542625816445390655340055 := by
  unfold tailWord_1056760
  simp only [CollatzResearch.WordTrace]
  refine ⟨19271601825773237542171867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25695469101030983389562489 19271601825773237542171867)
  ·
    refine ⟨28907402738659856313257801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19271601825773237542171867 28907402738659856313257801)
    ·
      refine ⟨21680552053994892234943351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28907402738659856313257801 21680552053994892234943351)
      ·
        refine ⟨32520828080992338352415027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21680552053994892234943351 32520828080992338352415027)
        ·
          refine ⟨48781242121488507528622541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32520828080992338352415027 48781242121488507528622541)
          ·
            refine ⟨18292965795558190323233453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48781242121488507528622541 18292965795558190323233453)
            ·
              refine ⟨6859862173334321371212545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18292965795558190323233453 6859862173334321371212545)
              ·
                refine ⟨5144896630000741028409409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6859862173334321371212545 5144896630000741028409409)
                ·
                  refine ⟨3858672472500555771307057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5144896630000741028409409 3858672472500555771307057)
                  ·
                    refine ⟨2894004354375416828480293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3858672472500555771307057 2894004354375416828480293)
                    ·
                      refine ⟨542625816445390655340055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2894004354375416828480293 542625816445390655340055)
                      ·
                        rfl

theorem cell23_1056760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_1056760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056760 prefixEnd_1056760 := by exact prefixLift 1056760
  have htrace : WordTrace (prefixWord ++ tailWord_1056760) baseStart_1056760 baseEnd_1056760 := by
    simpa [prefixWord, tailWord_1056760, baseEnd_1056760] using wordTrace_append hprefix tailTrace_1056760
  have hstable : (prefixWord ++ tailWord_1056760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056760).length < 2 ^ (prefixWord ++ tailWord_1056760).sum := by decide
  have hdescent : baseEnd_1056760 < baseStart_1056760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056764 : List Nat := [2, 2, 2, 1, 2, 2, 3, 1, 4, 2, 2]
def baseStart_1056764 : Nat := 118140960795 + 1056764 * 2 ^ 59
def prefixEnd_1056764 : Nat := 4983230072969 + 3 ^ 40 * 1056764 * 2
def baseEnd_1056764 : Nat := 542627870368008639690037

theorem tailTrace_1056764 : CollatzResearch.WordTrace tailWord_1056764 prefixEnd_1056764 542627870368008639690037 := by
  unfold tailWord_1056764
  simp only [CollatzResearch.WordTrace]
  refine ⟨19271674771765991883744673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25695566362354655844992897 19271674771765991883744673)
  ·
    refine ⟨14453756078824493912808505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19271674771765991883744673 14453756078824493912808505)
    ·
      refine ⟨10840317059118370434606379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14453756078824493912808505 10840317059118370434606379)
      ·
        refine ⟨16260475588677555651909569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10840317059118370434606379 16260475588677555651909569)
        ·
          refine ⟨12195356691508166738932177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16260475588677555651909569 12195356691508166738932177)
          ·
            refine ⟨9146517518631125054199133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12195356691508166738932177 9146517518631125054199133)
            ·
              refine ⟨3429944069486671895324675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9146517518631125054199133 3429944069486671895324675)
              ·
                refine ⟨5144916104230007842987013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3429944069486671895324675 5144916104230007842987013)
                ·
                  refine ⟨964671769543126470560065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5144916104230007842987013 964671769543126470560065)
                  ·
                    refine ⟨723503827157344852920049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 964671769543126470560065 723503827157344852920049)
                    ·
                      refine ⟨542627870368008639690037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 723503827157344852920049 542627870368008639690037)
                      ·
                        rfl

theorem cell23_1056764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 4, 2, 2].length) (baseStart_1056764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056764 prefixEnd_1056764 := by exact prefixLift 1056764
  have htrace : WordTrace (prefixWord ++ tailWord_1056764) baseStart_1056764 baseEnd_1056764 := by
    simpa [prefixWord, tailWord_1056764, baseEnd_1056764] using wordTrace_append hprefix tailTrace_1056764
  have hstable : (prefixWord ++ tailWord_1056764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056764).length < 2 ^ (prefixWord ++ tailWord_1056764).sum := by decide
  have hdescent : baseEnd_1056764 < baseStart_1056764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056817 : List Nat := [1, 2, 2, 3, 1, 4, 1, 2, 2, 5]
def baseStart_1056817 : Nat := 118140960795 + 1056817 * 2 ^ 59
def prefixEnd_1056817 : Nat := 4983230072969 + 3 ^ 40 * 1056817 * 2
def baseEnd_1056817 : Nat := 180885028280898977442431

theorem tailTrace_1056817 : CollatzResearch.WordTrace tailWord_1056817 prefixEnd_1056817 180885028280898977442431 := by
  unfold tailWord_1056817
  simp only [CollatzResearch.WordTrace]
  refine ⟨38545282612339973819168705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25696855074893315879445803 38545282612339973819168705)
  ·
    refine ⟨28908961959254980364376529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38545282612339973819168705 28908961959254980364376529)
    ·
      refine ⟨21681721469441235273282397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28908961959254980364376529 21681721469441235273282397)
      ·
        refine ⟨8130645551040463227480899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21681721469441235273282397 8130645551040463227480899)
        ·
          refine ⟨12195968326560694841221349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8130645551040463227480899 12195968326560694841221349)
          ·
            refine ⟨2286744061230130282729003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12195968326560694841221349 2286744061230130282729003)
            ·
              refine ⟨3430116091845195424093505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2286744061230130282729003 3430116091845195424093505)
              ·
                refine ⟨2572587068883896568070129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3430116091845195424093505 2572587068883896568070129)
                ·
                  refine ⟨1929440301662922426052597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2572587068883896568070129 1929440301662922426052597)
                  ·
                    refine ⟨180885028280898977442431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1929440301662922426052597 180885028280898977442431)
                    ·
                      rfl

theorem cell23_1056817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 5].length) (baseStart_1056817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056817 prefixEnd_1056817 := by exact prefixLift 1056817
  have htrace : WordTrace (prefixWord ++ tailWord_1056817) baseStart_1056817 baseEnd_1056817 := by
    simpa [prefixWord, tailWord_1056817, baseEnd_1056817] using wordTrace_append hprefix tailTrace_1056817
  have hstable : (prefixWord ++ tailWord_1056817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056817).length < 2 ^ (prefixWord ++ tailWord_1056817).sum := by decide
  have hdescent : baseEnd_1056817 < baseStart_1056817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056837 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 1, 6, 2]
def baseStart_1056837 : Nat := 118140960795 + 1056837 * 2 ^ 59
def prefixEnd_1056837 : Nat := 4983230072969 + 3 ^ 40 * 1056837 * 2
def baseEnd_1056837 : Nat := 542665354455786854077201

theorem tailTrace_1056837 : CollatzResearch.WordTrace tailWord_1056837 prefixEnd_1056837 542665354455786854077201 := by
  unfold tailWord_1056837
  simp only [CollatzResearch.WordTrace]
  refine ⟨38546012072267517234896765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25697341381511678156597843 38546012072267517234896765)
  ·
    refine ⟨14454754527100318963086287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38546012072267517234896765 14454754527100318963086287)
    ·
      refine ⟨21682131790650478444629431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14454754527100318963086287 21682131790650478444629431)
      ·
        refine ⟨32523197685975717666944147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21682131790650478444629431 32523197685975717666944147)
        ·
          refine ⟨48784796528963576500416221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32523197685975717666944147 48784796528963576500416221)
          ·
            refine ⟨18294298698361341187656083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48784796528963576500416221 18294298698361341187656083)
            ·
              refine ⟨27441448047542011781484125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18294298698361341187656083 27441448047542011781484125)
              ·
                refine ⟨10290543017828254418056547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27441448047542011781484125 10290543017828254418056547)
                ·
                  refine ⟨15435814526742381627084821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10290543017828254418056547 15435814526742381627084821)
                  ·
                    refine ⟨723553805941049138769601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15435814526742381627084821 723553805941049138769601)
                    ·
                      refine ⟨542665354455786854077201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 723553805941049138769601 542665354455786854077201)
                      ·
                        rfl

theorem cell23_1056837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 6, 2].length) (baseStart_1056837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056837 prefixEnd_1056837 := by exact prefixLift 1056837
  have htrace : WordTrace (prefixWord ++ tailWord_1056837) baseStart_1056837 baseEnd_1056837 := by
    simpa [prefixWord, tailWord_1056837, baseEnd_1056837] using wordTrace_append hprefix tailTrace_1056837
  have hstable : (prefixWord ++ tailWord_1056837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056837).length < 2 ^ (prefixWord ++ tailWord_1056837).sum := by decide
  have hdescent : baseEnd_1056837 < baseStart_1056837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056924 : List Nat := [2, 2, 3, 2, 1, 1, 3, 3, 1, 5]
def baseStart_1056924 : Nat := 118140960795 + 1056924 * 2 ^ 59
def prefixEnd_1056924 : Nat := 4983230072969 + 3 ^ 40 * 1056924 * 2
def baseEnd_1056924 : Nat := 180903342424242671229767

theorem tailTrace_1056924 : CollatzResearch.WordTrace tailWord_1056924 prefixEnd_1056924 180903342424242671229767 := by
  unfold tailWord_1056924
  simp only [CollatzResearch.WordTrace]
  refine ⟨19274592611476165546656913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25699456815301554062209217 19274592611476165546656913)
  ·
    refine ⟨14455944458607124159992685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19274592611476165546656913 14455944458607124159992685)
    ·
      refine ⟨5420979171977671559997257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14455944458607124159992685 5420979171977671559997257)
      ·
        refine ⟨4065734378983253669997943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5420979171977671559997257 4065734378983253669997943)
        ·
          refine ⟨6098601568474880504996915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4065734378983253669997943 6098601568474880504996915)
          ·
            refine ⟨9147902352712320757495373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6098601568474880504996915 9147902352712320757495373)
            ·
              refine ⟨3430463382267120284060765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9147902352712320757495373 3430463382267120284060765)
              ·
                refine ⟨1286423768350170106522787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3430463382267120284060765 1286423768350170106522787)
                ·
                  refine ⟨1929635652525255159784181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1286423768350170106522787 1929635652525255159784181)
                  ·
                    refine ⟨180903342424242671229767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1929635652525255159784181 180903342424242671229767)
                    ·
                      rfl

theorem cell23_1056924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_1056924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056924 prefixEnd_1056924 := by exact prefixLift 1056924
  have htrace : WordTrace (prefixWord ++ tailWord_1056924) baseStart_1056924 baseEnd_1056924 := by
    simpa [prefixWord, tailWord_1056924, baseEnd_1056924] using wordTrace_append hprefix tailTrace_1056924
  have hstable : (prefixWord ++ tailWord_1056924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056924).length < 2 ^ (prefixWord ++ tailWord_1056924).sum := by decide
  have hdescent : baseEnd_1056924 < baseStart_1056924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056954 : List Nat := [3, 1, 1, 1, 2, 2, 2, 5, 2, 4]
def baseStart_1056954 : Nat := 118140960795 + 1056954 * 2 ^ 59
def prefixEnd_1056954 : Nat := 4983230072969 + 3 ^ 40 * 1056954 * 2
def baseEnd_1056954 : Nat := 180908477230787632104721

theorem tailTrace_1056954 : CollatzResearch.WordTrace tailWord_1056954 prefixEnd_1056954 180908477230787632104721 := by
  unfold tailWord_1056954
  simp only [CollatzResearch.WordTrace]
  refine ⟨9637569853210911554226479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25700186275229097477937277 9637569853210911554226479)
  ·
    refine ⟨14456354779816367331339719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9637569853210911554226479 14456354779816367331339719)
    ·
      refine ⟨21684532169724550997009579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14456354779816367331339719 21684532169724550997009579)
      ·
        refine ⟨32526798254586826495514369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21684532169724550997009579 32526798254586826495514369)
        ·
          refine ⟨24395098690940119871635777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32526798254586826495514369 24395098690940119871635777)
          ·
            refine ⟨18296324018205089903726833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24395098690940119871635777 18296324018205089903726833)
            ·
              refine ⟨13722243013653817427795125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18296324018205089903726833 13722243013653817427795125)
              ·
                refine ⟨1286460282530045383855793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13722243013653817427795125 1286460282530045383855793)
                ·
                  refine ⟨964845211897534037891845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1286460282530045383855793 964845211897534037891845)
                  ·
                    refine ⟨180908477230787632104721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 964845211897534037891845 180908477230787632104721)
                    ·
                      rfl

theorem cell23_1056954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 2, 4].length) (baseStart_1056954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056954 prefixEnd_1056954 := by exact prefixLift 1056954
  have htrace : WordTrace (prefixWord ++ tailWord_1056954) baseStart_1056954 baseEnd_1056954 := by
    simpa [prefixWord, tailWord_1056954, baseEnd_1056954] using wordTrace_append hprefix tailTrace_1056954
  have hstable : (prefixWord ++ tailWord_1056954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056954).length < 2 ^ (prefixWord ++ tailWord_1056954).sum := by decide
  have hdescent : baseEnd_1056954 < baseStart_1056954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056972 : List Nat := [2, 2, 1, 6, 1, 2, 1, 3, 1, 1, 3]
def baseStart_1056972 : Nat := 118140960795 + 1056972 * 2 ^ 59
def prefixEnd_1056972 : Nat := 4983230072969 + 3 ^ 40 * 1056972 * 2
def baseEnd_1056972 : Nat := 542734674344143825889081

theorem tailTrace_1056972 : CollatzResearch.WordTrace tailWord_1056972 prefixEnd_1056972 542734674344143825889081 := by
  unfold tailWord_1056972
  simp only [CollatzResearch.WordTrace]
  refine ⟨19275467963389217645530585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25700623951185623527374113 19275467963389217645530585)
  ·
    refine ⟨14456600972541913234147939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19275467963389217645530585 14456600972541913234147939)
    ·
      refine ⟨21684901458812869851221909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14456600972541913234147939 21684901458812869851221909)
      ·
        refine ⟨1016479755881853274276027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 21684901458812869851221909 1016479755881853274276027)
        ·
          refine ⟨1524719633822779911414041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1016479755881853274276027 1524719633822779911414041)
          ·
            refine ⟨1143539725367084933560531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1524719633822779911414041 1143539725367084933560531)
            ·
              refine ⟨1715309588050627400340797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1143539725367084933560531 1715309588050627400340797)
              ·
                refine ⟨643241095518985275127799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1715309588050627400340797 643241095518985275127799)
                ·
                  refine ⟨964861643278477912691699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 643241095518985275127799 964861643278477912691699)
                  ·
                    refine ⟨1447292464917716869037549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 964861643278477912691699 1447292464917716869037549)
                    ·
                      refine ⟨542734674344143825889081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1447292464917716869037549 542734674344143825889081)
                      ·
                        rfl

theorem cell23_1056972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_1056972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056972 prefixEnd_1056972 := by exact prefixLift 1056972
  have htrace : WordTrace (prefixWord ++ tailWord_1056972) baseStart_1056972 baseEnd_1056972 := by
    simpa [prefixWord, tailWord_1056972, baseEnd_1056972] using wordTrace_append hprefix tailTrace_1056972
  have hstable : (prefixWord ++ tailWord_1056972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056972).length < 2 ^ (prefixWord ++ tailWord_1056972).sum := by decide
  have hdescent : baseEnd_1056972 < baseStart_1056972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056981 : List Nat := [1, 3, 2, 4, 2, 1, 2, 1, 1, 1, 5]
def baseStart_1056981 : Nat := 118140960795 + 1056981 * 2 ^ 59
def prefixEnd_1056981 : Nat := 4983230072969 + 3 ^ 40 * 1056981 * 2
def baseEnd_1056981 : Nat := 542739295670034290676539

theorem tailTrace_1056981 : CollatzResearch.WordTrace tailWord_1056981 prefixEnd_1056981 542739295670034290676539 := by
  unfold tailWord_1056981
  simp only [CollatzResearch.WordTrace]
  refine ⟨38551264183745829828138797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25700842789163886552092531 38551264183745829828138797)
  ·
    refine ⟨14456724068904686185552049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38551264183745829828138797 14456724068904686185552049)
    ·
      refine ⟨10842543051678514639164037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14456724068904686185552049 10842543051678514639164037)
      ·
        refine ⟨2032976822189721494843257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10842543051678514639164037 2032976822189721494843257)
        ·
          refine ⟨1524732616642291121132443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2032976822189721494843257 1524732616642291121132443)
          ·
            refine ⟨2287098924963436681698665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1524732616642291121132443 2287098924963436681698665)
            ·
              refine ⟨1715324193722577511273999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2287098924963436681698665 1715324193722577511273999)
              ·
                refine ⟨2572986290583866266910999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1715324193722577511273999 2572986290583866266910999)
                ·
                  refine ⟨3859479435875799400366499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2572986290583866266910999 3859479435875799400366499)
                  ·
                    refine ⟨5789219153813699100549749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3859479435875799400366499 5789219153813699100549749)
                    ·
                      refine ⟨542739295670034290676539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5789219153813699100549749 542739295670034290676539)
                      ·
                        rfl

theorem cell23_1056981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_1056981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1056981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1056981 prefixEnd_1056981 := by exact prefixLift 1056981
  have htrace : WordTrace (prefixWord ++ tailWord_1056981) baseStart_1056981 baseEnd_1056981 := by
    simpa [prefixWord, tailWord_1056981, baseEnd_1056981] using wordTrace_append hprefix tailTrace_1056981
  have hstable : (prefixWord ++ tailWord_1056981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056981).length < 2 ^ (prefixWord ++ tailWord_1056981).sum := by decide
  have hdescent : baseEnd_1056981 < baseStart_1056981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057005 : List Nat := [1, 5, 1, 2, 3, 2, 2, 1, 2, 4]
def baseStart_1057005 : Nat := 118140960795 + 1057005 * 2 ^ 59
def prefixEnd_1057005 : Nat := 4983230072969 + 3 ^ 40 * 1057005 * 2
def baseEnd_1057005 : Nat := 180917206401914065592143

theorem tailTrace_1057005 : CollatzResearch.WordTrace tailWord_1057005 prefixEnd_1057005 180917206401914065592143 := by
  unfold tailWord_1057005
  simp only [CollatzResearch.WordTrace]
  refine ⟨38552139535658881927012469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25701426357105921284674979 38552139535658881927012469)
  ·
    refine ⟨3614263081468020180657419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38552139535658881927012469 3614263081468020180657419)
    ·
      refine ⟨5421394622202030270986129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3614263081468020180657419 5421394622202030270986129)
      ·
        refine ⟨4066045966651522703239597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5421394622202030270986129 4066045966651522703239597)
        ·
          refine ⟨1524767237494321013714849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4066045966651522703239597 1524767237494321013714849)
          ·
            refine ⟨1143575428120740760286137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1524767237494321013714849 1143575428120740760286137)
            ·
              refine ⟨857681571090555570214603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1143575428120740760286137 857681571090555570214603)
              ·
                refine ⟨1286522356635833355321905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 857681571090555570214603 1286522356635833355321905)
                ·
                  refine ⟨964891767476875016491429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1286522356635833355321905 964891767476875016491429)
                  ·
                    refine ⟨180917206401914065592143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 964891767476875016491429 180917206401914065592143)
                    ·
                      rfl

theorem cell23_1057005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_1057005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057005 prefixEnd_1057005 := by exact prefixLift 1057005
  have htrace : WordTrace (prefixWord ++ tailWord_1057005) baseStart_1057005 baseEnd_1057005 := by
    simpa [prefixWord, tailWord_1057005, baseEnd_1057005] using wordTrace_append hprefix tailTrace_1057005
  have hstable : (prefixWord ++ tailWord_1057005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057005).length < 2 ^ (prefixWord ++ tailWord_1057005).sum := by decide
  have hdescent : baseEnd_1057005 < baseStart_1057005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057011 : List Nat := [1, 1, 1, 2, 2, 4, 3, 3, 2, 1, 3]
def baseStart_1057011 : Nat := 118140960795 + 1057011 * 2 ^ 59
def prefixEnd_1057011 : Nat := 4983230072969 + 3 ^ 40 * 1057011 * 2
def baseEnd_1057011 : Nat := 542754700089669173301401

theorem tailTrace_1057011 : CollatzResearch.WordTrace tailWord_1057011 prefixEnd_1057011 542754700089669173301401 := by
  unfold tailWord_1057011
  simp only [CollatzResearch.WordTrace]
  refine ⟨38552358373637144951730887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25701572249091429967820591 38552358373637144951730887)
  ·
    refine ⟨57828537560455717427596331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38552358373637144951730887 57828537560455717427596331)
    ·
      refine ⟨86742806340683576141394497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57828537560455717427596331 86742806340683576141394497)
      ·
        refine ⟨65057104755512682106045873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86742806340683576141394497 65057104755512682106045873)
        ·
          refine ⟨48792828566634511579534405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65057104755512682106045873 48792828566634511579534405)
          ·
            refine ⟨9148655356243970921162701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48792828566634511579534405 9148655356243970921162701)
            ·
              refine ⟨3430745758591489095436013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9148655356243970921162701 3430745758591489095436013)
              ·
                refine ⟨1286529659471808410788505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3430745758591489095436013 1286529659471808410788505)
                ·
                  refine ⟨964897244603856308091379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1286529659471808410788505 964897244603856308091379)
                  ·
                    refine ⟨1447345866905784462137069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 964897244603856308091379 1447345866905784462137069)
                    ·
                      refine ⟨542754700089669173301401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1447345866905784462137069 542754700089669173301401)
                      ·
                        rfl

theorem cell23_1057011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 2, 1, 3].length) (baseStart_1057011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057011 prefixEnd_1057011 := by exact prefixLift 1057011
  have htrace : WordTrace (prefixWord ++ tailWord_1057011) baseStart_1057011 baseEnd_1057011 := by
    simpa [prefixWord, tailWord_1057011, baseEnd_1057011] using wordTrace_append hprefix tailTrace_1057011
  have hstable : (prefixWord ++ tailWord_1057011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057011).length < 2 ^ (prefixWord ++ tailWord_1057011).sum := by decide
  have hdescent : baseEnd_1057011 < baseStart_1057011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057017 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 4, 3, 4]
def baseStart_1057017 : Nat := 118140960795 + 1057017 * 2 ^ 59
def prefixEnd_1057017 : Nat := 4983230072969 + 3 ^ 40 * 1057017 * 2
def baseEnd_1057017 : Nat := 542757780973596149826373

theorem tailTrace_1057017 : CollatzResearch.WordTrace tailWord_1057017 prefixEnd_1057017 542757780973596149826373 := by
  unfold tailWord_1057017
  simp only [CollatzResearch.WordTrace]
  refine ⟨38552577211615407976449305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25701718141076938650966203 38552577211615407976449305)
  ·
    refine ⟨28914432908711555982336979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38552577211615407976449305 28914432908711555982336979)
    ·
      refine ⟨43371649363067333973505469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28914432908711555982336979 43371649363067333973505469)
      ·
        refine ⟨16264368511150250240064551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43371649363067333973505469 16264368511150250240064551)
        ·
          refine ⟨24396552766725375360096827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16264368511150250240064551 24396552766725375360096827)
          ·
            refine ⟨36594829150088063040145241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24396552766725375360096827 36594829150088063040145241)
            ·
              refine ⟨27446121862566047280108931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36594829150088063040145241 27446121862566047280108931)
              ·
                refine ⟨41169182793849070920163397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27446121862566047280108931 41169182793849070920163397)
                ·
                  refine ⟨7719221773846700797530637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41169182793849070920163397 7719221773846700797530637)
                  ·
                    refine ⟨2894708165192512799073989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7719221773846700797530637 2894708165192512799073989)
                    ·
                      refine ⟨542757780973596149826373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2894708165192512799073989 542757780973596149826373)
                      ·
                        rfl

theorem cell23_1057017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_1057017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057017 prefixEnd_1057017 := by exact prefixLift 1057017
  have htrace : WordTrace (prefixWord ++ tailWord_1057017) baseStart_1057017 baseEnd_1057017 := by
    simpa [prefixWord, tailWord_1057017, baseEnd_1057017] using wordTrace_append hprefix tailTrace_1057017
  have hstable : (prefixWord ++ tailWord_1057017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057017).length < 2 ^ (prefixWord ++ tailWord_1057017).sum := by decide
  have hdescent : baseEnd_1057017 < baseStart_1057017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057051 : List Nat := [1, 1, 1, 1, 1, 1, 6, 3, 4, 2, 2]
def baseStart_1057051 : Nat := 118140960795 + 1057051 * 2 ^ 59
def prefixEnd_1057051 : Nat := 4983230072969 + 3 ^ 40 * 1057051 * 2
def baseEnd_1057051 : Nat := 542775239315849016801217

theorem tailTrace_1057051 : CollatzResearch.WordTrace tailWord_1057051 prefixEnd_1057051 542775239315849016801217 := by
  unfold tailWord_1057051
  simp only [CollatzResearch.WordTrace]
  refine ⟨38553817293492231783187007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25702544862328154522124671 38553817293492231783187007)
  ·
    refine ⟨57830725940238347674780511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38553817293492231783187007 57830725940238347674780511)
    ·
      refine ⟨86746088910357521512170767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57830725940238347674780511 86746088910357521512170767)
      ·
        refine ⟨130119133365536282268256151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86746088910357521512170767 130119133365536282268256151)
        ·
          refine ⟨195178700048304423402384227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130119133365536282268256151 195178700048304423402384227)
          ·
            refine ⟨292768050072456635103576341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195178700048304423402384227 292768050072456635103576341)
            ·
              refine ⟨13723502347146404770480141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 292768050072456635103576341 13723502347146404770480141)
              ·
                refine ⟨5146313380179901788930053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13723502347146404770480141 5146313380179901788930053)
                ·
                  refine ⟨964933758783731585424385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5146313380179901788930053 964933758783731585424385)
                  ·
                    refine ⟨723700319087798689068289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 964933758783731585424385 723700319087798689068289)
                    ·
                      refine ⟨542775239315849016801217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 723700319087798689068289 542775239315849016801217)
                      ·
                        rfl

theorem cell23_1057051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 4, 2, 2].length) (baseStart_1057051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057051 prefixEnd_1057051 := by exact prefixLift 1057051
  have htrace : WordTrace (prefixWord ++ tailWord_1057051) baseStart_1057051 baseEnd_1057051 := by
    simpa [prefixWord, tailWord_1057051, baseEnd_1057051] using wordTrace_append hprefix tailTrace_1057051
  have hstable : (prefixWord ++ tailWord_1057051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057051).length < 2 ^ (prefixWord ++ tailWord_1057051).sum := by decide
  have hdescent : baseEnd_1057051 < baseStart_1057051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057068 : List Nat := [2, 2, 1, 1, 1, 3, 4, 3, 2, 2, 2]
def baseStart_1057068 : Nat := 118140960795 + 1057068 * 2 ^ 59
def prefixEnd_1057068 : Nat := 4983230072969 + 3 ^ 40 * 1057068 * 2
def baseEnd_1057068 : Nat := 542783968486975450288639

theorem tailTrace_1057068 : CollatzResearch.WordTrace tailWord_1057068 prefixEnd_1057068 542783968486975450288639 := by
  unfold tailWord_1057068
  simp only [CollatzResearch.WordTrace]
  refine ⟨19277218667215321843277929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25702958222953762457703905 19277218667215321843277929)
  ·
    refine ⟨14457914000411491382458447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19277218667215321843277929 14457914000411491382458447)
    ·
      refine ⟨21686871000617237073687671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14457914000411491382458447 21686871000617237073687671)
      ·
        refine ⟨32530306500925855610531507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21686871000617237073687671 32530306500925855610531507)
        ·
          refine ⟨48795459751388783415797261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32530306500925855610531507 48795459751388783415797261)
          ·
            refine ⟨18298297406770793780923973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48795459751388783415797261 18298297406770793780923973)
            ·
              refine ⟨3430930763769523833923245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18298297406770793780923973 3430930763769523833923245)
              ·
                refine ⟨1286599036413571437721217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3430930763769523833923245 1286599036413571437721217)
                ·
                  refine ⟨964949277310178578290913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1286599036413571437721217 964949277310178578290913)
                  ·
                    refine ⟨723711957982633933718185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 964949277310178578290913 723711957982633933718185)
                    ·
                      refine ⟨542783968486975450288639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 723711957982633933718185 542783968486975450288639)
                      ·
                        rfl

theorem cell23_1057068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 2, 2].length) (baseStart_1057068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057068 prefixEnd_1057068 := by exact prefixLift 1057068
  have htrace : WordTrace (prefixWord ++ tailWord_1057068) baseStart_1057068 baseEnd_1057068 := by
    simpa [prefixWord, tailWord_1057068, baseEnd_1057068] using wordTrace_append hprefix tailTrace_1057068
  have hstable : (prefixWord ++ tailWord_1057068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057068).length < 2 ^ (prefixWord ++ tailWord_1057068).sum := by decide
  have hdescent : baseEnd_1057068 < baseStart_1057068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057084 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 1, 5, 3]
def baseStart_1057084 : Nat := 118140960795 + 1057084 * 2 ^ 59
def prefixEnd_1057084 : Nat := 4983230072969 + 3 ^ 40 * 1057084 * 2
def baseEnd_1057084 : Nat := 542792184177447387688565

theorem tailTrace_1057084 : CollatzResearch.WordTrace tailWord_1057084 prefixEnd_1057084 542792184177447387688565 := by
  unfold tailWord_1057084
  simp only [CollatzResearch.WordTrace]
  refine ⟨19277510451186339209569153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25703347268248452279425537 19277510451186339209569153)
  ·
    refine ⟨14458132838389754407176865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19277510451186339209569153 14458132838389754407176865)
    ·
      refine ⟨10843599628792315805382649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14458132838389754407176865 10843599628792315805382649)
      ·
        refine ⟨8132699721594236854036987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10843599628792315805382649 8132699721594236854036987)
        ·
          refine ⟨12199049582391355281055481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8132699721594236854036987 12199049582391355281055481)
          ·
            refine ⟨9149287186793516460791611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12199049582391355281055481 9149287186793516460791611)
            ·
              refine ⟨13723930780190274691187417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9149287186793516460791611 13723930780190274691187417)
              ·
                refine ⟨10292948085142706018390563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13723930780190274691187417 10292948085142706018390563)
                ·
                  refine ⟨15439422127714059027585845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10292948085142706018390563 15439422127714059027585845)
                  ·
                    refine ⟨1447445824473193033836173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15439422127714059027585845 1447445824473193033836173)
                    ·
                      refine ⟨542792184177447387688565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1447445824473193033836173 542792184177447387688565)
                      ·
                        rfl

theorem cell23_1057084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_1057084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057084 prefixEnd_1057084 := by exact prefixLift 1057084
  have htrace : WordTrace (prefixWord ++ tailWord_1057084) baseStart_1057084 baseEnd_1057084 := by
    simpa [prefixWord, tailWord_1057084, baseEnd_1057084] using wordTrace_append hprefix tailTrace_1057084
  have hstable : (prefixWord ++ tailWord_1057084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057084).length < 2 ^ (prefixWord ++ tailWord_1057084).sum := by decide
  have hdescent : baseEnd_1057084 < baseStart_1057084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057089 : List Nat := [1, 2, 5, 2, 3, 1, 2, 1, 1, 3, 2]
def baseStart_1057089 : Nat := 118140960795 + 1057089 * 2 ^ 59
def prefixEnd_1057089 : Nat := 4983230072969 + 3 ^ 40 * 1057089 * 2
def baseEnd_1057089 : Nat := 542794751580719868126043

theorem tailTrace_1057089 : CollatzResearch.WordTrace tailWord_1057089 prefixEnd_1057089 542794751580719868126043 := by
  unfold tailWord_1057089
  simp only [CollatzResearch.WordTrace]
  refine ⟨38555203267354564273070321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25703468844903042848713547 38555203267354564273070321)
  ·
    refine ⟨28916402450515923204802741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38555203267354564273070321 28916402450515923204802741)
    ·
      refine ⟨2710912729735867800450257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28916402450515923204802741 2710912729735867800450257)
      ·
        refine ⟨2033184547301900850337693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2710912729735867800450257 2033184547301900850337693)
        ·
          refine ⟨762444205238212818876635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2033184547301900850337693 762444205238212818876635)
          ·
            refine ⟨1143666307857319228314953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 762444205238212818876635 1143666307857319228314953)
            ·
              refine ⟨857749730892989421236215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1143666307857319228314953 857749730892989421236215)
              ·
                refine ⟨1286624596339484131854323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 857749730892989421236215 1286624596339484131854323)
                ·
                  refine ⟨1929936894509226197781485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1286624596339484131854323 1929936894509226197781485)
                  ·
                    refine ⟨723726335440959824168057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1929936894509226197781485 723726335440959824168057)
                    ·
                      refine ⟨542794751580719868126043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 723726335440959824168057 542794751580719868126043)
                      ·
                        rfl

theorem cell23_1057089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_1057089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057089 prefixEnd_1057089 := by exact prefixLift 1057089
  have htrace : WordTrace (prefixWord ++ tailWord_1057089) baseStart_1057089 baseEnd_1057089 := by
    simpa [prefixWord, tailWord_1057089, baseEnd_1057089] using wordTrace_append hprefix tailTrace_1057089
  have hstable : (prefixWord ++ tailWord_1057089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057089).length < 2 ^ (prefixWord ++ tailWord_1057089).sum := by decide
  have hdescent : baseEnd_1057089 < baseStart_1057089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057124 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 3, 3, 4]
def baseStart_1057124 : Nat := 118140960795 + 1057124 * 2 ^ 59
def prefixEnd_1057124 : Nat := 4983230072969 + 3 ^ 40 * 1057124 * 2
def baseEnd_1057124 : Nat := 542812723403627231188381

theorem tailTrace_1057124 : CollatzResearch.WordTrace tailWord_1057124 prefixEnd_1057124 542812723403627231188381 := by
  unfold tailWord_1057124
  simp only [CollatzResearch.WordTrace]
  refine ⟨19278239911113882625297213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25704319881485176833729617 19278239911113882625297213)
  ·
    refine ⟨7229339966667705984486455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19278239911113882625297213 7229339966667705984486455)
    ·
      refine ⟨10844009950001558976729683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7229339966667705984486455 10844009950001558976729683)
      ·
        refine ⟨16266014925002338465094525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10844009950001558976729683 16266014925002338465094525)
        ·
          refine ⟨6099755596875876924410447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16266014925002338465094525 6099755596875876924410447)
          ·
            refine ⟨9149633395313815386615671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6099755596875876924410447 9149633395313815386615671)
            ·
              refine ⟨13724450092970723079923507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9149633395313815386615671 13724450092970723079923507)
              ·
                refine ⟨20586675139456084619885261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13724450092970723079923507 20586675139456084619885261)
                ·
                  refine ⟨7720003177296031732456973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20586675139456084619885261 7720003177296031732456973)
                  ·
                    refine ⟨2895001191486011899671365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7720003177296031732456973 2895001191486011899671365)
                    ·
                      refine ⟨542812723403627231188381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2895001191486011899671365 542812723403627231188381)
                      ·
                        rfl

theorem cell23_1057124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_1057124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057124 prefixEnd_1057124 := by exact prefixLift 1057124
  have htrace : WordTrace (prefixWord ++ tailWord_1057124) baseStart_1057124 baseEnd_1057124 := by
    simpa [prefixWord, tailWord_1057124, baseEnd_1057124] using wordTrace_append hprefix tailTrace_1057124
  have hstable : (prefixWord ++ tailWord_1057124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057124).length < 2 ^ (prefixWord ++ tailWord_1057124).sum := by decide
  have hdescent : baseEnd_1057124 < baseStart_1057124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057141 : List Nat := [1, 3, 4, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_1057141 : Nat := 118140960795 + 1057141 * 2 ^ 59
def prefixEnd_1057141 : Nat := 4983230072969 + 3 ^ 40 * 1057141 * 2
def baseEnd_1057141 : Nat := 542821452574753664675803

theorem tailTrace_1057141 : CollatzResearch.WordTrace tailWord_1057141 prefixEnd_1057141 542821452574753664675803 := by
  unfold tailWord_1057141
  simp only [CollatzResearch.WordTrace]
  refine ⟨38557099863166177153963277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25704733242110784769308851 38557099863166177153963277)
  ·
    refine ⟨14458912448687316432736229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38557099863166177153963277 14458912448687316432736229)
    ·
      refine ⟨2711046084128871831138043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14458912448687316432736229 2711046084128871831138043)
      ·
        refine ⟨4066569126193307746707065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2711046084128871831138043 4066569126193307746707065)
        ·
          refine ⟨3049926844644980810030299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4066569126193307746707065 3049926844644980810030299)
          ·
            refine ⟨4574890266967471215045449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3049926844644980810030299 4574890266967471215045449)
            ·
              refine ⟨3431167700225603411284087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4574890266967471215045449 3431167700225603411284087)
              ·
                refine ⟨5146751550338405116926131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3431167700225603411284087 5146751550338405116926131)
                ·
                  refine ⟨7720127325507607675389197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5146751550338405116926131 7720127325507607675389197)
                  ·
                    refine ⟨2895047747065352878270949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7720127325507607675389197 2895047747065352878270949)
                    ·
                      refine ⟨542821452574753664675803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2895047747065352878270949 542821452574753664675803)
                      ·
                        rfl

theorem cell23_1057141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_1057141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057141 prefixEnd_1057141 := by exact prefixLift 1057141
  have htrace : WordTrace (prefixWord ++ tailWord_1057141) baseStart_1057141 baseEnd_1057141 := by
    simpa [prefixWord, tailWord_1057141, baseEnd_1057141] using wordTrace_append hprefix tailTrace_1057141
  have hstable : (prefixWord ++ tailWord_1057141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057141).length < 2 ^ (prefixWord ++ tailWord_1057141).sum := by decide
  have hdescent : baseEnd_1057141 < baseStart_1057141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057142 : List Nat := [5, 1, 1, 4, 1, 2, 1, 3, 5]
def baseStart_1057142 : Nat := 118140960795 + 1057142 * 2 ^ 59
def prefixEnd_1057142 : Nat := 4983230072969 + 3 ^ 40 * 1057142 * 2
def baseEnd_1057142 : Nat := 60313551783934240084811

theorem tailTrace_1057142 : CollatzResearch.WordTrace tailWord_1057142 prefixEnd_1057142 60313551783934240084811 := by
  unfold tailWord_1057142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2409821021010159645296855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25704757557441702883166453 2409821021010159645296855)
  ·
    refine ⟨3614731531515239467945283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2409821021010159645296855 3614731531515239467945283)
    ·
      refine ⟨5422097297272859201917925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3614731531515239467945283 5422097297272859201917925)
      ·
        refine ⟨1016643243238661100359611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5422097297272859201917925 1016643243238661100359611)
        ·
          refine ⟨1524964864857991650539417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1016643243238661100359611 1524964864857991650539417)
          ·
            refine ⟨1143723648643493737904563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1524964864857991650539417 1143723648643493737904563)
            ·
              refine ⟨1715585472965240606856845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1143723648643493737904563 1715585472965240606856845)
              ·
                refine ⟨643344552361965227571317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1715585472965240606856845 643344552361965227571317)
                ·
                  refine ⟨60313551783934240084811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 643344552361965227571317 60313551783934240084811)
                  ·
                    rfl

theorem cell23_1057142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_1057142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057142 prefixEnd_1057142 := by exact prefixLift 1057142
  have htrace : WordTrace (prefixWord ++ tailWord_1057142) baseStart_1057142 baseEnd_1057142 := by
    simpa [prefixWord, tailWord_1057142, baseEnd_1057142] using wordTrace_append hprefix tailTrace_1057142
  have hstable : (prefixWord ++ tailWord_1057142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057142).length < 2 ^ (prefixWord ++ tailWord_1057142).sum := by decide
  have hdescent : baseEnd_1057142 < baseStart_1057142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057161 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 4, 2, 3]
def baseStart_1057161 : Nat := 118140960795 + 1057161 * 2 ^ 59
def prefixEnd_1057161 : Nat := 4983230072969 + 3 ^ 40 * 1057161 * 2
def baseEnd_1057161 : Nat := 542831722187843586425711

theorem tailTrace_1057161 : CollatzResearch.WordTrace tailWord_1057161 prefixEnd_1057161 542831722187843586425711 := by
  unfold tailWord_1057161
  simp only [CollatzResearch.WordTrace]
  refine ⟨38557829323093720569691337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25705219548729147046460891 38557829323093720569691337)
  ·
    refine ⟨28918371992320290427268503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38557829323093720569691337 28918371992320290427268503)
    ·
      refine ⟨43377557988480435640902755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28918371992320290427268503 43377557988480435640902755)
      ·
        refine ⟨65066336982720653461354133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43377557988480435640902755 65066336982720653461354133)
        ·
          refine ⟨3049984546065030631000975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 65066336982720653461354133 3049984546065030631000975)
          ·
            refine ⟨4574976819097545946501463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3049984546065030631000975 4574976819097545946501463)
            ·
              refine ⟨6862465228646318919752195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4574976819097545946501463 6862465228646318919752195)
              ·
                refine ⟨10293697842969478379628293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6862465228646318919752195 10293697842969478379628293)
                ·
                  refine ⟨1930068345556777196180305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10293697842969478379628293 1930068345556777196180305)
                  ·
                    refine ⟨1447551259167582897135229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1930068345556777196180305 1447551259167582897135229)
                    ·
                      refine ⟨542831722187843586425711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1447551259167582897135229 542831722187843586425711)
                      ·
                        rfl

theorem cell23_1057161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 2, 3].length) (baseStart_1057161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057161 prefixEnd_1057161 := by exact prefixLift 1057161
  have htrace : WordTrace (prefixWord ++ tailWord_1057161) baseStart_1057161 baseEnd_1057161 := by
    simpa [prefixWord, tailWord_1057161, baseEnd_1057161] using wordTrace_append hprefix tailTrace_1057161
  have hstable : (prefixWord ++ tailWord_1057161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057161).length < 2 ^ (prefixWord ++ tailWord_1057161).sum := by decide
  have hdescent : baseEnd_1057161 < baseStart_1057161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057164 : List Nat := [2, 2, 1, 2, 1, 4, 2, 1, 8]
def baseStart_1057164 : Nat := 118140960795 + 1057164 * 2 ^ 59
def prefixEnd_1057164 : Nat := 4983230072969 + 3 ^ 40 * 1057164 * 2
def baseEnd_1057164 : Nat := 60314806958867452743133

theorem tailTrace_1057164 : CollatzResearch.WordTrace tailWord_1057164 prefixEnd_1057164 60314806958867452743133 := by
  unfold tailWord_1057164
  simp only [CollatzResearch.WordTrace]
  refine ⟨19278969371041426041025273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25705292494721901388033697 19278969371041426041025273)
  ·
    refine ⟨14459227028281069530768955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19278969371041426041025273 14459227028281069530768955)
    ·
      refine ⟨21688840542421604296153433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14459227028281069530768955 21688840542421604296153433)
      ·
        refine ⟨16266630406816203222115075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21688840542421604296153433 16266630406816203222115075)
        ·
          refine ⟨24399945610224304833172613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16266630406816203222115075 24399945610224304833172613)
          ·
            refine ⟨4574989801917057156219865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24399945610224304833172613 4574989801917057156219865)
            ·
              refine ⟨3431242351437792867164899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4574989801917057156219865 3431242351437792867164899)
              ·
                refine ⟨5146863527156689300747349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3431242351437792867164899 5146863527156689300747349)
                ·
                  refine ⟨60314806958867452743133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5146863527156689300747349 60314806958867452743133)
                  ·
                    rfl

theorem cell23_1057164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 8].length) (baseStart_1057164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057164 prefixEnd_1057164 := by exact prefixLift 1057164
  have htrace : WordTrace (prefixWord ++ tailWord_1057164) baseStart_1057164 baseEnd_1057164 := by
    simpa [prefixWord, tailWord_1057164, baseEnd_1057164] using wordTrace_append hprefix tailTrace_1057164
  have hstable : (prefixWord ++ tailWord_1057164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057164).length < 2 ^ (prefixWord ++ tailWord_1057164).sum := by decide
  have hdescent : baseEnd_1057164 < baseStart_1057164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057231 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 2, 6, 2]
def baseStart_1057231 : Nat := 118140960795 + 1057231 * 2 ^ 59
def prefixEnd_1057231 : Nat := 4983230072969 + 3 ^ 40 * 1057231 * 2
def baseEnd_1057231 : Nat := 542867665833658312550389

theorem tailTrace_1057231 : CollatzResearch.WordTrace tailWord_1057231 prefixEnd_1057231 542867665833658312550389 := by
  unfold tailWord_1057231
  simp only [CollatzResearch.WordTrace]
  refine ⟨38560382432840122524739547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25706921621893415016493031 38560382432840122524739547)
  ·
    refine ⟨57840573649260183787109321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38560382432840122524739547 57840573649260183787109321)
    ·
      refine ⟨43380430236945137840331991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57840573649260183787109321 43380430236945137840331991)
      ·
        refine ⟨65070645355417706760497987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43380430236945137840331991 65070645355417706760497987)
        ·
          refine ⟨97605968033126560140746981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65070645355417706760497987 97605968033126560140746981)
          ·
            refine ⟨18301119006211230026390059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97605968033126560140746981 18301119006211230026390059)
            ·
              refine ⟨27451678509316845039585089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18301119006211230026390059 27451678509316845039585089)
              ·
                refine ⟨20588758881987633779688817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27451678509316845039585089 20588758881987633779688817)
                ·
                  refine ⟨15441569161490725334766613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20588758881987633779688817 15441569161490725334766613)
                  ·
                    refine ⟨723823554444877750067185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15441569161490725334766613 723823554444877750067185)
                    ·
                      refine ⟨542867665833658312550389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 723823554444877750067185 542867665833658312550389)
                      ·
                        rfl

theorem cell23_1057231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 6, 2].length) (baseStart_1057231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057231 prefixEnd_1057231 := by exact prefixLift 1057231
  have htrace : WordTrace (prefixWord ++ tailWord_1057231) baseStart_1057231 baseEnd_1057231 := by
    simpa [prefixWord, tailWord_1057231, baseEnd_1057231] using wordTrace_append hprefix tailTrace_1057231
  have hstable : (prefixWord ++ tailWord_1057231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057231).length < 2 ^ (prefixWord ++ tailWord_1057231).sum := by decide
  have hdescent : baseEnd_1057231 < baseStart_1057231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057241 : List Nat := [1, 2, 1, 2, 4, 1, 4, 1, 1, 6]
def baseStart_1057241 : Nat := 118140960795 + 1057241 * 2 ^ 59
def prefixEnd_1057241 : Nat := 4983230072969 + 3 ^ 40 * 1057241 * 2
def baseEnd_1057241 : Nat := 180957600213401091141781

theorem tailTrace_1057241 : CollatzResearch.WordTrace tailWord_1057241 prefixEnd_1057241 180957600213401091141781 := by
  unfold tailWord_1057241
  simp only [CollatzResearch.WordTrace]
  refine ⟨38560747162803894232603577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25707164775202596155069051 38560747162803894232603577)
  ·
    refine ⟨28920560372102920674452683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38560747162803894232603577 28920560372102920674452683)
    ·
      refine ⟨43380840558154381011679025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28920560372102920674452683 43380840558154381011679025)
      ·
        refine ⟨32535630418615785758759269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43380840558154381011679025 32535630418615785758759269)
        ·
          refine ⟨6100430703490459829767363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32535630418615785758759269 6100430703490459829767363)
          ·
            refine ⟨9150646055235689744651045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6100430703490459829767363 9150646055235689744651045)
            ·
              refine ⟨1715746135356691827122071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9150646055235689744651045 1715746135356691827122071)
              ·
                refine ⟨2573619203035037740683107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1715746135356691827122071 2573619203035037740683107)
                ·
                  refine ⟨3860428804552556611024661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2573619203035037740683107 3860428804552556611024661)
                  ·
                    refine ⟨180957600213401091141781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3860428804552556611024661 180957600213401091141781)
                    ·
                      rfl

theorem cell23_1057241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 6].length) (baseStart_1057241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057241 prefixEnd_1057241 := by exact prefixLift 1057241
  have htrace : WordTrace (prefixWord ++ tailWord_1057241) baseStart_1057241 baseEnd_1057241 := by
    simpa [prefixWord, tailWord_1057241, baseEnd_1057241] using wordTrace_append hprefix tailTrace_1057241
  have hstable : (prefixWord ++ tailWord_1057241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057241).length < 2 ^ (prefixWord ++ tailWord_1057241).sum := by decide
  have hdescent : baseEnd_1057241 < baseStart_1057241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057372 : List Nat := [2, 2, 4, 1, 3, 1, 1, 2, 1, 4, 2]
def baseStart_1057372 : Nat := 118140960795 + 1057372 * 2 ^ 59
def prefixEnd_1057372 : Nat := 4983230072969 + 3 ^ 40 * 1057372 * 2
def baseEnd_1057372 : Nat := 542940066605942260887241

theorem tailTrace_1057372 : CollatzResearch.WordTrace tailWord_1057372 prefixEnd_1057372 542940066605942260887241 := by
  unfold tailWord_1057372
  simp only [CollatzResearch.WordTrace]
  refine ⟨19282762562664651802811185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25710350083552869070414913 19282762562664651802811185)
  ·
    refine ⟨14462071921998488852108389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19282762562664651802811185 14462071921998488852108389)
    ·
      refine ⟨2711638485374716659770323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14462071921998488852108389 2711638485374716659770323)
      ·
        refine ⟨4067457728062074989655485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2711638485374716659770323 4067457728062074989655485)
        ·
          refine ⟨1525296648023278121120807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4067457728062074989655485 1525296648023278121120807)
          ·
            refine ⟨2287944972034917181681211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1525296648023278121120807 2287944972034917181681211)
            ·
              refine ⟨3431917458052375772521817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2287944972034917181681211 3431917458052375772521817)
              ·
                refine ⟨2573938093539281829391363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3431917458052375772521817 2573938093539281829391363)
                ·
                  refine ⟨3860907140308922744087045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2573938093539281829391363 3860907140308922744087045)
                  ·
                    refine ⟨723920088807923014516321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3860907140308922744087045 723920088807923014516321)
                    ·
                      refine ⟨542940066605942260887241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 723920088807923014516321 542940066605942260887241)
                      ·
                        rfl

theorem cell23_1057372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_1057372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057372 prefixEnd_1057372 := by exact prefixLift 1057372
  have htrace : WordTrace (prefixWord ++ tailWord_1057372) baseStart_1057372 baseEnd_1057372 := by
    simpa [prefixWord, tailWord_1057372, baseEnd_1057372] using wordTrace_append hprefix tailTrace_1057372
  have hstable : (prefixWord ++ tailWord_1057372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057372).length < 2 ^ (prefixWord ++ tailWord_1057372).sum := by decide
  have hdescent : baseEnd_1057372 < baseStart_1057372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057389 : List Nat := [1, 5, 1, 1, 3, 2, 2, 2, 2, 2, 2]
def baseStart_1057389 : Nat := 118140960795 + 1057389 * 2 ^ 59
def prefixEnd_1057389 : Nat := 4983230072969 + 3 ^ 40 * 1057389 * 2
def baseEnd_1057389 : Nat := 542948795777068694374663

theorem tailTrace_1057389 : CollatzResearch.WordTrace tailWord_1057389 prefixEnd_1057389 542948795777068694374663 := by
  unfold tailWord_1057389
  simp only [CollatzResearch.WordTrace]
  refine ⟨38566145166267715508991221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25710763444178477005994147 38566145166267715508991221)
  ·
    refine ⟨3615576109337598328967927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38566145166267715508991221 3615576109337598328967927)
    ·
      refine ⟨5423364164006397493451891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3615576109337598328967927 5423364164006397493451891)
      ·
        refine ⟨8135046246009596240177837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5423364164006397493451891 8135046246009596240177837)
        ·
          refine ⟨3050642342253598590066689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8135046246009596240177837 3050642342253598590066689)
          ·
            refine ⟨2287981756690198942550017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3050642342253598590066689 2287981756690198942550017)
            ·
              refine ⟨1715986317517649206912513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2287981756690198942550017 1715986317517649206912513)
              ·
                refine ⟨1286989738138236905184385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1715986317517649206912513 1286989738138236905184385)
                ·
                  refine ⟨965242303603677678888289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1286989738138236905184385 965242303603677678888289)
                  ·
                    refine ⟨723931727702758259166217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 965242303603677678888289 723931727702758259166217)
                    ·
                      refine ⟨542948795777068694374663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 723931727702758259166217 542948795777068694374663)
                      ·
                        rfl

theorem cell23_1057389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_1057389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057389 prefixEnd_1057389 := by exact prefixLift 1057389
  have htrace : WordTrace (prefixWord ++ tailWord_1057389) baseStart_1057389 baseEnd_1057389 := by
    simpa [prefixWord, tailWord_1057389, baseEnd_1057389] using wordTrace_append hprefix tailTrace_1057389
  have hstable : (prefixWord ++ tailWord_1057389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057389).length < 2 ^ (prefixWord ++ tailWord_1057389).sum := by decide
  have hdescent : baseEnd_1057389 < baseStart_1057389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057405 : List Nat := [1, 4, 1, 1, 5, 1, 1, 1, 2, 3, 3]
def baseStart_1057405 : Nat := 118140960795 + 1057405 * 2 ^ 59
def prefixEnd_1057405 : Nat := 4983230072969 + 3 ^ 40 * 1057405 * 2
def baseEnd_1057405 : Nat := 542957011467540631774589

theorem tailTrace_1057405 : CollatzResearch.WordTrace tailWord_1057405 prefixEnd_1057405 542957011467540631774589 := by
  unfold tailWord_1057405
  simp only [CollatzResearch.WordTrace]
  refine ⟨38566728734209750241573669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25711152489473166827715779 38566728734209750241573669)
  ·
    refine ⟨7231261637664328170295063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38566728734209750241573669 7231261637664328170295063)
    ·
      refine ⟨10846892456496492255442595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7231261637664328170295063 10846892456496492255442595)
      ·
        refine ⟨16270338684744738383163893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10846892456496492255442595 16270338684744738383163893)
        ·
          refine ⟨1525344251694819223421615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16270338684744738383163893 1525344251694819223421615)
          ·
            refine ⟨2288016377542228835132423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1525344251694819223421615 2288016377542228835132423)
            ·
              refine ⟨3432024566313343252698635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2288016377542228835132423 3432024566313343252698635)
              ·
                refine ⟨5148036849470014879047953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3432024566313343252698635 5148036849470014879047953)
                ·
                  refine ⟨3861027637102511159285965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5148036849470014879047953 3861027637102511159285965)
                  ·
                    refine ⟨1447885363913441684732237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3861027637102511159285965 1447885363913441684732237)
                    ·
                      refine ⟨542957011467540631774589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1447885363913441684732237 542957011467540631774589)
                      ·
                        rfl

theorem cell23_1057405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_1057405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057405 prefixEnd_1057405 := by exact prefixLift 1057405
  have htrace : WordTrace (prefixWord ++ tailWord_1057405) baseStart_1057405 baseEnd_1057405 := by
    simpa [prefixWord, tailWord_1057405, baseEnd_1057405] using wordTrace_append hprefix tailTrace_1057405
  have hstable : (prefixWord ++ tailWord_1057405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057405).length < 2 ^ (prefixWord ++ tailWord_1057405).sum := by decide
  have hdescent : baseEnd_1057405 < baseStart_1057405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057455 : List Nat := [1, 1, 2, 1, 2, 6, 2, 1, 3, 4]
def baseStart_1057455 : Nat := 118140960795 + 1057455 * 2 ^ 59
def prefixEnd_1057455 : Nat := 4983230072969 + 3 ^ 40 * 1057455 * 2
def baseEnd_1057455 : Nat := 180994228500088478716453

theorem tailTrace_1057455 : CollatzResearch.WordTrace tailWord_1057455 prefixEnd_1057455 180994228500088478716453 := by
  unfold tailWord_1057455
  simp only [CollatzResearch.WordTrace]
  refine ⟨38568552384028608780893819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25712368256019072520595879 38568552384028608780893819)
  ·
    refine ⟨57852828576042913171340729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38568552384028608780893819 57852828576042913171340729)
    ·
      refine ⟨43389621432032184878505547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57852828576042913171340729 43389621432032184878505547)
      ·
        refine ⟨65084432148048277317758321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43389621432032184878505547 65084432148048277317758321)
        ·
          refine ⟨48813324111036207988318741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65084432148048277317758321 48813324111036207988318741)
          ·
            refine ⟨2288124567704822249452441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 48813324111036207988318741 2288124567704822249452441)
            ·
              refine ⟨1716093425778616687089331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2288124567704822249452441 1716093425778616687089331)
              ·
                refine ⟨2574140138667925030633997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1716093425778616687089331 2574140138667925030633997)
                ·
                  refine ⟨965302552000471886487749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2574140138667925030633997 965302552000471886487749)
                  ·
                    refine ⟨180994228500088478716453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 965302552000471886487749 180994228500088478716453)
                    ·
                      rfl

theorem cell23_1057455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 3, 4].length) (baseStart_1057455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057455 prefixEnd_1057455 := by exact prefixLift 1057455
  have htrace : WordTrace (prefixWord ++ tailWord_1057455) baseStart_1057455 baseEnd_1057455 := by
    simpa [prefixWord, tailWord_1057455, baseEnd_1057455] using wordTrace_append hprefix tailTrace_1057455
  have hstable : (prefixWord ++ tailWord_1057455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057455).length < 2 ^ (prefixWord ++ tailWord_1057455).sum := by decide
  have hdescent : baseEnd_1057455 < baseStart_1057455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057481 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 4, 9]
def baseStart_1057481 : Nat := 118140960795 + 1057481 * 2 ^ 59
def prefixEnd_1057481 : Nat := 4983230072969 + 3 ^ 40 * 1057481 * 2
def baseEnd_1057481 : Nat := 180998678665760778141413

theorem tailTrace_1057481 : CollatzResearch.WordTrace tailWord_1057481 prefixEnd_1057481 180998678665760778141413 := by
  unfold tailWord_1057481
  simp only [CollatzResearch.WordTrace]
  refine ⟨38569500681934415221340297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25713000454622943480893531 38569500681934415221340297)
  ·
    refine ⟨28927125511450811416005223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38569500681934415221340297 28927125511450811416005223)
    ·
      refine ⟨43390688267176217124007835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28927125511450811416005223 43390688267176217124007835)
      ·
        refine ⟨65086032400764325686011753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43390688267176217124007835 65086032400764325686011753)
        ·
          refine ⟨48814524300573244264508815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65086032400764325686011753 48814524300573244264508815)
          ·
            refine ⟨73221786450859866396763223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48814524300573244264508815 73221786450859866396763223)
            ·
              refine ⟨109832679676289799595144835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73221786450859866396763223 109832679676289799595144835)
              ·
                refine ⟨164749019514434699392717253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109832679676289799595144835 164749019514434699392717253)
                ·
                  refine ⟨30890441158956506136134485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 164749019514434699392717253 30890441158956506136134485)
                  ·
                    refine ⟨180998678665760778141413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 30890441158956506136134485 180998678665760778141413)
                    ·
                      rfl

theorem cell23_1057481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 9].length) (baseStart_1057481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057481 prefixEnd_1057481 := by exact prefixLift 1057481
  have htrace : WordTrace (prefixWord ++ tailWord_1057481) baseStart_1057481 baseEnd_1057481 := by
    simpa [prefixWord, tailWord_1057481, baseEnd_1057481] using wordTrace_append hprefix tailTrace_1057481
  have hstable : (prefixWord ++ tailWord_1057481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057481).length < 2 ^ (prefixWord ++ tailWord_1057481).sum := by decide
  have hdescent : baseEnd_1057481 < baseStart_1057481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057528 : List Nat := [2, 1, 2, 1, 1, 2, 4, 3, 1, 6]
def baseStart_1057528 : Nat := 118140960795 + 1057528 * 2 ^ 59
def prefixEnd_1057528 : Nat := 4983230072969 + 3 ^ 40 * 1057528 * 2
def baseEnd_1057528 : Nat := 181006723196014550178841

theorem tailTrace_1057528 : CollatzResearch.WordTrace tailWord_1057528 prefixEnd_1057528 181006723196014550178841 := by
  unfold tailWord_1057528
  simp only [CollatzResearch.WordTrace]
  refine ⟨19285607456382071124150619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25714143275176094832200825 19285607456382071124150619)
  ·
    refine ⟨28928411184573106686225929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19285607456382071124150619 28928411184573106686225929)
    ·
      refine ⟨21696308388429830014669447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28928411184573106686225929 21696308388429830014669447)
      ·
        refine ⟨32544462582644745022004171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21696308388429830014669447 32544462582644745022004171)
        ·
          refine ⟨48816693873967117533006257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32544462582644745022004171 48816693873967117533006257)
          ·
            refine ⟨36612520405475338149754693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48816693873967117533006257 36612520405475338149754693)
            ·
              refine ⟨6864847576026625903079005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36612520405475338149754693 6864847576026625903079005)
              ·
                refine ⟨2574317841009984713654627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6864847576026625903079005 2574317841009984713654627)
                ·
                  refine ⟨3861476761514977070481941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2574317841009984713654627 3861476761514977070481941)
                  ·
                    refine ⟨181006723196014550178841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3861476761514977070481941 181006723196014550178841)
                    ·
                      rfl

theorem cell23_1057528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 1, 6].length) (baseStart_1057528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057528 prefixEnd_1057528 := by exact prefixLift 1057528
  have htrace : WordTrace (prefixWord ++ tailWord_1057528) baseStart_1057528 baseEnd_1057528 := by
    simpa [prefixWord, tailWord_1057528, baseEnd_1057528] using wordTrace_append hprefix tailTrace_1057528
  have hstable : (prefixWord ++ tailWord_1057528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057528).length < 2 ^ (prefixWord ++ tailWord_1057528).sum := by decide
  have hdescent : baseEnd_1057528 < baseStart_1057528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057532 : List Nat := [2, 2, 2, 1, 3, 4, 1, 2, 1, 5]
def baseStart_1057532 : Nat := 118140960795 + 1057532 * 2 ^ 59
def prefixEnd_1057532 : Nat := 4983230072969 + 3 ^ 40 * 1057532 * 2
def baseEnd_1057532 : Nat := 181007407836887211628835

theorem tailTrace_1057532 : CollatzResearch.WordTrace tailWord_1057532 prefixEnd_1057532 181007407836887211628835 := by
  unfold tailWord_1057532
  simp only [CollatzResearch.WordTrace]
  refine ⟨19285680402374825465723425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25714240536499767287631233 19285680402374825465723425)
  ·
    refine ⟨14464260301781119099292569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19285680402374825465723425 14464260301781119099292569)
    ·
      refine ⟨10848195226335839324469427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14464260301781119099292569 10848195226335839324469427)
      ·
        refine ⟨16272292839503758986704141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10848195226335839324469427 16272292839503758986704141)
        ·
          refine ⟨6102109814813909620014053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16272292839503758986704141 6102109814813909620014053)
          ·
            refine ⟨1144145590277608053752635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6102109814813909620014053 1144145590277608053752635)
            ·
              refine ⟨1716218385416412080628953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1144145590277608053752635 1716218385416412080628953)
              ·
                refine ⟨1287163789062309060471715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1716218385416412080628953 1287163789062309060471715)
                ·
                  refine ⟨1930745683593463590707573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1287163789062309060471715 1930745683593463590707573)
                  ·
                    refine ⟨181007407836887211628835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1930745683593463590707573 181007407836887211628835)
                    ·
                      rfl

theorem cell23_1057532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_1057532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057532 prefixEnd_1057532 := by exact prefixLift 1057532
  have htrace : WordTrace (prefixWord ++ tailWord_1057532) baseStart_1057532 baseEnd_1057532 := by
    simpa [prefixWord, tailWord_1057532, baseEnd_1057532] using wordTrace_append hprefix tailTrace_1057532
  have hstable : (prefixWord ++ tailWord_1057532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057532).length < 2 ^ (prefixWord ++ tailWord_1057532).sum := by decide
  have hdescent : baseEnd_1057532 < baseStart_1057532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057562 : List Nat := [3, 1, 1, 3, 2, 1, 4, 2, 2, 4]
def baseStart_1057562 : Nat := 118140960795 + 1057562 * 2 ^ 59
def prefixEnd_1057562 : Nat := 4983230072969 + 3 ^ 40 * 1057562 * 2
def baseEnd_1057562 : Nat := 181012542643432172503789

theorem tailTrace_1057562 : CollatzResearch.WordTrace tailWord_1057562 prefixEnd_1057562 181012542643432172503789 := by
  unfold tailWord_1057562
  simp only [CollatzResearch.WordTrace]
  refine ⟨9643113748660241513759735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25714969996427310703359293 9643113748660241513759735)
  ·
    refine ⟨14464670622990362270639603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9643113748660241513759735 14464670622990362270639603)
    ·
      refine ⟨21697005934485543405959405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14464670622990362270639603 21697005934485543405959405)
      ·
        refine ⟨8136377225432078777234777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21697005934485543405959405 8136377225432078777234777)
        ·
          refine ⟨6102282919074059082926083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8136377225432078777234777 6102282919074059082926083)
          ·
            refine ⟨9153424378611088624389125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6102282919074059082926083 9153424378611088624389125)
            ·
              refine ⟨1716267070989579117072961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9153424378611088624389125 1716267070989579117072961)
              ·
                refine ⟨1287200303242184337804721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1716267070989579117072961 1287200303242184337804721)
                ·
                  refine ⟨965400227431638253353541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1287200303242184337804721 965400227431638253353541)
                  ·
                    refine ⟨181012542643432172503789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 965400227431638253353541 181012542643432172503789)
                    ·
                      rfl

theorem cell23_1057562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 2, 4].length) (baseStart_1057562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057562 prefixEnd_1057562 := by exact prefixLift 1057562
  have htrace : WordTrace (prefixWord ++ tailWord_1057562) baseStart_1057562 baseEnd_1057562 := by
    simpa [prefixWord, tailWord_1057562, baseEnd_1057562] using wordTrace_append hprefix tailTrace_1057562
  have hstable : (prefixWord ++ tailWord_1057562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057562).length < 2 ^ (prefixWord ++ tailWord_1057562).sum := by decide
  have hdescent : baseEnd_1057562 < baseStart_1057562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057582 : List Nat := [4, 1, 3, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_1057582 : Nat := 118140960795 + 1057582 * 2 ^ 59
def prefixEnd_1057582 : Nat := 4983230072969 + 3 ^ 40 * 1057582 * 2
def baseEnd_1057582 : Nat := 543047897543386439261275

theorem tailTrace_1057582 : CollatzResearch.WordTrace tailWord_1057582 prefixEnd_1057582 543047897543386439261275 := by
  unfold tailWord_1057582
  simp only [CollatzResearch.WordTrace]
  refine ⟨4821648056821063683845875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25715456303045672980511333 4821648056821063683845875)
  ·
    refine ⟨7232472085231595525768813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4821648056821063683845875 7232472085231595525768813)
    ·
      refine ⟨2712177031961848322163305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7232472085231595525768813 2712177031961848322163305)
      ·
        refine ⟨2034132773971386241622479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2712177031961848322163305 2034132773971386241622479)
        ·
          refine ⟨3051199160957079362433719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2034132773971386241622479 3051199160957079362433719)
          ·
            refine ⟨4576798741435619043650579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3051199160957079362433719 4576798741435619043650579)
            ·
              refine ⟨6865198112153428565475869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4576798741435619043650579 6865198112153428565475869)
              ·
                refine ⟨2574449292057535712053451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6865198112153428565475869 2574449292057535712053451)
                ·
                  refine ⟨3861673938086303568080177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2574449292057535712053451 3861673938086303568080177)
                  ·
                    refine ⟨2896255453564727676060133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3861673938086303568080177 2896255453564727676060133)
                    ·
                      refine ⟨543047897543386439261275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2896255453564727676060133 543047897543386439261275)
                      ·
                        rfl

theorem cell23_1057582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_1057582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057582 prefixEnd_1057582 := by exact prefixLift 1057582
  have htrace : WordTrace (prefixWord ++ tailWord_1057582) baseStart_1057582 baseEnd_1057582 := by
    simpa [prefixWord, tailWord_1057582, baseEnd_1057582] using wordTrace_append hprefix tailTrace_1057582
  have hstable : (prefixWord ++ tailWord_1057582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057582).length < 2 ^ (prefixWord ++ tailWord_1057582).sum := by decide
  have hdescent : baseEnd_1057582 < baseStart_1057582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057613 : List Nat := [1, 6, 1, 2, 3, 1, 1, 2, 2, 4]
def baseStart_1057613 : Nat := 118140960795 + 1057613 * 2 ^ 59
def prefixEnd_1057613 : Nat := 4983230072969 + 3 ^ 40 * 1057613 * 2
def baseEnd_1057613 : Nat := 181021271814558605991211

theorem tailTrace_1057613 : CollatzResearch.WordTrace tailWord_1057613 prefixEnd_1057613 181021271814558605991211 := by
  unfold tailWord_1057613
  simp only [CollatzResearch.WordTrace]
  refine ⟨38574315117456201765145493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25716210078304134510096995 38574315117456201765145493)
  ·
    refine ⟨1808171021130759457741195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38574315117456201765145493 1808171021130759457741195)
    ·
      refine ⟨2712256531696139186611793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1808171021130759457741195 2712256531696139186611793)
      ·
        refine ⟨2034192398772104389958845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2712256531696139186611793 2034192398772104389958845)
        ·
          refine ⟨762822149539539146234567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2034192398772104389958845 762822149539539146234567)
          ·
            refine ⟨1144233224309308719351851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 762822149539539146234567 1144233224309308719351851)
            ·
              refine ⟨1716349836463963079027777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1144233224309308719351851 1716349836463963079027777)
              ·
                refine ⟨1287262377347972309270833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1716349836463963079027777 1287262377347972309270833)
                ·
                  refine ⟨965446783010979231953125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1287262377347972309270833 965446783010979231953125)
                  ·
                    refine ⟨181021271814558605991211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 965446783010979231953125 181021271814558605991211)
                    ·
                      rfl

theorem cell23_1057613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_1057613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057613 prefixEnd_1057613 := by exact prefixLift 1057613
  have htrace : WordTrace (prefixWord ++ tailWord_1057613) baseStart_1057613 baseEnd_1057613 := by
    simpa [prefixWord, tailWord_1057613, baseEnd_1057613] using wordTrace_append hprefix tailTrace_1057613
  have hstable : (prefixWord ++ tailWord_1057613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057613).length < 2 ^ (prefixWord ++ tailWord_1057613).sum := by decide
  have hdescent : baseEnd_1057613 < baseStart_1057613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057635 : List Nat := [1, 1, 1, 5, 3, 1, 2, 1, 2, 6]
def baseStart_1057635 : Nat := 118140960795 + 1057635 * 2 ^ 59
def prefixEnd_1057635 : Nat := 4983230072969 + 3 ^ 40 * 1057635 * 2
def baseEnd_1057635 : Nat := 181025037339358243966177

theorem tailTrace_1057635 : CollatzResearch.WordTrace tailWord_1057635 prefixEnd_1057635 181025037339358243966177 := by
  unfold tailWord_1057635
  simp only [CollatzResearch.WordTrace]
  refine ⟨38575117523376499522446359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25716745015584333014964239 38575117523376499522446359)
  ·
    refine ⟨57862676285064749283669539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38575117523376499522446359 57862676285064749283669539)
    ·
      refine ⟨86794014427597123925504309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57862676285064749283669539 86794014427597123925504309)
      ·
        refine ⟨8136938852587230368016029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86794014427597123925504309 8136938852587230368016029)
        ·
          refine ⟨3051352069720211388006011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8136938852587230368016029 3051352069720211388006011)
          ·
            refine ⟨4577028104580317082009017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3051352069720211388006011 4577028104580317082009017)
            ·
              refine ⟨3432771078435237811506763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4577028104580317082009017 3432771078435237811506763)
              ·
                refine ⟨5149156617652856717260145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3432771078435237811506763 5149156617652856717260145)
                ·
                  refine ⟨3861867463239642537945109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5149156617652856717260145 3861867463239642537945109)
                  ·
                    refine ⟨181025037339358243966177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3861867463239642537945109 181025037339358243966177)
                    ·
                      rfl

theorem cell23_1057635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 6].length) (baseStart_1057635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057635 prefixEnd_1057635 := by exact prefixLift 1057635
  have htrace : WordTrace (prefixWord ++ tailWord_1057635) baseStart_1057635 baseEnd_1057635 := by
    simpa [prefixWord, tailWord_1057635, baseEnd_1057635] using wordTrace_append hprefix tailTrace_1057635
  have hstable : (prefixWord ++ tailWord_1057635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057635).length < 2 ^ (prefixWord ++ tailWord_1057635).sum := by decide
  have hdescent : baseEnd_1057635 < baseStart_1057635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057636 : List Nat := [2, 3, 1, 1, 4, 2, 3, 1, 2, 1, 3]
def baseStart_1057636 : Nat := 118140960795 + 1057636 * 2 ^ 59
def prefixEnd_1057636 : Nat := 4983230072969 + 3 ^ 40 * 1057636 * 2
def baseEnd_1057636 : Nat := 543075625498729227986027

theorem tailTrace_1057636 : CollatzResearch.WordTrace tailWord_1057636 prefixEnd_1057636 543075625498729227986027 := by
  unfold tailWord_1057636
  simp only [CollatzResearch.WordTrace]
  refine ⟨19287576998186438346616381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25716769330915251128821841 19287576998186438346616381)
  ·
    refine ⟨7232841374319914379981143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19287576998186438346616381 7232841374319914379981143)
    ·
      refine ⟨10849262061479871569971715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7232841374319914379981143 10849262061479871569971715)
      ·
        refine ⟨16273893092219807354957573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10849262061479871569971715 16273893092219807354957573)
        ·
          refine ⟨3051354954791213879054545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16273893092219807354957573 3051354954791213879054545)
          ·
            refine ⟨2288516216093410409290909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3051354954791213879054545 2288516216093410409290909)
            ·
              refine ⟨858193581035028903484091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2288516216093410409290909 858193581035028903484091)
              ·
                refine ⟨1287290371552543355226137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 858193581035028903484091 1287290371552543355226137)
                ·
                  refine ⟨965467778664407516419603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1287290371552543355226137 965467778664407516419603)
                  ·
                    refine ⟨1448201667996611274629405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 965467778664407516419603 1448201667996611274629405)
                    ·
                      refine ⟨543075625498729227986027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1448201667996611274629405 543075625498729227986027)
                      ·
                        rfl

theorem cell23_1057636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 2, 1, 3].length) (baseStart_1057636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057636 prefixEnd_1057636 := by exact prefixLift 1057636
  have htrace : WordTrace (prefixWord ++ tailWord_1057636) baseStart_1057636 baseEnd_1057636 := by
    simpa [prefixWord, tailWord_1057636, baseEnd_1057636] using wordTrace_append hprefix tailTrace_1057636
  have hstable : (prefixWord ++ tailWord_1057636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057636).length < 2 ^ (prefixWord ++ tailWord_1057636).sum := by decide
  have hdescent : baseEnd_1057636 < baseStart_1057636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057645 : List Nat := [1, 5, 1, 1, 1, 1, 1, 4, 2, 1, 5]
def baseStart_1057645 : Nat := 118140960795 + 1057645 * 2 ^ 59
def prefixEnd_1057645 : Nat := 4983230072969 + 3 ^ 40 * 1057645 * 2
def baseEnd_1057645 : Nat := 543080246824619692773485

theorem tailTrace_1057645 : CollatzResearch.WordTrace tailWord_1057645 prefixEnd_1057645 543080246824619692773485 := by
  unfold tailWord_1057645
  simp only [CollatzResearch.WordTrace]
  refine ⟨38575482253340271230310389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25716988168893514153540259 38575482253340271230310389)
  ·
    refine ⟨3616451461250650427841599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38575482253340271230310389 3616451461250650427841599)
    ·
      refine ⟨5424677191875975641762399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3616451461250650427841599 5424677191875975641762399)
      ·
        refine ⟨8137015787813963462643599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5424677191875975641762399 8137015787813963462643599)
        ·
          refine ⟨12205523681720945193965399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8137015787813963462643599 12205523681720945193965399)
          ·
            refine ⟨18308285522581417790948099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12205523681720945193965399 18308285522581417790948099)
            ·
              refine ⟨27462428283872126686422149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18308285522581417790948099 27462428283872126686422149)
              ·
                refine ⟨5149205303226023753704153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27462428283872126686422149 5149205303226023753704153)
                ·
                  refine ⟨3861903977419517815278115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5149205303226023753704153 3861903977419517815278115)
                  ·
                    refine ⟨5792855966129276722917173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3861903977419517815278115 5792855966129276722917173)
                    ·
                      refine ⟨543080246824619692773485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5792855966129276722917173 543080246824619692773485)
                      ·
                        rfl

theorem cell23_1057645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_1057645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057645 prefixEnd_1057645 := by exact prefixLift 1057645
  have htrace : WordTrace (prefixWord ++ tailWord_1057645) baseStart_1057645 baseEnd_1057645 := by
    simpa [prefixWord, tailWord_1057645, baseEnd_1057645] using wordTrace_append hprefix tailTrace_1057645
  have hstable : (prefixWord ++ tailWord_1057645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057645).length < 2 ^ (prefixWord ++ tailWord_1057645).sum := by decide
  have hdescent : baseEnd_1057645 < baseStart_1057645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057675 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 4, 3, 3]
def baseStart_1057675 : Nat := 118140960795 + 1057675 * 2 ^ 59
def prefixEnd_1057675 : Nat := 4983230072969 + 3 ^ 40 * 1057675 * 2
def baseEnd_1057675 : Nat := 543095651244254575398347

theorem tailTrace_1057675 : CollatzResearch.WordTrace tailWord_1057675 prefixEnd_1057675 543095651244254575398347 := by
  unfold tailWord_1057675
  simp only [CollatzResearch.WordTrace]
  refine ⟨38576576443231586353902479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25717717628821057569268319 38576576443231586353902479)
  ·
    refine ⟨57864864664847379530853719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38576576443231586353902479 57864864664847379530853719)
    ·
      refine ⟨86797296997271069296280579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57864864664847379530853719 86797296997271069296280579)
      ·
        refine ⟨130195945495906603944420869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86797296997271069296280579 130195945495906603944420869)
        ·
          refine ⟨24411739780482488239578913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130195945495906603944420869 24411739780482488239578913)
          ·
            refine ⟨18308804835361866179684185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24411739780482488239578913 18308804835361866179684185)
            ·
              refine ⟨13731603626521399634763139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18308804835361866179684185 13731603626521399634763139)
              ·
                refine ⟨20597405439782099452144709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13731603626521399634763139 20597405439782099452144709)
                ·
                  refine ⟨3862013519959143647277133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20597405439782099452144709 3862013519959143647277133)
                  ·
                    refine ⟨1448255069984678867728925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3862013519959143647277133 1448255069984678867728925)
                    ·
                      refine ⟨543095651244254575398347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1448255069984678867728925 543095651244254575398347)
                      ·
                        rfl

theorem cell23_1057675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 3, 3].length) (baseStart_1057675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057675 prefixEnd_1057675 := by exact prefixLift 1057675
  have htrace : WordTrace (prefixWord ++ tailWord_1057675) baseStart_1057675 baseEnd_1057675 := by
    simpa [prefixWord, tailWord_1057675, baseEnd_1057675] using wordTrace_append hprefix tailTrace_1057675
  have hstable : (prefixWord ++ tailWord_1057675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057675).length < 2 ^ (prefixWord ++ tailWord_1057675).sum := by decide
  have hdescent : baseEnd_1057675 < baseStart_1057675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057759 : List Nat := [1, 1, 2, 3, 5, 1, 1, 2, 3, 4]
def baseStart_1057759 : Nat := 118140960795 + 1057759 * 2 ^ 59
def prefixEnd_1057759 : Nat := 4983230072969 + 3 ^ 40 * 1057759 * 2
def baseEnd_1057759 : Nat := 181046261206410748915987

theorem tailTrace_1057759 : CollatzResearch.WordTrace tailWord_1057759 prefixEnd_1057759 181046261206410748915987 := by
  unfold tailWord_1057759
  simp only [CollatzResearch.WordTrace]
  refine ⟨38579640174927268699960331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25719760116618179133306887 38579640174927268699960331)
  ·
    refine ⟨57869460262390903049940497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38579640174927268699960331 57869460262390903049940497)
    ·
      refine ⟨43402095196793177287455373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57869460262390903049940497 43402095196793177287455373)
      ·
        refine ⟨16275785698797441482795765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43402095196793177287455373 16275785698797441482795765)
        ·
          refine ⟨1525854909262260139012103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16275785698797441482795765 1525854909262260139012103)
          ·
            refine ⟨2288782363893390208518155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1525854909262260139012103 2288782363893390208518155)
            ·
              refine ⟨3433173545840085312777233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2288782363893390208518155 3433173545840085312777233)
              ·
                refine ⟨2574880159380063984582925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3433173545840085312777233 2574880159380063984582925)
                ·
                  refine ⟨965580059767523994218597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2574880159380063984582925 965580059767523994218597)
                  ·
                    refine ⟨181046261206410748915987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 965580059767523994218597 181046261206410748915987)
                    ·
                      rfl

theorem cell23_1057759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 3, 4].length) (baseStart_1057759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057759 prefixEnd_1057759 := by exact prefixLift 1057759
  have htrace : WordTrace (prefixWord ++ tailWord_1057759) baseStart_1057759 baseEnd_1057759 := by
    simpa [prefixWord, tailWord_1057759, baseEnd_1057759] using wordTrace_append hprefix tailTrace_1057759
  have hstable : (prefixWord ++ tailWord_1057759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057759).length < 2 ^ (prefixWord ++ tailWord_1057759).sum := by decide
  have hdescent : baseEnd_1057759 < baseStart_1057759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057849 : List Nat := [1, 2, 1, 5, 2, 1, 2, 1, 4, 4]
def baseStart_1057849 : Nat := 118140960795 + 1057849 * 2 ^ 59
def prefixEnd_1057849 : Nat := 4983230072969 + 3 ^ 40 * 1057849 * 2
def baseEnd_1057849 : Nat := 181061665626045631540849

theorem tailTrace_1057849 : CollatzResearch.WordTrace tailWord_1057849 prefixEnd_1057849 181061665626045631540849 := by
  unfold tailWord_1057849
  simp only [CollatzResearch.WordTrace]
  refine ⟨38582922744601214070736601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25721948496400809380491067 38582922744601214070736601)
  ·
    refine ⟨28937192058450910553052451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38582922744601214070736601 28937192058450910553052451)
    ·
      refine ⟨43405788087676365829578677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28937192058450910553052451 43405788087676365829578677)
      ·
        refine ⟨4069292633219659296523001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43405788087676365829578677 4069292633219659296523001)
        ·
          refine ⟨3051969474914744472392251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4069292633219659296523001 3051969474914744472392251)
          ·
            refine ⟨4577954212372116708588377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3051969474914744472392251 4577954212372116708588377)
            ·
              refine ⟨3433465659279087531441283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4577954212372116708588377 3433465659279087531441283)
              ·
                refine ⟨5150198488918631297161925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3433465659279087531441283 5150198488918631297161925)
                ·
                  refine ⟨965662216672243368217861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5150198488918631297161925 965662216672243368217861)
                  ·
                    refine ⟨181061665626045631540849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 965662216672243368217861 181061665626045631540849)
                    ·
                      rfl

theorem cell23_1057849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 4, 4].length) (baseStart_1057849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057849 prefixEnd_1057849 := by exact prefixLift 1057849
  have htrace : WordTrace (prefixWord ++ tailWord_1057849) baseStart_1057849 baseEnd_1057849 := by
    simpa [prefixWord, tailWord_1057849, baseEnd_1057849] using wordTrace_append hprefix tailTrace_1057849
  have hstable : (prefixWord ++ tailWord_1057849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057849).length < 2 ^ (prefixWord ++ tailWord_1057849).sum := by decide
  have hdescent : baseEnd_1057849 < baseStart_1057849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057852 : List Nat := [2, 2, 2, 2, 2, 2, 1, 2, 1, 1, 6]
def baseStart_1057852 : Nat := 118140960795 + 1057852 * 2 ^ 59
def prefixEnd_1057852 : Nat := 4983230072969 + 3 ^ 40 * 1057852 * 2
def baseEnd_1057852 : Nat := 543186537320100382885033

theorem tailTrace_1057852 : CollatzResearch.WordTrace tailWord_1057852 prefixEnd_1057852 543186537320100382885033 := by
  unfold tailWord_1057852
  simp only [CollatzResearch.WordTrace]
  refine ⟨19291516081795172791547905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25722021442393563722063873 19291516081795172791547905)
  ·
    refine ⟨14468637061346379593660929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19291516081795172791547905 14468637061346379593660929)
    ·
      refine ⟨10851477796009784695245697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14468637061346379593660929 10851477796009784695245697)
      ·
        refine ⟨8138608347007338521434273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10851477796009784695245697 8138608347007338521434273)
        ·
          refine ⟨6103956260255503891075705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8138608347007338521434273 6103956260255503891075705)
          ·
            refine ⟨4577967195191627918306779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6103956260255503891075705 4577967195191627918306779)
            ·
              refine ⟨6866950792787441877460169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4577967195191627918306779 6866950792787441877460169)
              ·
                refine ⟨5150213094590581408095127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6866950792787441877460169 5150213094590581408095127)
                ·
                  refine ⟨7725319641885872112142691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5150213094590581408095127 7725319641885872112142691)
                  ·
                    refine ⟨11587979462828808168214037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7725319641885872112142691 11587979462828808168214037)
                    ·
                      refine ⟨543186537320100382885033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11587979462828808168214037 543186537320100382885033)
                      ·
                        rfl

theorem cell23_1057852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_1057852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057852 prefixEnd_1057852 := by exact prefixLift 1057852
  have htrace : WordTrace (prefixWord ++ tailWord_1057852) baseStart_1057852 baseEnd_1057852 := by
    simpa [prefixWord, tailWord_1057852, baseEnd_1057852] using wordTrace_append hprefix tailTrace_1057852
  have hstable : (prefixWord ++ tailWord_1057852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057852).length < 2 ^ (prefixWord ++ tailWord_1057852).sum := by decide
  have hdescent : baseEnd_1057852 < baseStart_1057852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057866 : List Nat := [3, 1, 2, 1, 1, 2, 6, 1, 2, 4]
def baseStart_1057866 : Nat := 118140960795 + 1057866 * 2 ^ 59
def prefixEnd_1057866 : Nat := 4983230072969 + 3 ^ 40 * 1057866 * 2
def baseEnd_1057866 : Nat := 181064575349754442703323

theorem tailTrace_1057866 : CollatzResearch.WordTrace tailWord_1057866 prefixEnd_1057866 181064575349754442703323 := by
  unfold tailWord_1057866
  simp only [CollatzResearch.WordTrace]
  refine ⟨9645885696384906493526363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25722361857026417316070301 9645885696384906493526363)
  ·
    refine ⟨14468828544577359740289545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9645885696384906493526363 14468828544577359740289545)
    ·
      refine ⟨10851621408433019805217159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14468828544577359740289545 10851621408433019805217159)
      ·
        refine ⟨16277432112649529707825739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10851621408433019805217159 16277432112649529707825739)
        ·
          refine ⟨24416148168974294561738609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16277432112649529707825739 24416148168974294561738609)
          ·
            refine ⟨18312111126730720921303957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24416148168974294561738609 18312111126730720921303957)
            ·
              refine ⟨858380209065502543186123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18312111126730720921303957 858380209065502543186123)
              ·
                refine ⟨1287570313598253814779185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 858380209065502543186123 1287570313598253814779185)
                ·
                  refine ⟨965677735198690361084389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1287570313598253814779185 965677735198690361084389)
                  ·
                    refine ⟨181064575349754442703323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 965677735198690361084389 181064575349754442703323)
                    ·
                      rfl

theorem cell23_1057866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_1057866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057866 prefixEnd_1057866 := by exact prefixLift 1057866
  have htrace : WordTrace (prefixWord ++ tailWord_1057866) baseStart_1057866 baseEnd_1057866 := by
    simpa [prefixWord, tailWord_1057866, baseEnd_1057866] using wordTrace_append hprefix tailTrace_1057866
  have hstable : (prefixWord ++ tailWord_1057866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057866).length < 2 ^ (prefixWord ++ tailWord_1057866).sum := by decide
  have hdescent : baseEnd_1057866 < baseStart_1057866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057869 : List Nat := [1, 6, 1, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_1057869 : Nat := 118140960795 + 1057869 * 2 ^ 59
def prefixEnd_1057869 : Nat := 4983230072969 + 3 ^ 40 * 1057869 * 2
def baseEnd_1057869 : Nat := 543195266491226816372455

theorem tailTrace_1057869 : CollatzResearch.WordTrace tailWord_1057869 prefixEnd_1057869 543195266491226816372455 := by
  unfold tailWord_1057869
  simp only [CollatzResearch.WordTrace]
  refine ⟨38583652204528757486464661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25722434803019171657643107 38583652204528757486464661)
  ·
    refine ⟨1808608697087285507178031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38583652204528757486464661 1808608697087285507178031)
    ·
      refine ⟨2712913045630928260767047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1808608697087285507178031 2712913045630928260767047)
      ·
        refine ⟨4069369568446392391150571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2712913045630928260767047 4069369568446392391150571)
        ·
          refine ⟨6104054352669588586725857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4069369568446392391150571 6104054352669588586725857)
          ·
            refine ⟨4578040764502191440044393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6104054352669588586725857 4578040764502191440044393)
            ·
              refine ⟨3433530573376643580033295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4578040764502191440044393 3433530573376643580033295)
              ·
                refine ⟨5150295860064965370049943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3433530573376643580033295 5150295860064965370049943)
                ·
                  refine ⟨7725443790097448055074915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5150295860064965370049943 7725443790097448055074915)
                  ·
                    refine ⟨11588165685146172082612373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7725443790097448055074915 11588165685146172082612373)
                    ·
                      refine ⟨543195266491226816372455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11588165685146172082612373 543195266491226816372455)
                      ·
                        rfl

theorem cell23_1057869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_1057869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057869 prefixEnd_1057869 := by exact prefixLift 1057869
  have htrace : WordTrace (prefixWord ++ tailWord_1057869) baseStart_1057869 baseEnd_1057869 := by
    simpa [prefixWord, tailWord_1057869, baseEnd_1057869] using wordTrace_append hprefix tailTrace_1057869
  have hstable : (prefixWord ++ tailWord_1057869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057869).length < 2 ^ (prefixWord ++ tailWord_1057869).sum := by decide
  have hdescent : baseEnd_1057869 < baseStart_1057869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057872 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 3]
def baseStart_1057872 : Nat := 118140960795 + 1057872 * 2 ^ 59
def prefixEnd_1057872 : Nat := 4983230072969 + 3 ^ 40 * 1057872 * 2
def baseEnd_1057872 : Nat := 543196806933190304634941

theorem tailTrace_1057872 : CollatzResearch.WordTrace tailWord_1057872 prefixEnd_1057872 543196806933190304634941 := by
  unfold tailWord_1057872
  simp only [CollatzResearch.WordTrace]
  refine ⟨19291880811758944499411935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25722507749011925999215913 19291880811758944499411935)
  ·
    refine ⟨28937821217638416749117903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19291880811758944499411935 28937821217638416749117903)
    ·
      refine ⟨43406731826457625123676855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28937821217638416749117903 43406731826457625123676855)
      ·
        refine ⟨65110097739686437685515283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43406731826457625123676855 65110097739686437685515283)
        ·
          refine ⟨97665146609529656528272925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65110097739686437685515283 97665146609529656528272925)
          ·
            refine ⟨36624429978573621198102347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97665146609529656528272925 36624429978573621198102347)
            ·
              refine ⟨54936644967860431797153521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36624429978573621198102347 54936644967860431797153521)
              ·
                refine ⟨41202483725895323847865141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54936644967860431797153521 41202483725895323847865141)
                ·
                  refine ⟨3862732849302686610737357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41202483725895323847865141 3862732849302686610737357)
                  ·
                    refine ⟨1448524818488507479026509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3862732849302686610737357 1448524818488507479026509)
                    ·
                      refine ⟨543196806933190304634941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1448524818488507479026509 543196806933190304634941)
                      ·
                        rfl

theorem cell23_1057872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 3].length) (baseStart_1057872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057872 prefixEnd_1057872 := by exact prefixLift 1057872
  have htrace : WordTrace (prefixWord ++ tailWord_1057872) baseStart_1057872 baseEnd_1057872 := by
    simpa [prefixWord, tailWord_1057872, baseEnd_1057872] using wordTrace_append hprefix tailTrace_1057872
  have hstable : (prefixWord ++ tailWord_1057872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057872).length < 2 ^ (prefixWord ++ tailWord_1057872).sum := by decide
  have hdescent : baseEnd_1057872 < baseStart_1057872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057876 : List Nat := [2, 4, 1, 1, 1, 1, 5, 2, 1, 2, 3]
def baseStart_1057876 : Nat := 118140960795 + 1057876 * 2 ^ 59
def prefixEnd_1057876 : Nat := 4983230072969 + 3 ^ 40 * 1057876 * 2
def baseEnd_1057876 : Nat := 543198860855808288984923

theorem tailTrace_1057876 : CollatzResearch.WordTrace tailWord_1057876 prefixEnd_1057876 543198860855808288984923 := by
  unfold tailWord_1057876
  simp only [CollatzResearch.WordTrace]
  refine ⟨19291953757751698840984741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25722605010335598454646321 19291953757751698840984741)
  ·
    refine ⟨3617241329578443532684639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19291953757751698840984741 3617241329578443532684639)
    ·
      refine ⟨5425861994367665299026959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3617241329578443532684639 5425861994367665299026959)
      ·
        refine ⟨8138792991551497948540439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5425861994367665299026959 8138792991551497948540439)
        ·
          refine ⟨12208189487327246922810659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8138792991551497948540439 12208189487327246922810659)
          ·
            refine ⟨18312284230990870384215989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12208189487327246922810659 18312284230990870384215989)
            ·
              refine ⟨1716776646655394098520249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18312284230990870384215989 1716776646655394098520249)
              ·
                refine ⟨1287582484991545573890187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1716776646655394098520249 1287582484991545573890187)
                ·
                  refine ⟨1931373727487318360835281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1287582484991545573890187 1931373727487318360835281)
                  ·
                    refine ⟨1448530295615488770626461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1931373727487318360835281 1448530295615488770626461)
                    ·
                      refine ⟨543198860855808288984923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1448530295615488770626461 543198860855808288984923)
                      ·
                        rfl

theorem cell23_1057876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_1057876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057876 prefixEnd_1057876 := by exact prefixLift 1057876
  have htrace : WordTrace (prefixWord ++ tailWord_1057876) baseStart_1057876 baseEnd_1057876 := by
    simpa [prefixWord, tailWord_1057876, baseEnd_1057876] using wordTrace_append hprefix tailTrace_1057876
  have hstable : (prefixWord ++ tailWord_1057876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057876).length < 2 ^ (prefixWord ++ tailWord_1057876).sum := by decide
  have hdescent : baseEnd_1057876 < baseStart_1057876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057889 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 6, 1, 3]
def baseStart_1057889 : Nat := 118140960795 + 1057889 * 2 ^ 59
def prefixEnd_1057889 : Nat := 4983230072969 + 3 ^ 40 * 1057889 * 2
def baseEnd_1057889 : Nat := 543205536104316738122363

theorem tailTrace_1057889 : CollatzResearch.WordTrace tailWord_1057889 prefixEnd_1057889 543205536104316738122363 := by
  unfold tailWord_1057889
  simp only [CollatzResearch.WordTrace]
  refine ⟨38584381664456300902192721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25722921109637533934795147 38584381664456300902192721)
  ·
    refine ⟨28938286248342225676644541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38584381664456300902192721 28938286248342225676644541)
    ·
      refine ⟨10851857343128334628741703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28938286248342225676644541 10851857343128334628741703)
      ·
        refine ⟨16277786014692501943112555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10851857343128334628741703 16277786014692501943112555)
        ·
          refine ⟨24416679022038752914668833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16277786014692501943112555 24416679022038752914668833)
          ·
            refine ⟨18312509266529064686001625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24416679022038752914668833 18312509266529064686001625)
            ·
              refine ⟨13734381949896798514501219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18312509266529064686001625 13734381949896798514501219)
              ·
                refine ⟨20601572924845197771751829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13734381949896798514501219 20601572924845197771751829)
                ·
                  refine ⟨965698730852118645550867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20601572924845197771751829 965698730852118645550867)
                  ·
                    refine ⟨1448548096278177968326301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 965698730852118645550867 1448548096278177968326301)
                    ·
                      refine ⟨543205536104316738122363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1448548096278177968326301 543205536104316738122363)
                      ·
                        rfl

theorem cell23_1057889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_1057889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057889 prefixEnd_1057889 := by exact prefixLift 1057889
  have htrace : WordTrace (prefixWord ++ tailWord_1057889) baseStart_1057889 baseEnd_1057889 := by
    simpa [prefixWord, tailWord_1057889, baseEnd_1057889] using wordTrace_append hprefix tailTrace_1057889
  have hstable : (prefixWord ++ tailWord_1057889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057889).length < 2 ^ (prefixWord ++ tailWord_1057889).sum := by decide
  have hdescent : baseEnd_1057889 < baseStart_1057889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057912 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 2, 3, 4]
def baseStart_1057912 : Nat := 118140960795 + 1057912 * 2 ^ 59
def prefixEnd_1057912 : Nat := 4983230072969 + 3 ^ 40 * 1057912 * 2
def baseEnd_1057912 : Nat := 543217346159370148134757

theorem tailTrace_1057912 : CollatzResearch.WordTrace tailWord_1057912 prefixEnd_1057912 543217346159370148134757 := by
  unfold tailWord_1057912
  simp only [CollatzResearch.WordTrace]
  refine ⟨19292610271686487915139995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25723480362248650553519993 19292610271686487915139995)
  ·
    refine ⟨28938915407529731872709993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19292610271686487915139995 28938915407529731872709993)
    ·
      refine ⟨21704186555647298904532495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28938915407529731872709993 21704186555647298904532495)
      ·
        refine ⟨32556279833470948356798743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21704186555647298904532495 32556279833470948356798743)
        ·
          refine ⟨48834419750206422535198115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32556279833470948356798743 48834419750206422535198115)
          ·
            refine ⟨73251629625309633802797173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48834419750206422535198115 73251629625309633802797173)
            ·
              refine ⟨6867340277372778169012235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 73251629625309633802797173 6867340277372778169012235)
              ·
                refine ⟨10301010416059167253518353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6867340277372778169012235 10301010416059167253518353)
                ·
                  refine ⟨7725757812044375440138765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10301010416059167253518353 7725757812044375440138765)
                  ·
                    refine ⟨2897159179516640790052037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7725757812044375440138765 2897159179516640790052037)
                    ·
                      refine ⟨543217346159370148134757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2897159179516640790052037 543217346159370148134757)
                      ·
                        rfl

theorem cell23_1057912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_1057912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057912 prefixEnd_1057912 := by exact prefixLift 1057912
  have htrace : WordTrace (prefixWord ++ tailWord_1057912) baseStart_1057912 baseEnd_1057912 := by
    simpa [prefixWord, tailWord_1057912, baseEnd_1057912] using wordTrace_append hprefix tailTrace_1057912
  have hstable : (prefixWord ++ tailWord_1057912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057912).length < 2 ^ (prefixWord ++ tailWord_1057912).sum := by decide
  have hdescent : baseEnd_1057912 < baseStart_1057912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057932 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 4, 1, 5]
def baseStart_1057932 : Nat := 118140960795 + 1057932 * 2 ^ 59
def prefixEnd_1057932 : Nat := 4983230072969 + 3 ^ 40 * 1057932 * 2
def baseEnd_1057932 : Nat := 543227615772460069884665

theorem tailTrace_1057932 : CollatzResearch.WordTrace tailWord_1057932 prefixEnd_1057932 543227615772460069884665 := by
  unfold tailWord_1057932
  simp only [CollatzResearch.WordTrace]
  refine ⟨19292975001650259623004025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25723966668867012830672033 19292975001650259623004025)
  ·
    refine ⟨14469731251237694717253019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19292975001650259623004025 14469731251237694717253019)
    ·
      refine ⟨21704596876856542075879529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14469731251237694717253019 21704596876856542075879529)
      ·
        refine ⟨16278447657642406556909647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21704596876856542075879529 16278447657642406556909647)
        ·
          refine ⟨24417671486463609835364471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16278447657642406556909647 24417671486463609835364471)
          ·
            refine ⟨36626507229695414753046707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24417671486463609835364471 36626507229695414753046707)
            ·
              refine ⟨54939760844543122129570061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36626507229695414753046707 54939760844543122129570061)
              ·
                refine ⟨20602410316703670798588773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54939760844543122129570061 20602410316703670798588773)
                ·
                  refine ⟨3862951934381938274735395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20602410316703670798588773 3862951934381938274735395)
                  ·
                    refine ⟨5794427901572907412103093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3862951934381938274735395 5794427901572907412103093)
                    ·
                      refine ⟨543227615772460069884665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5794427901572907412103093 543227615772460069884665)
                      ·
                        rfl

theorem cell23_1057932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_1057932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057932 prefixEnd_1057932 := by exact prefixLift 1057932
  have htrace : WordTrace (prefixWord ++ tailWord_1057932) baseStart_1057932 baseEnd_1057932 := by
    simpa [prefixWord, tailWord_1057932, baseEnd_1057932] using wordTrace_append hprefix tailTrace_1057932
  have hstable : (prefixWord ++ tailWord_1057932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057932).length < 2 ^ (prefixWord ++ tailWord_1057932).sum := by decide
  have hdescent : baseEnd_1057932 < baseStart_1057932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057950 : List Nat := [4, 3, 1, 1, 2, 2, 1, 3, 1, 3, 2]
def baseStart_1057950 : Nat := 118140960795 + 1057950 * 2 ^ 59
def prefixEnd_1057950 : Nat := 4983230072969 + 3 ^ 40 * 1057950 * 2
def baseEnd_1057950 : Nat := 543236858424240999459583

theorem tailTrace_1057950 : CollatzResearch.WordTrace tailWord_1057950 prefixEnd_1057950 543236858424240999459583 := by
  unfold tailWord_1057950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4823325814654413540020413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25724404344823538880108869 4823325814654413540020413)
  ·
    refine ⟨1808747180495405077507655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4823325814654413540020413 1808747180495405077507655)
    ·
      refine ⟨2713120770743107616261483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1808747180495405077507655 2713120770743107616261483)
      ·
        refine ⟨4069681156114661424392225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2713120770743107616261483 4069681156114661424392225)
        ·
          refine ⟨3052260867085996068294169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4069681156114661424392225 3052260867085996068294169)
          ·
            refine ⟨2289195650314497051220627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3052260867085996068294169 2289195650314497051220627)
            ·
              refine ⟨3433793475471745576830941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2289195650314497051220627 3433793475471745576830941)
              ·
                refine ⟨1287672553301904591311603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3433793475471745576830941 1287672553301904591311603)
                ·
                  refine ⟨1931508829952856886967405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1287672553301904591311603 1931508829952856886967405)
                  ·
                    refine ⟨724315811232321332612777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1931508829952856886967405 724315811232321332612777)
                    ·
                      refine ⟨543236858424240999459583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 724315811232321332612777 543236858424240999459583)
                      ·
                        rfl

theorem cell23_1057950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_1057950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057950 prefixEnd_1057950 := by exact prefixLift 1057950
  have htrace : WordTrace (prefixWord ++ tailWord_1057950) baseStart_1057950 baseEnd_1057950 := by
    simpa [prefixWord, tailWord_1057950, baseEnd_1057950] using wordTrace_append hprefix tailTrace_1057950
  have hstable : (prefixWord ++ tailWord_1057950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057950).length < 2 ^ (prefixWord ++ tailWord_1057950).sum := by decide
  have hdescent : baseEnd_1057950 < baseStart_1057950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057952 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 9]
def baseStart_1057952 : Nat := 118140960795 + 1057952 * 2 ^ 59
def prefixEnd_1057952 : Nat := 4983230072969 + 3 ^ 40 * 1057952 * 2
def baseEnd_1057952 : Nat := 60359765042838887959397

theorem tailTrace_1057952 : CollatzResearch.WordTrace tailWord_1057952 prefixEnd_1057952 60359765042838887959397 := by
  unfold tailWord_1057952
  simp only [CollatzResearch.WordTrace]
  refine ⟨19293339731614031330868055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25724452975485375107824073 19293339731614031330868055)
  ·
    refine ⟨28940009597421046996302083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19293339731614031330868055 28940009597421046996302083)
    ·
      refine ⟨43410014396131570494453125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28940009597421046996302083 43410014396131570494453125)
      ·
        refine ⟨8139377699274669467709961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43410014396131570494453125 8139377699274669467709961)
        ·
          refine ⟨6104533274456002100782471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8139377699274669467709961 6104533274456002100782471)
          ·
            refine ⟨9156799911684003151173707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6104533274456002100782471 9156799911684003151173707)
            ·
              refine ⟨13735199867526004726760561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9156799911684003151173707 13735199867526004726760561)
              ·
                refine ⟨10301399900644503545070421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13735199867526004726760561 10301399900644503545070421)
                ·
                  refine ⟨60359765042838887959397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10301399900644503545070421 60359765042838887959397)
                  ·
                    rfl

theorem cell23_1057952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 9].length) (baseStart_1057952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057952 prefixEnd_1057952 := by exact prefixLift 1057952
  have htrace : WordTrace (prefixWord ++ tailWord_1057952) baseStart_1057952 baseEnd_1057952 := by
    simpa [prefixWord, tailWord_1057952, baseEnd_1057952] using wordTrace_append hprefix tailTrace_1057952
  have hstable : (prefixWord ++ tailWord_1057952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057952).length < 2 ^ (prefixWord ++ tailWord_1057952).sum := by decide
  have hdescent : baseEnd_1057952 < baseStart_1057952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057969 : List Nat := [1, 2, 2, 5, 1, 1, 1, 3, 7]
def baseStart_1057969 : Nat := 118140960795 + 1057969 * 2 ^ 59
def prefixEnd_1057969 : Nat := 4983230072969 + 3 ^ 40 * 1057969 * 2
def baseEnd_1057969 : Nat := 60360734950741825013555

theorem tailTrace_1057969 : CollatzResearch.WordTrace tailWord_1057969 prefixEnd_1057969 60360734950741825013555 := by
  unfold tailWord_1057969
  simp only [CollatzResearch.WordTrace]
  refine ⟨38587299504166474565104961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25724866336110983043403307 38587299504166474565104961)
  ·
    refine ⟨28940474628124855923828721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38587299504166474565104961 28940474628124855923828721)
    ·
      refine ⟨21705355971093641942871541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28940474628124855923828721 21705355971093641942871541)
      ·
        refine ⟨2034877122290028932144207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21705355971093641942871541 2034877122290028932144207)
        ·
          refine ⟨3052315683435043398216311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2034877122290028932144207 3052315683435043398216311)
          ·
            refine ⟨4578473525152565097324467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3052315683435043398216311 4578473525152565097324467)
            ·
              refine ⟨6867710287728847645986701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4578473525152565097324467 6867710287728847645986701)
              ·
                refine ⟨2575391357898317867245013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6867710287728847645986701 2575391357898317867245013)
                ·
                  refine ⟨60360734950741825013555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2575391357898317867245013 60360734950741825013555)
                  ·
                    rfl

theorem cell23_1057969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 7].length) (baseStart_1057969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057969 prefixEnd_1057969 := by exact prefixLift 1057969
  have htrace : WordTrace (prefixWord ++ tailWord_1057969) baseStart_1057969 baseEnd_1057969 := by
    simpa [prefixWord, tailWord_1057969, baseEnd_1057969] using wordTrace_append hprefix tailTrace_1057969
  have hstable : (prefixWord ++ tailWord_1057969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057969).length < 2 ^ (prefixWord ++ tailWord_1057969).sum := by decide
  have hdescent : baseEnd_1057969 < baseStart_1057969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057974 : List Nat := [5, 1, 3, 2, 1, 1, 3, 1, 2, 1, 3]
def baseStart_1057974 : Nat := 118140960795 + 1057974 * 2 ^ 59
def prefixEnd_1057974 : Nat := 4983230072969 + 3 ^ 40 * 1057974 * 2
def baseEnd_1057974 : Nat := 543249181959948905559473

theorem tailTrace_1057974 : CollatzResearch.WordTrace tailWord_1057974 prefixEnd_1057974 543249181959948905559473 := by
  unfold tailWord_1057974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2411717616821772526189811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25724987912765573612691317 2411717616821772526189811)
  ·
    refine ⟨3617576425232658789284717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2411717616821772526189811 3617576425232658789284717)
    ·
      refine ⟨1356591159462247045981769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3617576425232658789284717 1356591159462247045981769)
      ·
        refine ⟨1017443369596685284486327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1356591159462247045981769 1017443369596685284486327)
        ·
          refine ⟨1526165054395027926729491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1017443369596685284486327 1526165054395027926729491)
          ·
            refine ⟨2289247581592541890094237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1526165054395027926729491 2289247581592541890094237)
            ·
              refine ⟨858467843097203208785339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2289247581592541890094237 858467843097203208785339)
              ·
                refine ⟨1287701764645804813178009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 858467843097203208785339 1287701764645804813178009)
                ·
                  refine ⟨965776323484353609883507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1287701764645804813178009 965776323484353609883507)
                  ·
                    refine ⟨1448664485226530414825261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 965776323484353609883507 1448664485226530414825261)
                    ·
                      refine ⟨543249181959948905559473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1448664485226530414825261 543249181959948905559473)
                      ·
                        rfl

theorem cell23_1057974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_1057974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1057974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1057974 prefixEnd_1057974 := by exact prefixLift 1057974
  have htrace : WordTrace (prefixWord ++ tailWord_1057974) baseStart_1057974 baseEnd_1057974 := by
    simpa [prefixWord, tailWord_1057974, baseEnd_1057974] using wordTrace_append hprefix tailTrace_1057974
  have hstable : (prefixWord ++ tailWord_1057974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057974).length < 2 ^ (prefixWord ++ tailWord_1057974).sum := by decide
  have hdescent : baseEnd_1057974 < baseStart_1057974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058080 : List Nat := [2, 1, 1, 5, 3, 1, 1, 4, 1, 4]
def baseStart_1058080 : Nat := 118140960795 + 1058080 * 2 ^ 59
def prefixEnd_1058080 : Nat := 4983230072969 + 3 ^ 40 * 1058080 * 2
def baseEnd_1058080 : Nat := 181101203636441830277995

theorem tailTrace_1058080 : CollatzResearch.WordTrace tailWord_1058080 prefixEnd_1058080 181101203636441830277995 := by
  unfold tailWord_1058080
  simp only [CollatzResearch.WordTrace]
  refine ⟨19295674003382170261197847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25727565337842893681597129 19295674003382170261197847)
  ·
    refine ⟨28943511005073255391796771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19295674003382170261197847 28943511005073255391796771)
    ·
      refine ⟨43415266507609883087695157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28943511005073255391796771 43415266507609883087695157)
      ·
        refine ⟨4070181235088426539471421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43415266507609883087695157 4070181235088426539471421)
        ·
          refine ⟨1526317963158159952301783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4070181235088426539471421 1526317963158159952301783)
          ·
            refine ⟨2289476944737239928452675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1526317963158159952301783 2289476944737239928452675)
            ·
              refine ⟨3434215417105859892679013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2289476944737239928452675 3434215417105859892679013)
              ·
                refine ⟨643915390707348729877315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3434215417105859892679013 643915390707348729877315)
                ·
                  refine ⟨965873086061023094815973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 643915390707348729877315 965873086061023094815973)
                  ·
                    refine ⟨181101203636441830277995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 965873086061023094815973 181101203636441830277995)
                    ·
                      rfl

theorem cell23_1058080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 4, 1, 4].length) (baseStart_1058080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058080 prefixEnd_1058080 := by exact prefixLift 1058080
  have htrace : WordTrace (prefixWord ++ tailWord_1058080) baseStart_1058080 baseEnd_1058080 := by
    simpa [prefixWord, tailWord_1058080, baseEnd_1058080] using wordTrace_append hprefix tailTrace_1058080
  have hstable : (prefixWord ++ tailWord_1058080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058080).length < 2 ^ (prefixWord ++ tailWord_1058080).sum := by decide
  have hdescent : baseEnd_1058080 < baseStart_1058080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058093 : List Nat := [1, 5, 3, 1, 1, 1, 2, 3, 6]
def baseStart_1058093 : Nat := 118140960795 + 1058093 * 2 ^ 59
def prefixEnd_1058093 : Nat := 4983230072969 + 3 ^ 40 * 1058093 * 2
def baseEnd_1058093 : Nat := 60367809573092659996825

theorem tailTrace_1058093 : CollatzResearch.WordTrace tailWord_1058093 prefixEnd_1058093 60367809573092659996825 := by
  unfold tailWord_1058093
  simp only [CollatzResearch.WordTrace]
  refine ⟨38591822155717243742618933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25727881437144829161745955 38591822155717243742618933)
  ·
    refine ⟨3617983327098491600870525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38591822155717243742618933 3617983327098491600870525)
    ·
      refine ⟨1356743747661934350326447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3617983327098491600870525 1356743747661934350326447)
      ·
        refine ⟨2035115621492901525489671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1356743747661934350326447 2035115621492901525489671)
        ·
          refine ⟨3052673432239352288234507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2035115621492901525489671 3052673432239352288234507)
          ·
            refine ⟨4579010148359028432351761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3052673432239352288234507 4579010148359028432351761)
            ·
              refine ⟨3434257611269271324263821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4579010148359028432351761 3434257611269271324263821)
              ·
                refine ⟨1287846604225976746598933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3434257611269271324263821 1287846604225976746598933)
                ·
                  refine ⟨60367809573092659996825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1287846604225976746598933 60367809573092659996825)
                  ·
                    rfl

theorem cell23_1058093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_1058093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058093 prefixEnd_1058093 := by exact prefixLift 1058093
  have htrace : WordTrace (prefixWord ++ tailWord_1058093) baseStart_1058093 baseEnd_1058093 := by
    simpa [prefixWord, tailWord_1058093, baseEnd_1058093] using wordTrace_append hprefix tailTrace_1058093
  have hstable : (prefixWord ++ tailWord_1058093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058093).length < 2 ^ (prefixWord ++ tailWord_1058093).sum := by decide
  have hdescent : baseEnd_1058093 < baseStart_1058093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058096 : List Nat := [2, 1, 1, 1, 2, 2, 4, 2, 1, 5, 2]
def baseStart_1058096 : Nat := 118140960795 + 1058096 * 2 ^ 59
def prefixEnd_1058096 : Nat := 4983230072969 + 3 ^ 40 * 1058096 * 2
def baseEnd_1058096 : Nat := 543311826599797428233911

theorem tailTrace_1058096 : CollatzResearch.WordTrace tailWord_1058096 prefixEnd_1058096 543311826599797428233911 := by
  unfold tailWord_1058096
  simp only [CollatzResearch.WordTrace]
  refine ⟨19295965787353187627489071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25727954383137583503318761 19295965787353187627489071)
  ·
    refine ⟨28943948681029781441233607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19295965787353187627489071 28943948681029781441233607)
    ·
      refine ⟨43415923021544672161850411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28943948681029781441233607 43415923021544672161850411)
      ·
        refine ⟨65123884532317008242775617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43415923021544672161850411 65123884532317008242775617)
        ·
          refine ⟨48842913399237756182081713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65123884532317008242775617 48842913399237756182081713)
          ·
            refine ⟨36632185049428317136561285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48842913399237756182081713 36632185049428317136561285)
            ·
              refine ⟨6868534696767809463105241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36632185049428317136561285 6868534696767809463105241)
              ·
                refine ⟨5151401022575857097328931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6868534696767809463105241 5151401022575857097328931)
                ·
                  refine ⟨7727101533863785645993397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5151401022575857097328931 7727101533863785645993397)
                  ·
                    refine ⟨724415768799729904311881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7727101533863785645993397 724415768799729904311881)
                    ·
                      refine ⟨543311826599797428233911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 724415768799729904311881 543311826599797428233911)
                      ·
                        rfl

theorem cell23_1058096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 1, 5, 2].length) (baseStart_1058096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058096 prefixEnd_1058096 := by exact prefixLift 1058096
  have htrace : WordTrace (prefixWord ++ tailWord_1058096) baseStart_1058096 baseEnd_1058096 := by
    simpa [prefixWord, tailWord_1058096, baseEnd_1058096] using wordTrace_append hprefix tailTrace_1058096
  have hstable : (prefixWord ++ tailWord_1058096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058096).length < 2 ^ (prefixWord ++ tailWord_1058096).sum := by decide
  have hdescent : baseEnd_1058096 < baseStart_1058096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058106 : List Nat := [3, 1, 1, 1, 4, 1, 2, 4, 1, 5]
def baseStart_1058106 : Nat := 118140960795 + 1058106 * 2 ^ 59
def prefixEnd_1058106 : Nat := 4983230072969 + 3 ^ 40 * 1058106 * 2
def baseEnd_1058106 : Nat := 181105653802114129702955

theorem tailTrace_1058106 : CollatzResearch.WordTrace tailWord_1058106 prefixEnd_1058106 181105653802114129702955 := by
  unfold tailWord_1058106
  simp only [CollatzResearch.WordTrace]
  refine ⟨9648074076167536740710543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25728197536446764641894781 9648074076167536740710543)
  ·
    refine ⟨14472111114251305111065815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9648074076167536740710543 14472111114251305111065815)
    ·
      refine ⟨21708166671376957666598723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14472111114251305111065815 21708166671376957666598723)
      ·
        refine ⟨32562250007065436499898085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21708166671376957666598723 32562250007065436499898085)
        ·
          refine ⟨6105421876324769343730891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32562250007065436499898085 6105421876324769343730891)
          ·
            refine ⟨9158132814487154015596337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6105421876324769343730891 9158132814487154015596337)
            ·
              refine ⟨6868599610865365511697253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9158132814487154015596337 6868599610865365511697253)
              ·
                refine ⟨1287862427037256033443235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6868599610865365511697253 1287862427037256033443235)
                ·
                  refine ⟨1931793640555884050164853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1287862427037256033443235 1931793640555884050164853)
                  ·
                    refine ⟨181105653802114129702955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1931793640555884050164853 181105653802114129702955)
                    ·
                      rfl

theorem cell23_1058106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 1, 5].length) (baseStart_1058106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058106 prefixEnd_1058106 := by exact prefixLift 1058106
  have htrace : WordTrace (prefixWord ++ tailWord_1058106) baseStart_1058106 baseEnd_1058106 := by
    simpa [prefixWord, tailWord_1058106, baseEnd_1058106] using wordTrace_append hprefix tailTrace_1058106
  have hstable : (prefixWord ++ tailWord_1058106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058106).length < 2 ^ (prefixWord ++ tailWord_1058106).sum := by decide
  have hdescent : baseEnd_1058106 < baseStart_1058106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058136 : List Nat := [2, 1, 2, 2, 1, 1, 5, 1, 4, 4]
def baseStart_1058136 : Nat := 118140960795 + 1058136 * 2 ^ 59
def prefixEnd_1058136 : Nat := 4983230072969 + 3 ^ 40 * 1058136 * 2
def baseEnd_1058136 : Nat := 181110788608659090577909

theorem tailTrace_1058136 : CollatzResearch.WordTrace tailWord_1058136 prefixEnd_1058136 181110788608659090577909 := by
  unfold tailWord_1058136
  simp only [CollatzResearch.WordTrace]
  refine ⟨19296695247280731043217131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25728926996374308057622841 19296695247280731043217131)
  ·
    refine ⟨28945042870921096564825697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19296695247280731043217131 28945042870921096564825697)
    ·
      refine ⟨21708782153190822423619273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28945042870921096564825697 21708782153190822423619273)
      ·
        refine ⟨16281586614893116817714455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21708782153190822423619273 16281586614893116817714455)
        ·
          refine ⟨24422379922339675226571683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16281586614893116817714455 24422379922339675226571683)
          ·
            refine ⟨36633569883509512839857525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24422379922339675226571683 36633569883509512839857525)
            ·
              refine ⟨3434397176579016828736643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36633569883509512839857525 3434397176579016828736643)
              ·
                refine ⟨5151595764868525243104965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3434397176579016828736643 5151595764868525243104965)
                ·
                  refine ⟨965924205912848483082181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5151595764868525243104965 965924205912848483082181)
                  ·
                    refine ⟨181110788608659090577909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 965924205912848483082181 181110788608659090577909)
                    ·
                      rfl

theorem cell23_1058136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 4, 4].length) (baseStart_1058136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058136 prefixEnd_1058136 := by exact prefixLift 1058136
  have htrace : WordTrace (prefixWord ++ tailWord_1058136) baseStart_1058136 baseEnd_1058136 := by
    simpa [prefixWord, tailWord_1058136, baseEnd_1058136] using wordTrace_append hprefix tailTrace_1058136
  have hstable : (prefixWord ++ tailWord_1058136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058136).length < 2 ^ (prefixWord ++ tailWord_1058136).sum := by decide
  have hdescent : baseEnd_1058136 < baseStart_1058136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058149 : List Nat := [1, 3, 1, 3, 1, 2, 2, 10]
def baseStart_1058149 : Nat := 118140960795 + 1058149 * 2 ^ 59
def prefixEnd_1058149 : Nat := 4983230072969 + 3 ^ 40 * 1058149 * 2
def baseEnd_1058149 : Nat := 20123668187943915587821

theorem tailTrace_1058149 : CollatzResearch.WordTrace tailWord_1058149 prefixEnd_1058149 20123668187943915587821 := by
  unfold tailWord_1058149
  simp only [CollatzResearch.WordTrace]
  refine ⟨38593864643514365306657501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25729243095676243537771667 38593864643514365306657501)
  ·
    refine ⟨14472699241317886989996563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38593864643514365306657501 14472699241317886989996563)
    ·
      refine ⟨21709048861976830484994845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14472699241317886989996563 21709048861976830484994845)
      ·
        refine ⟨8140893323241311431873067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21709048861976830484994845 8140893323241311431873067)
        ·
          refine ⟨12211339984861967147809601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8140893323241311431873067 12211339984861967147809601)
          ·
            refine ⟨9158504988646475360857201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12211339984861967147809601 9158504988646475360857201)
            ·
              refine ⟨6868878741484856520642901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9158504988646475360857201 6868878741484856520642901)
              ·
                refine ⟨20123668187943915587821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 6868878741484856520642901 20123668187943915587821)
                ·
                  rfl

theorem cell23_1058149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 10].length) (baseStart_1058149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058149 prefixEnd_1058149 := by exact prefixLift 1058149
  have htrace : WordTrace (prefixWord ++ tailWord_1058149) baseStart_1058149 baseEnd_1058149 := by
    simpa [prefixWord, tailWord_1058149, baseEnd_1058149] using wordTrace_append hprefix tailTrace_1058149
  have hstable : (prefixWord ++ tailWord_1058149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058149).length < 2 ^ (prefixWord ++ tailWord_1058149).sum := by decide
  have hdescent : baseEnd_1058149 < baseStart_1058149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058156 : List Nat := [2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 6]
def baseStart_1058156 : Nat := 118140960795 + 1058156 * 2 ^ 59
def prefixEnd_1058156 : Nat := 4983230072969 + 3 ^ 40 * 1058156 * 2
def baseEnd_1058156 : Nat := 543342635439067193483635

theorem tailTrace_1058156 : CollatzResearch.WordTrace tailWord_1058156 prefixEnd_1058156 543342635439067193483635 := by
  unfold tailWord_1058156
  simp only [CollatzResearch.WordTrace]
  refine ⟨19297059977244502751081161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25729413302992670334774881 19297059977244502751081161)
  ·
    refine ⟨14472794982933377063310871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19297059977244502751081161 14472794982933377063310871)
    ·
      refine ⟨21709192474400065594966307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14472794982933377063310871 21709192474400065594966307)
      ·
        refine ⟨32563788711600098392449461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21709192474400065594966307 32563788711600098392449461)
        ·
          refine ⟨3052855191712509224292137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32563788711600098392449461 3052855191712509224292137)
          ·
            refine ⟨2289641393784381918219103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3052855191712509224292137 2289641393784381918219103)
            ·
              refine ⟨3434462090676572877328655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2289641393784381918219103 3434462090676572877328655)
              ·
                refine ⟨5151693136014859315992983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3434462090676572877328655 5151693136014859315992983)
                ·
                  refine ⟨7727539704022288973989475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5151693136014859315992983 7727539704022288973989475)
                  ·
                    refine ⟨11591309556033433460984213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7727539704022288973989475 11591309556033433460984213)
                    ·
                      refine ⟨543342635439067193483635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11591309556033433460984213 543342635439067193483635)
                      ·
                        rfl

theorem cell23_1058156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_1058156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058156 prefixEnd_1058156 := by exact prefixLift 1058156
  have htrace : WordTrace (prefixWord ++ tailWord_1058156) baseStart_1058156 baseEnd_1058156 := by
    simpa [prefixWord, tailWord_1058156, baseEnd_1058156] using wordTrace_append hprefix tailTrace_1058156
  have hstable : (prefixWord ++ tailWord_1058156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058156).length < 2 ^ (prefixWord ++ tailWord_1058156).sum := by decide
  have hdescent : baseEnd_1058156 < baseStart_1058156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058176 : List Nat := [2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 3]
def baseStart_1058176 : Nat := 118140960795 + 1058176 * 2 ^ 59
def prefixEnd_1058176 : Nat := 4983230072969 + 3 ^ 40 * 1058176 * 2
def baseEnd_1058176 : Nat := 543352905052157115233543

theorem tailTrace_1058176 : CollatzResearch.WordTrace tailWord_1058176 prefixEnd_1058176 543352905052157115233543 := by
  unfold tailWord_1058176
  simp only [CollatzResearch.WordTrace]
  refine ⟨19297424707208274458945191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25729899609611032611926921 19297424707208274458945191)
  ·
    refine ⟨28946137060812411688417787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19297424707208274458945191 28946137060812411688417787)
    ·
      refine ⟨43419205591218617532626681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28946137060812411688417787 43419205591218617532626681)
      ·
        refine ⟨32564404193413963149470011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43419205591218617532626681 32564404193413963149470011)
        ·
          refine ⟨48846606290120944724205017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32564404193413963149470011 48846606290120944724205017)
          ·
            refine ⟨36634954717590708543153763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48846606290120944724205017 36634954717590708543153763)
            ·
              refine ⟨54952432076386062814730645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36634954717590708543153763 54952432076386062814730645)
              ·
                refine ⟨2575895253580596694440499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54952432076386062814730645 2575895253580596694440499)
                ·
                  refine ⟨3863842880370895041660749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2575895253580596694440499 3863842880370895041660749)
                  ·
                    refine ⟨1448941080139085640622781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3863842880370895041660749 1448941080139085640622781)
                    ·
                      refine ⟨543352905052157115233543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1448941080139085640622781 543352905052157115233543)
                      ·
                        rfl

theorem cell23_1058176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 3].length) (baseStart_1058176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058176 prefixEnd_1058176 := by exact prefixLift 1058176
  have htrace : WordTrace (prefixWord ++ tailWord_1058176) baseStart_1058176 baseEnd_1058176 := by
    simpa [prefixWord, tailWord_1058176, baseEnd_1058176] using wordTrace_append hprefix tailTrace_1058176
  have hstable : (prefixWord ++ tailWord_1058176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058176).length < 2 ^ (prefixWord ++ tailWord_1058176).sum := by decide
  have hdescent : baseEnd_1058176 < baseStart_1058176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058204 : List Nat := [2, 2, 3, 4, 1, 2, 2, 1, 2, 4]
def baseStart_1058204 : Nat := 118140960795 + 1058204 * 2 ^ 59
def prefixEnd_1058204 : Nat := 4983230072969 + 3 ^ 40 * 1058204 * 2
def baseEnd_1058204 : Nat := 181122427503494335227805

theorem tailTrace_1058204 : CollatzResearch.WordTrace tailWord_1058204 prefixEnd_1058204 181122427503494335227805 := by
  unfold tailWord_1058204
  simp only [CollatzResearch.WordTrace]
  refine ⟨19297935329157554849954833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25730580438876739799939777 19297935329157554849954833)
  ·
    refine ⟨14473451496868166137466125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19297935329157554849954833 14473451496868166137466125)
    ·
      refine ⟨5427544311325562301549797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14473451496868166137466125 5427544311325562301549797)
      ·
        refine ⟨1017664558373542931540587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5427544311325562301549797 1017664558373542931540587)
        ·
          refine ⟨1526496837560314397310881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1017664558373542931540587 1526496837560314397310881)
          ·
            refine ⟨1144872628170235797983161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1526496837560314397310881 1144872628170235797983161)
            ·
              refine ⟨858654471127676848487371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1144872628170235797983161 858654471127676848487371)
              ·
                refine ⟨1287981706691515272731057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 858654471127676848487371 1287981706691515272731057)
                ·
                  refine ⟨965986280018636454548293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1287981706691515272731057 965986280018636454548293)
                  ·
                    refine ⟨181122427503494335227805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 965986280018636454548293 181122427503494335227805)
                    ·
                      rfl

theorem cell23_1058204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_1058204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058204 prefixEnd_1058204 := by exact prefixLift 1058204
  have htrace : WordTrace (prefixWord ++ tailWord_1058204) baseStart_1058204 baseEnd_1058204 := by
    simpa [prefixWord, tailWord_1058204, baseEnd_1058204] using wordTrace_append hprefix tailTrace_1058204
  have hstable : (prefixWord ++ tailWord_1058204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058204).length < 2 ^ (prefixWord ++ tailWord_1058204).sum := by decide
  have hdescent : baseEnd_1058204 < baseStart_1058204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058220 : List Nat := [2, 2, 1, 1, 1, 1, 7, 2, 1, 3, 2]
def baseStart_1058220 : Nat := 118140960795 + 1058220 * 2 ^ 59
def prefixEnd_1058220 : Nat := 4983230072969 + 3 ^ 40 * 1058220 * 2
def baseEnd_1058220 : Nat := 543375498200954943083341

theorem tailTrace_1058220 : CollatzResearch.WordTrace tailWord_1058220 prefixEnd_1058220 543375498200954943083341 := by
  unfold tailWord_1058220
  simp only [CollatzResearch.WordTrace]
  refine ⟨19298227113128572216246057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25730969484171429621661409 19298227113128572216246057)
  ·
    refine ⟨14473670334846429162184543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19298227113128572216246057 14473670334846429162184543)
    ·
      refine ⟨21710505502269643743276815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14473670334846429162184543 21710505502269643743276815)
      ·
        refine ⟨32565758253404465614915223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21710505502269643743276815 32565758253404465614915223)
        ·
          refine ⟨48848637380106698422372835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32565758253404465614915223 48848637380106698422372835)
          ·
            refine ⟨73272956070160047633559253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48848637380106698422372835 73272956070160047633559253)
            ·
              refine ⟨1717334907894376116411545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 73272956070160047633559253 1717334907894376116411545)
              ·
                refine ⟨1288001180920782087308659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1717334907894376116411545 1288001180920782087308659)
                ·
                  refine ⟨1932001771381173130962989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1288001180920782087308659 1932001771381173130962989)
                  ·
                    refine ⟨724500664267939924111121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1932001771381173130962989 724500664267939924111121)
                    ·
                      refine ⟨543375498200954943083341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 724500664267939924111121 543375498200954943083341)
                      ·
                        rfl

theorem cell23_1058220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 3, 2].length) (baseStart_1058220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058220 prefixEnd_1058220 := by exact prefixLift 1058220
  have htrace : WordTrace (prefixWord ++ tailWord_1058220) baseStart_1058220 baseEnd_1058220 := by
    simpa [prefixWord, tailWord_1058220, baseEnd_1058220] using wordTrace_append hprefix tailTrace_1058220
  have hstable : (prefixWord ++ tailWord_1058220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058220).length < 2 ^ (prefixWord ++ tailWord_1058220).sum := by decide
  have hdescent : baseEnd_1058220 < baseStart_1058220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058237 : List Nat := [1, 4, 1, 2, 2, 1, 5, 1, 1, 3, 2]
def baseStart_1058237 : Nat := 118140960795 + 1058237 * 2 ^ 59
def prefixEnd_1058237 : Nat := 4983230072969 + 3 ^ 40 * 1058237 * 2
def baseEnd_1058237 : Nat := 543384227372081376570763

theorem tailTrace_1058237 : CollatzResearch.WordTrace tailWord_1058237 prefixEnd_1058237 543384227372081376570763 := by
  unfold tailWord_1058237
  simp only [CollatzResearch.WordTrace]
  refine ⟨38597074267195556335860965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25731382844797037557240643 38597074267195556335860965)
  ·
    refine ⟨7236951425099166812973931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38597074267195556335860965 7236951425099166812973931)
    ·
      refine ⟨10855427137648750219460897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7236951425099166812973931 10855427137648750219460897)
      ·
        refine ⟨8141570353236562664595673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10855427137648750219460897 8141570353236562664595673)
        ·
          refine ⟨6106177764927421998446755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8141570353236562664595673 6106177764927421998446755)
          ·
            refine ⟨9159266647391132997670133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6106177764927421998446755 9159266647391132997670133)
            ·
              refine ⟨858681248192918718531575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9159266647391132997670133 858681248192918718531575)
              ·
                refine ⟨1288021872289378077797363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 858681248192918718531575 1288021872289378077797363)
                ·
                  refine ⟨1932032808434067116696045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1288021872289378077797363 1932032808434067116696045)
                  ·
                    refine ⟨724512303162775168761017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1932032808434067116696045 724512303162775168761017)
                    ·
                      refine ⟨543384227372081376570763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 724512303162775168761017 543384227372081376570763)
                      ·
                        rfl

theorem cell23_1058237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_1058237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058237 prefixEnd_1058237 := by exact prefixLift 1058237
  have htrace : WordTrace (prefixWord ++ tailWord_1058237) baseStart_1058237 baseEnd_1058237 := by
    simpa [prefixWord, tailWord_1058237, baseEnd_1058237] using wordTrace_append hprefix tailTrace_1058237
  have hstable : (prefixWord ++ tailWord_1058237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058237).length < 2 ^ (prefixWord ++ tailWord_1058237).sum := by decide
  have hdescent : baseEnd_1058237 < baseStart_1058237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058290 : List Nat := [3, 2, 1, 4, 1, 1, 1, 5, 5]
def baseStart_1058290 : Nat := 118140960795 + 1058290 * 2 ^ 59
def prefixEnd_1058290 : Nat := 4983230072969 + 3 ^ 40 * 1058290 * 2
def baseEnd_1058290 : Nat := 60379049094085518800891

theorem tailTrace_1058290 : CollatzResearch.WordTrace tailWord_1058290 prefixEnd_1058290 60379049094085518800891 := by
  unfold tailWord_1058290
  simp only [CollatzResearch.WordTrace]
  refine ⟨9649751834000886596885081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25732671557335697591693549 9649751834000886596885081)
  ·
    refine ⟨7237313875500664947663811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9649751834000886596885081 7237313875500664947663811)
    ·
      refine ⟨10855970813250997421495717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7237313875500664947663811 10855970813250997421495717)
      ·
        refine ⟨2035494527484562016530447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10855970813250997421495717 2035494527484562016530447)
        ·
          refine ⟨3053241791226843024795671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2035494527484562016530447 3053241791226843024795671)
          ·
            refine ⟨4579862686840264537193507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3053241791226843024795671 4579862686840264537193507)
            ·
              refine ⟨6869794030260396805790261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4579862686840264537193507 6869794030260396805790261)
              ·
                refine ⟨644043190336912200542837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6869794030260396805790261 644043190336912200542837)
                ·
                  refine ⟨60379049094085518800891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 644043190336912200542837 60379049094085518800891)
                  ·
                    rfl

theorem cell23_1058290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 5, 5].length) (baseStart_1058290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058290 prefixEnd_1058290 := by exact prefixLift 1058290
  have htrace : WordTrace (prefixWord ++ tailWord_1058290) baseStart_1058290 baseEnd_1058290 := by
    simpa [prefixWord, tailWord_1058290, baseEnd_1058290] using wordTrace_append hprefix tailTrace_1058290
  have hstable : (prefixWord ++ tailWord_1058290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058290).length < 2 ^ (prefixWord ++ tailWord_1058290).sum := by decide
  have hdescent : baseEnd_1058290 < baseStart_1058290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058360 : List Nat := [2, 1, 2, 1, 4, 3, 1, 2, 2, 2, 3]
def baseStart_1058360 : Nat := 118140960795 + 1058360 * 2 ^ 59
def prefixEnd_1058360 : Nat := 4983230072969 + 3 ^ 40 * 1058360 * 2
def baseEnd_1058360 : Nat := 543447385492584395332697

theorem tailTrace_1058360 : CollatzResearch.WordTrace tailWord_1058360 prefixEnd_1058360 543447385492584395332697 := by
  unfold tailWord_1058360
  simp only [CollatzResearch.WordTrace]
  refine ⟨19300780222874974171294267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25734373630499965561725689 19300780222874974171294267)
  ·
    refine ⟨28951170334312461256941401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19300780222874974171294267 28951170334312461256941401)
    ·
      refine ⟨21713377750734345942706051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28951170334312461256941401 21713377750734345942706051)
      ·
        refine ⟨32570066626101518914059077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21713377750734345942706051 32570066626101518914059077)
        ·
          refine ⟨6106887492394034796386077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32570066626101518914059077 6106887492394034796386077)
          ·
            refine ⟨2290082809647763048644779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6106887492394034796386077 2290082809647763048644779)
            ·
              refine ⟨3435124214471644572967169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2290082809647763048644779 3435124214471644572967169)
              ·
                refine ⟨2576343160853733429725377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3435124214471644572967169 2576343160853733429725377)
                ·
                  refine ⟨1932257370640300072294033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2576343160853733429725377 1932257370640300072294033)
                  ·
                    refine ⟨1449193027980225054220525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1932257370640300072294033 1449193027980225054220525)
                    ·
                      refine ⟨543447385492584395332697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1449193027980225054220525 543447385492584395332697)
                      ·
                        rfl

theorem cell23_1058360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 2, 2, 3].length) (baseStart_1058360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058360 prefixEnd_1058360 := by exact prefixLift 1058360
  have htrace : WordTrace (prefixWord ++ tailWord_1058360) baseStart_1058360 baseEnd_1058360 := by
    simpa [prefixWord, tailWord_1058360, baseEnd_1058360] using wordTrace_append hprefix tailTrace_1058360
  have hstable : (prefixWord ++ tailWord_1058360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058360).length < 2 ^ (prefixWord ++ tailWord_1058360).sum := by decide
  have hdescent : baseEnd_1058360 < baseStart_1058360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058376 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 1, 11]
def baseStart_1058376 : Nat := 118140960795 + 1058376 * 2 ^ 59
def prefixEnd_1058376 : Nat := 4983230072969 + 3 ^ 40 * 1058376 * 2
def baseEnd_1058376 : Nat := 181151867061018777577541

theorem tailTrace_1058376 : CollatzResearch.WordTrace tailWord_1058376 prefixEnd_1058376 181151867061018777577541 := by
  unfold tailWord_1058376
  simp only [CollatzResearch.WordTrace]
  refine ⟨19301072006845991537585491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25734762675794655383447321 19301072006845991537585491)
  ·
    refine ⟨28951608010268987306378237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19301072006845991537585491 28951608010268987306378237)
    ·
      refine ⟨10856853003850870239891839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28951608010268987306378237 10856853003850870239891839)
      ·
        refine ⟨16285279505776305359837759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10856853003850870239891839 16285279505776305359837759)
        ·
          refine ⟨24427919258664458039756639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16285279505776305359837759 24427919258664458039756639)
          ·
            refine ⟨36641878887996687059634959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24427919258664458039756639 36641878887996687059634959)
            ·
              refine ⟨54962818331995030589452439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36641878887996687059634959 54962818331995030589452439)
              ·
                refine ⟨82444227497992545884178659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54962818331995030589452439 82444227497992545884178659)
                ·
                  refine ⟨123666341246988818826267989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82444227497992545884178659 123666341246988818826267989)
                  ·
                    refine ⟨181151867061018777577541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 123666341246988818826267989 181151867061018777577541)
                    ·
                      rfl

theorem cell23_1058376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_1058376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058376 prefixEnd_1058376 := by exact prefixLift 1058376
  have htrace : WordTrace (prefixWord ++ tailWord_1058376) baseStart_1058376 baseEnd_1058376 := by
    simpa [prefixWord, tailWord_1058376, baseEnd_1058376] using wordTrace_append hprefix tailTrace_1058376
  have hstable : (prefixWord ++ tailWord_1058376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058376).length < 2 ^ (prefixWord ++ tailWord_1058376).sum := by decide
  have hdescent : baseEnd_1058376 < baseStart_1058376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058380 : List Nat := [2, 2, 1, 3, 1, 3, 4, 1, 6]
def baseStart_1058380 : Nat := 118140960795 + 1058380 * 2 ^ 59
def prefixEnd_1058380 : Nat := 4983230072969 + 3 ^ 40 * 1058380 * 2
def baseEnd_1058380 : Nat := 60384183900630479675845

theorem tailTrace_1058380 : CollatzResearch.WordTrace tailWord_1058380 prefixEnd_1058380 60384183900630479675845 := by
  unfold tailWord_1058380
  simp only [CollatzResearch.WordTrace]
  refine ⟨19301144952838745879158297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25734859937118327838877729 19301144952838745879158297)
  ·
    refine ⟨14475858714629059409368723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19301144952838745879158297 14475858714629059409368723)
    ·
      refine ⟨21713788071943589114053085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14475858714629059409368723 21713788071943589114053085)
      ·
        refine ⟨8142670526978845917769907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21713788071943589114053085 8142670526978845917769907)
        ·
          refine ⟨12214005790468268876654861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8142670526978845917769907 12214005790468268876654861)
          ·
            refine ⟨4580252171425600828745573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12214005790468268876654861 4580252171425600828745573)
            ·
              refine ⟨858797282142300155389795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4580252171425600828745573 858797282142300155389795)
              ·
                refine ⟨1288195923213450233084693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 858797282142300155389795 1288195923213450233084693)
                ·
                  refine ⟨60384183900630479675845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1288195923213450233084693 60384183900630479675845)
                  ·
                    rfl

theorem cell23_1058380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 6].length) (baseStart_1058380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058380 prefixEnd_1058380 := by exact prefixLift 1058380
  have htrace : WordTrace (prefixWord ++ tailWord_1058380) baseStart_1058380 baseEnd_1058380 := by
    simpa [prefixWord, tailWord_1058380, baseEnd_1058380] using wordTrace_append hprefix tailTrace_1058380
  have hstable : (prefixWord ++ tailWord_1058380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058380).length < 2 ^ (prefixWord ++ tailWord_1058380).sum := by decide
  have hdescent : baseEnd_1058380 < baseStart_1058380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058464 : List Nat := [2, 1, 1, 4, 3, 3, 2, 1, 1, 1, 4]
def baseStart_1058464 : Nat := 118140960795 + 1058464 * 2 ^ 59
def prefixEnd_1058464 : Nat := 4983230072969 + 3 ^ 40 * 1058464 * 2
def baseEnd_1058464 : Nat := 543500787480651988432219

theorem tailTrace_1058464 : CollatzResearch.WordTrace tailWord_1058464 prefixEnd_1058464 543500787480651988432219 := by
  unfold tailWord_1058464
  simp only [CollatzResearch.WordTrace]
  refine ⟨19302676818686587052187223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25736902424915449402916297 19302676818686587052187223)
  ·
    refine ⟨28954015228029880578280835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19302676818686587052187223 28954015228029880578280835)
    ·
      refine ⟨43431022842044820867421253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28954015228029880578280835 43431022842044820867421253)
      ·
        refine ⟨8143316782883403912641485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43431022842044820867421253 8143316782883403912641485)
        ·
          refine ⟨3053743793581276467240557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8143316782883403912641485 3053743793581276467240557)
          ·
            refine ⟨1145153922592978675215209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3053743793581276467240557 1145153922592978675215209)
            ·
              refine ⟨858865441944734006411407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1145153922592978675215209 858865441944734006411407)
              ·
                refine ⟨1288298162917101009617111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 858865441944734006411407 1288298162917101009617111)
                ·
                  refine ⟨1932447244375651514425667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1288298162917101009617111 1932447244375651514425667)
                  ·
                    refine ⟨2898670866563477271638501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1932447244375651514425667 2898670866563477271638501)
                    ·
                      refine ⟨543500787480651988432219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2898670866563477271638501 543500787480651988432219)
                      ·
                        rfl

theorem cell23_1058464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_1058464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058464 prefixEnd_1058464 := by exact prefixLift 1058464
  have htrace : WordTrace (prefixWord ++ tailWord_1058464) baseStart_1058464 baseEnd_1058464 := by
    simpa [prefixWord, tailWord_1058464, baseEnd_1058464] using wordTrace_append hprefix tailTrace_1058464
  have hstable : (prefixWord ++ tailWord_1058464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058464).length < 2 ^ (prefixWord ++ tailWord_1058464).sum := by decide
  have hdescent : baseEnd_1058464 < baseStart_1058464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058498 : List Nat := [3, 5, 1, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_1058498 : Nat := 118140960795 + 1058498 * 2 ^ 59
def prefixEnd_1058498 : Nat := 4983230072969 + 3 ^ 40 * 1058498 * 2
def baseEnd_1058498 : Nat := 543518245822904855407063

theorem tailTrace_1058498 : CollatzResearch.WordTrace tailWord_1058498 prefixEnd_1058498 543518245822904855407063 := by
  unfold tailWord_1058498
  simp only [CollatzResearch.WordTrace]
  refine ⟨9651648429812499477778037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25737729146166665274074765 9651648429812499477778037)
  ·
    refine ⟨904842040294921826041691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9651648429812499477778037 904842040294921826041691)
    ·
      refine ⟨1357263060442382739062537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 904842040294921826041691 1357263060442382739062537)
      ·
        refine ⟨1017947295331787054296903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1357263060442382739062537 1017947295331787054296903)
        ·
          refine ⟨1526920942997680581445355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1017947295331787054296903 1526920942997680581445355)
          ·
            refine ⟨2290381414496520872168033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1526920942997680581445355 2290381414496520872168033)
            ·
              refine ⟨1717786060872390654126025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2290381414496520872168033 1717786060872390654126025)
              ·
                refine ⟨1288339545654292990594519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1717786060872390654126025 1288339545654292990594519)
                ·
                  refine ⟨1932509318481439485891779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1288339545654292990594519 1932509318481439485891779)
                  ·
                    refine ⟨2898763977722159228837669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1932509318481439485891779 2898763977722159228837669)
                    ·
                      refine ⟨543518245822904855407063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2898763977722159228837669 543518245822904855407063)
                      ·
                        rfl

theorem cell23_1058498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_1058498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058498 prefixEnd_1058498 := by exact prefixLift 1058498
  have htrace : WordTrace (prefixWord ++ tailWord_1058498) baseStart_1058498 baseEnd_1058498 := by
    simpa [prefixWord, tailWord_1058498, baseEnd_1058498] using wordTrace_append hprefix tailTrace_1058498
  have hstable : (prefixWord ++ tailWord_1058498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058498).length < 2 ^ (prefixWord ++ tailWord_1058498).sum := by decide
  have hdescent : baseEnd_1058498 < baseStart_1058498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058548 : List Nat := [2, 6, 1, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_1058548 : Nat := 118140960795 + 1058548 * 2 ^ 59
def prefixEnd_1058548 : Nat := 4983230072969 + 3 ^ 40 * 1058548 * 2
def baseEnd_1058548 : Nat := 543543919855629659781833

theorem tailTrace_1058548 : CollatzResearch.WordTrace tailWord_1058548 prefixEnd_1058548 543543919855629659781833 := by
  unfold tailWord_1058548
  simp only [CollatzResearch.WordTrace]
  refine ⟨19304208684534428225216149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25738944912712570966954865 19304208684534428225216149)
  ·
    refine ⟨904884782087551323057007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19304208684534428225216149 904884782087551323057007)
    ·
      refine ⟨1357327173131326984585511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 904884782087551323057007 1357327173131326984585511)
      ·
        refine ⟨2035990759696990476878267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1357327173131326984585511 2035990759696990476878267)
        ·
          refine ⟨3053986139545485715317401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2035990759696990476878267 3053986139545485715317401)
          ·
            refine ⟨2290489604659114286488051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3053986139545485715317401 2290489604659114286488051)
            ·
              refine ⟨3435734406988671429732077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2290489604659114286488051 3435734406988671429732077)
              ·
                refine ⟨1288400402620751786149529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3435734406988671429732077 1288400402620751786149529)
                ·
                  refine ⟨966300301965563839612147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1288400402620751786149529 966300301965563839612147)
                  ·
                    refine ⟨1449450452948345759418221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 966300301965563839612147 1449450452948345759418221)
                    ·
                      refine ⟨543543919855629659781833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1449450452948345759418221 543543919855629659781833)
                      ·
                        rfl

theorem cell23_1058548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_1058548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058548 prefixEnd_1058548 := by exact prefixLift 1058548
  have htrace : WordTrace (prefixWord ++ tailWord_1058548) baseStart_1058548 baseEnd_1058548 := by
    simpa [prefixWord, tailWord_1058548, baseEnd_1058548] using wordTrace_append hprefix tailTrace_1058548
  have hstable : (prefixWord ++ tailWord_1058548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058548).length < 2 ^ (prefixWord ++ tailWord_1058548).sum := by decide
  have hdescent : baseEnd_1058548 < baseStart_1058548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058558 : List Nat := [4, 2, 2, 1, 3, 2, 1, 2, 1, 3, 2]
def baseStart_1058558 : Nat := 118140960795 + 1058558 * 2 ^ 59
def prefixEnd_1058558 : Nat := 4983230072969 + 3 ^ 40 * 1058558 * 2
def baseEnd_1058558 : Nat := 543549054662174620656787

theorem tailTrace_1058558 : CollatzResearch.WordTrace tailWord_1058558 prefixEnd_1058558 543549054662174620656787 := by
  unfold tailWord_1058558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4826097762379078519787041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25739188066021752105530885 4826097762379078519787041)
  ·
    refine ⟨3619573321784308889840281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4826097762379078519787041 3619573321784308889840281)
    ·
      refine ⟨2714679991338231667380211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3619573321784308889840281 2714679991338231667380211)
      ·
        refine ⟨4072019987007347501070317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2714679991338231667380211 4072019987007347501070317)
        ·
          refine ⟨1527007495127755312901369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4072019987007347501070317 1527007495127755312901369)
          ·
            refine ⟨1145255621345816484676027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1527007495127755312901369 1145255621345816484676027)
            ·
              refine ⟨1717883432018724727014041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1145255621345816484676027 1717883432018724727014041)
              ·
                refine ⟨1288412574014043545260531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1717883432018724727014041 1288412574014043545260531)
                ·
                  refine ⟨1932618861021065317890797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1288412574014043545260531 1932618861021065317890797)
                  ·
                    refine ⟨724732072882899494209049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1932618861021065317890797 724732072882899494209049)
                    ·
                      refine ⟨543549054662174620656787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 724732072882899494209049 543549054662174620656787)
                      ·
                        rfl

theorem cell23_1058558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_1058558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058558 prefixEnd_1058558 := by exact prefixLift 1058558
  have htrace : WordTrace (prefixWord ++ tailWord_1058558) baseStart_1058558 baseEnd_1058558 := by
    simpa [prefixWord, tailWord_1058558, baseEnd_1058558] using wordTrace_append hprefix tailTrace_1058558
  have hstable : (prefixWord ++ tailWord_1058558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058558).length < 2 ^ (prefixWord ++ tailWord_1058558).sum := by decide
  have hdescent : baseEnd_1058558 < baseStart_1058558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058597 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 2, 5, 2]
def baseStart_1058597 : Nat := 118140960795 + 1058597 * 2 ^ 59
def prefixEnd_1058597 : Nat := 4983230072969 + 3 ^ 40 * 1058597 * 2
def baseEnd_1058597 : Nat := 543569080407699968069107

theorem tailTrace_1058597 : CollatzResearch.WordTrace tailWord_1058597 prefixEnd_1058597 543569080407699968069107 := by
  unfold tailWord_1058597
  simp only [CollatzResearch.WordTrace]
  refine ⟨38610204545891337818966045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25740136363927558545977363 38610204545891337818966045)
  ·
    refine ⟨14478826704709251682112267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38610204545891337818966045 14478826704709251682112267)
    ·
      refine ⟨21718240057063877523168401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14478826704709251682112267 21718240057063877523168401)
      ·
        refine ⟨16288680042797908142376301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21718240057063877523168401 16288680042797908142376301)
        ·
          refine ⟨6108255016049215553391113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16288680042797908142376301 6108255016049215553391113)
          ·
            refine ⟨4581191262036911665043335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6108255016049215553391113 4581191262036911665043335)
            ·
              refine ⟨6871786893055367497565003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4581191262036911665043335 6871786893055367497565003)
              ·
                refine ⟨10307680339583051246347505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6871786893055367497565003 10307680339583051246347505)
                ·
                  refine ⟨7730760254687288434760629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10307680339583051246347505 7730760254687288434760629)
                  ·
                    refine ⟨724758773876933290758809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7730760254687288434760629 724758773876933290758809)
                    ·
                      refine ⟨543569080407699968069107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 724758773876933290758809 543569080407699968069107)
                      ·
                        rfl

theorem cell23_1058597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 5, 2].length) (baseStart_1058597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058597 prefixEnd_1058597 := by exact prefixLift 1058597
  have htrace : WordTrace (prefixWord ++ tailWord_1058597) baseStart_1058597 baseEnd_1058597 := by
    simpa [prefixWord, tailWord_1058597, baseEnd_1058597] using wordTrace_append hprefix tailTrace_1058597
  have hstable : (prefixWord ++ tailWord_1058597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058597).length < 2 ^ (prefixWord ++ tailWord_1058597).sum := by decide
  have hdescent : baseEnd_1058597 < baseStart_1058597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058627 : List Nat := [1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 4]
def baseStart_1058627 : Nat := 118140960795 + 1058627 * 2 ^ 59
def prefixEnd_1058627 : Nat := 4983230072969 + 3 ^ 40 * 1058627 * 2
def baseEnd_1058627 : Nat := 543584484827334850693969

theorem tailTrace_1058627 : CollatzResearch.WordTrace tailWord_1058627 prefixEnd_1058627 543584484827334850693969 := by
  unfold tailWord_1058627
  simp only [CollatzResearch.WordTrace]
  refine ⟨38611298735782652942558135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25740865823855101961705423 38611298735782652942558135)
  ·
    refine ⟨57916948103673979413837203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38611298735782652942558135 57916948103673979413837203)
    ·
      refine ⟨86875422155510969120755805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57916948103673979413837203 86875422155510969120755805)
      ·
        refine ⟨32578283308316613420283427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86875422155510969120755805 32578283308316613420283427)
        ·
          refine ⟨48867424962474920130425141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32578283308316613420283427 48867424962474920130425141)
          ·
            refine ⟨4581321090232023762227357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48867424962474920130425141 4581321090232023762227357)
            ·
              refine ⟨1717995408837008910835259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4581321090232023762227357 1717995408837008910835259)
              ·
                refine ⟨2576993113255513366252889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1717995408837008910835259 2576993113255513366252889)
                ·
                  refine ⟨1932744834941635024689667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2576993113255513366252889 1932744834941635024689667)
                  ·
                    refine ⟨2899117252412452537034501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1932744834941635024689667 2899117252412452537034501)
                    ·
                      refine ⟨543584484827334850693969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2899117252412452537034501 543584484827334850693969)
                      ·
                        rfl

theorem cell23_1058627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 4].length) (baseStart_1058627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058627 prefixEnd_1058627 := by exact prefixLift 1058627
  have htrace : WordTrace (prefixWord ++ tailWord_1058627) baseStart_1058627 baseEnd_1058627 := by
    simpa [prefixWord, tailWord_1058627, baseEnd_1058627] using wordTrace_append hprefix tailTrace_1058627
  have hstable : (prefixWord ++ tailWord_1058627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058627).length < 2 ^ (prefixWord ++ tailWord_1058627).sum := by decide
  have hdescent : baseEnd_1058627 < baseStart_1058627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058644 : List Nat := [2, 4, 1, 1, 3, 1, 1, 2, 2, 4, 2]
def baseStart_1058644 : Nat := 118140960795 + 1058644 * 2 ^ 59
def prefixEnd_1058644 : Nat := 4983230072969 + 3 ^ 40 * 1058644 * 2
def baseEnd_1058644 : Nat := 543593213998461284181391

theorem tailTrace_1058644 : CollatzResearch.WordTrace tailWord_1058644 prefixEnd_1058644 543593213998461284181391 := by
  unfold tailWord_1058644
  simp only [CollatzResearch.WordTrace]
  refine ⟨19305959388360532422963493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25741279184480709897284657 19305959388360532422963493)
  ·
    refine ⟨3619867385317599829305655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19305959388360532422963493 3619867385317599829305655)
    ·
      refine ⟨5429801077976399743958483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3619867385317599829305655 5429801077976399743958483)
      ·
        refine ⟨8144701616964599615937725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5429801077976399743958483 8144701616964599615937725)
        ·
          refine ⟨3054263106361724855976647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8144701616964599615937725 3054263106361724855976647)
          ·
            refine ⟨4581394659542587283964971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3054263106361724855976647 4581394659542587283964971)
            ·
              refine ⟨6872091989313880925947457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4581394659542587283964971 6872091989313880925947457)
              ·
                refine ⟨5154068991985410694460593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6872091989313880925947457 5154068991985410694460593)
                ·
                  refine ⟨3865551743989058020845445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5154068991985410694460593 3865551743989058020845445)
                  ·
                    refine ⟨724790951997948378908521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3865551743989058020845445 724790951997948378908521)
                    ·
                      refine ⟨543593213998461284181391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 724790951997948378908521 543593213998461284181391)
                      ·
                        rfl

theorem cell23_1058644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_1058644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058644 prefixEnd_1058644 := by exact prefixLift 1058644
  have htrace : WordTrace (prefixWord ++ tailWord_1058644) baseStart_1058644 baseEnd_1058644 := by
    simpa [prefixWord, tailWord_1058644, baseEnd_1058644] using wordTrace_append hprefix tailTrace_1058644
  have hstable : (prefixWord ++ tailWord_1058644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058644).length < 2 ^ (prefixWord ++ tailWord_1058644).sum := by decide
  have hdescent : baseEnd_1058644 < baseStart_1058644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058650 : List Nat := [3, 1, 1, 2, 1, 3, 3, 1, 8]
def baseStart_1058650 : Nat := 118140960795 + 1058650 * 2 ^ 59
def prefixEnd_1058650 : Nat := 4983230072969 + 3 ^ 40 * 1058650 * 2
def baseEnd_1058650 : Nat := 60399588320265362300707

theorem tailTrace_1058650 : CollatzResearch.WordTrace tailWord_1058650 prefixEnd_1058650 60399588320265362300707 := by
  unfold tailWord_1058650
  simp only [CollatzResearch.WordTrace]
  refine ⟨9653034403674831967661351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25741425076466218580430269 9653034403674831967661351)
  ·
    refine ⟨14479551605512247951492027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9653034403674831967661351 14479551605512247951492027)
    ·
      refine ⟨21719327408268371927238041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14479551605512247951492027 21719327408268371927238041)
      ·
        refine ⟨16289495556201278945428531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21719327408268371927238041 16289495556201278945428531)
        ·
          refine ⟨24434243334301918418142797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16289495556201278945428531 24434243334301918418142797)
          ·
            refine ⟨9162841250363219406803549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24434243334301918418142797 9162841250363219406803549)
            ·
              refine ⟨3436065468886207277551331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9162841250363219406803549 3436065468886207277551331)
              ·
                refine ⟨5154098203329310916326997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3436065468886207277551331 5154098203329310916326997)
                ·
                  refine ⟨60399588320265362300707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5154098203329310916326997 60399588320265362300707)
                  ·
                    rfl

theorem cell23_1058650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 8].length) (baseStart_1058650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058650 prefixEnd_1058650 := by exact prefixLift 1058650
  have htrace : WordTrace (prefixWord ++ tailWord_1058650) baseStart_1058650 baseEnd_1058650 := by
    simpa [prefixWord, tailWord_1058650, baseEnd_1058650] using wordTrace_append hprefix tailTrace_1058650
  have hstable : (prefixWord ++ tailWord_1058650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058650).length < 2 ^ (prefixWord ++ tailWord_1058650).sum := by decide
  have hdescent : baseEnd_1058650 < baseStart_1058650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058677 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 2, 5, 3]
def baseStart_1058677 : Nat := 118140960795 + 1058677 * 2 ^ 59
def prefixEnd_1058677 : Nat := 4983230072969 + 3 ^ 40 * 1058677 * 2
def baseEnd_1058677 : Nat := 543610158860059655068739

theorem tailTrace_1058677 : CollatzResearch.WordTrace tailWord_1058677 prefixEnd_1058677 543610158860059655068739 := by
  unfold tailWord_1058677
  simp only [CollatzResearch.WordTrace]
  refine ⟨38613122385601511481878285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25742081590401007654585523 38613122385601511481878285)
  ·
    refine ⟨14479920894600566805704357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38613122385601511481878285 14479920894600566805704357)
    ·
      refine ⟨2714985167737606276069567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14479920894600566805704357 2714985167737606276069567)
      ·
        refine ⟨4072477751606409414104351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2714985167737606276069567 4072477751606409414104351)
        ·
          refine ⟨6108716627409614121156527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4072477751606409414104351 6108716627409614121156527)
          ·
            refine ⟨9163074941114421181734791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6108716627409614121156527 9163074941114421181734791)
            ·
              refine ⟨13744612411671631772602187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9163074941114421181734791 13744612411671631772602187)
              ·
                refine ⟨20616918617507447658903281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13744612411671631772602187 20616918617507447658903281)
                ·
                  refine ⟨15462688963130585744177461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20616918617507447658903281 15462688963130585744177461)
                  ·
                    refine ⟨1449627090293492413516637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15462688963130585744177461 1449627090293492413516637)
                    ·
                      refine ⟨543610158860059655068739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1449627090293492413516637 543610158860059655068739)
                      ·
                        rfl

theorem cell23_1058677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_1058677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058677 prefixEnd_1058677 := by exact prefixLift 1058677
  have htrace : WordTrace (prefixWord ++ tailWord_1058677) baseStart_1058677 baseEnd_1058677 := by
    simpa [prefixWord, tailWord_1058677, baseEnd_1058677] using wordTrace_append hprefix tailTrace_1058677
  have hstable : (prefixWord ++ tailWord_1058677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058677).length < 2 ^ (prefixWord ++ tailWord_1058677).sum := by decide
  have hdescent : baseEnd_1058677 < baseStart_1058677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058680 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 7, 5]
def baseStart_1058680 : Nat := 118140960795 + 1058680 * 2 ^ 59
def prefixEnd_1058680 : Nat := 4983230072969 + 3 ^ 40 * 1058680 * 2
def baseEnd_1058680 : Nat := 181203899767341047777075

theorem tailTrace_1058680 : CollatzResearch.WordTrace tailWord_1058680 prefixEnd_1058680 181203899767341047777075 := by
  unfold tailWord_1058680
  simp only [CollatzResearch.WordTrace]
  refine ⟨19306615902295321497118747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25742154536393761996158329 19306615902295321497118747)
  ·
    refine ⟨28959923853442982245678121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19306615902295321497118747 28959923853442982245678121)
    ·
      refine ⟨21719942890082236684258591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28959923853442982245678121 21719942890082236684258591)
      ·
        refine ⟨32579914335123355026387887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21719942890082236684258591 32579914335123355026387887)
        ·
          refine ⟨48869871502685032539581831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32579914335123355026387887 48869871502685032539581831)
          ·
            refine ⟨73304807254027548809372747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48869871502685032539581831 73304807254027548809372747)
            ·
              refine ⟨109957210881041323214059121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73304807254027548809372747 109957210881041323214059121)
              ·
                refine ⟨82467908160780992410544341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109957210881041323214059121 82467908160780992410544341)
                ·
                  refine ⟨1932841597518304509622133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 82467908160780992410544341 1932841597518304509622133)
                  ·
                    refine ⟨181203899767341047777075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1932841597518304509622133 181203899767341047777075)
                    ·
                      rfl

theorem cell23_1058680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 7, 5].length) (baseStart_1058680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058680 prefixEnd_1058680 := by exact prefixLift 1058680
  have htrace : WordTrace (prefixWord ++ tailWord_1058680) baseStart_1058680 baseEnd_1058680 := by
    simpa [prefixWord, tailWord_1058680, baseEnd_1058680] using wordTrace_append hprefix tailTrace_1058680
  have hstable : (prefixWord ++ tailWord_1058680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058680).length < 2 ^ (prefixWord ++ tailWord_1058680).sum := by decide
  have hdescent : baseEnd_1058680 < baseStart_1058680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058697 : List Nat := [1, 2, 1, 1, 5, 1, 1, 5, 1, 5]
def baseStart_1058697 : Nat := 118140960795 + 1058697 * 2 ^ 59
def prefixEnd_1058697 : Nat := 4983230072969 + 3 ^ 40 * 1058697 * 2
def baseEnd_1058697 : Nat := 181206809491049858939549

theorem tailTrace_1058697 : CollatzResearch.WordTrace tailWord_1058697 prefixEnd_1058697 181206809491049858939549 := by
  unfold tailWord_1058697
  simp only [CollatzResearch.WordTrace]
  refine ⟨38613851845529054897606345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25742567897019369931737563 38613851845529054897606345)
  ·
    refine ⟨28960388884146791173204759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38613851845529054897606345 28960388884146791173204759)
    ·
      refine ⟨43440583326220186759807139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28960388884146791173204759 43440583326220186759807139)
      ·
        refine ⟨65160874989330280139710709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43440583326220186759807139 65160874989330280139710709)
        ·
          refine ⟨6108832030249713763097879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65160874989330280139710709 6108832030249713763097879)
          ·
            refine ⟨9163248045374570644646819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6108832030249713763097879 9163248045374570644646819)
            ·
              refine ⟨13744872068061855966970229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9163248045374570644646819 13744872068061855966970229)
              ·
                refine ⟨1288581756380798996903459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13744872068061855966970229 1288581756380798996903459)
                ·
                  refine ⟨1932872634571198495355189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1288581756380798996903459 1932872634571198495355189)
                  ·
                    refine ⟨181206809491049858939549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1932872634571198495355189 181206809491049858939549)
                    ·
                      rfl

theorem cell23_1058697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 5].length) (baseStart_1058697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058697 prefixEnd_1058697 := by exact prefixLift 1058697
  have htrace : WordTrace (prefixWord ++ tailWord_1058697) baseStart_1058697 baseEnd_1058697 := by
    simpa [prefixWord, tailWord_1058697, baseEnd_1058697] using wordTrace_append hprefix tailTrace_1058697
  have hstable : (prefixWord ++ tailWord_1058697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058697).length < 2 ^ (prefixWord ++ tailWord_1058697).sum := by decide
  have hdescent : baseEnd_1058697 < baseStart_1058697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058711 : List Nat := [1, 1, 3, 3, 1, 5, 1, 1, 3, 1, 3]
def baseStart_1058711 : Nat := 118140960795 + 1058711 * 2 ^ 59
def prefixEnd_1058711 : Nat := 4983230072969 + 3 ^ 40 * 1058711 * 2
def baseEnd_1058711 : Nat := 543627617202312522043583

theorem tailTrace_1058711 : CollatzResearch.WordTrace tailWord_1058711 prefixEnd_1058711 543627617202312522043583 := by
  unfold tailWord_1058711
  simp only [CollatzResearch.WordTrace]
  refine ⟨38614362467478335288615987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25742908311652223525743991 38614362467478335288615987)
  ·
    refine ⟨57921543701217502932923981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38614362467478335288615987 57921543701217502932923981)
    ·
      refine ⟨21720578887956563599846493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57921543701217502932923981 21720578887956563599846493)
      ·
        refine ⟨8145217082983711349942435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21720578887956563599846493 8145217082983711349942435)
        ·
          refine ⟨12217825624475567024913653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8145217082983711349942435 12217825624475567024913653)
          ·
            refine ⟨1145421152294584408585655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12217825624475567024913653 1145421152294584408585655)
            ·
              refine ⟨1718131728441876612878483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1145421152294584408585655 1718131728441876612878483)
              ·
                refine ⟨2577197592662814919317725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1718131728441876612878483 2577197592662814919317725)
                ·
                  refine ⟨966449097248555594744147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2577197592662814919317725 966449097248555594744147)
                  ·
                    refine ⟨1449673645872833392116221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 966449097248555594744147 1449673645872833392116221)
                    ·
                      refine ⟨543627617202312522043583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1449673645872833392116221 543627617202312522043583)
                      ·
                        rfl

theorem cell23_1058711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_1058711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058711 prefixEnd_1058711 := by exact prefixLift 1058711
  have htrace : WordTrace (prefixWord ++ tailWord_1058711) baseStart_1058711 baseEnd_1058711 := by
    simpa [prefixWord, tailWord_1058711, baseEnd_1058711] using wordTrace_append hprefix tailTrace_1058711
  have hstable : (prefixWord ++ tailWord_1058711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058711).length < 2 ^ (prefixWord ++ tailWord_1058711).sum := by decide
  have hdescent : baseEnd_1058711 < baseStart_1058711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058748 : List Nat := [2, 2, 2, 5, 1, 1, 3, 1, 1, 5]
def baseStart_1058748 : Nat := 118140960795 + 1058748 * 2 ^ 59
def prefixEnd_1058748 : Nat := 4983230072969 + 3 ^ 40 * 1058748 * 2
def baseEnd_1058748 : Nat := 181215538662176292426971

theorem tailTrace_1058748 : CollatzResearch.WordTrace tailWord_1058748 prefixEnd_1058748 181215538662176292426971 := by
  unfold tailWord_1058748
  simp only [CollatzResearch.WordTrace]
  refine ⟨19307855984172145303856449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25743807978896193738475265 19307855984172145303856449)
  ·
    refine ⟨14480891988129108977892337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19307855984172145303856449 14480891988129108977892337)
    ·
      refine ⟨10860668991096831733419253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14480891988129108977892337 10860668991096831733419253)
      ·
        refine ⟨1018187717915327975008055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10860668991096831733419253 1018187717915327975008055)
        ·
          refine ⟨1527281576872991962512083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1018187717915327975008055 1527281576872991962512083)
          ·
            refine ⟨2290922365309487943768125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1527281576872991962512083 2290922365309487943768125)
            ·
              refine ⟨859095886991057978913047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2290922365309487943768125 859095886991057978913047)
              ·
                refine ⟨1288643830486586968369571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 859095886991057978913047 1288643830486586968369571)
                ·
                  refine ⟨1932965745729880452554357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1288643830486586968369571 1932965745729880452554357)
                  ·
                    refine ⟨181215538662176292426971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1932965745729880452554357 181215538662176292426971)
                    ·
                      rfl

theorem cell23_1058748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_1058748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058748 prefixEnd_1058748 := by exact prefixLift 1058748
  have htrace : WordTrace (prefixWord ++ tailWord_1058748) baseStart_1058748 baseEnd_1058748 := by
    simpa [prefixWord, tailWord_1058748, baseEnd_1058748] using wordTrace_append hprefix tailTrace_1058748
  have hstable : (prefixWord ++ tailWord_1058748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058748).length < 2 ^ (prefixWord ++ tailWord_1058748).sum := by decide
  have hdescent : baseEnd_1058748 < baseStart_1058748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058767 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 3, 3, 3]
def baseStart_1058767 : Nat := 118140960795 + 1058767 * 2 ^ 59
def prefixEnd_1058767 : Nat := 4983230072969 + 3 ^ 40 * 1058767 * 2
def baseEnd_1058767 : Nat := 543656372118964302943325

theorem tailTrace_1058767 : CollatzResearch.WordTrace tailWord_1058767 prefixEnd_1058767 543656372118964302943325 := by
  unfold tailWord_1058767
  simp only [CollatzResearch.WordTrace]
  refine ⟨38616404955275456852654555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25744269970183637901769703 38616404955275456852654555)
  ·
    refine ⟨57924607432913185278981833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38616404955275456852654555 57924607432913185278981833)
    ·
      refine ⟨43443455574684888959236375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57924607432913185278981833 43443455574684888959236375)
      ·
        refine ⟨65165183362027333438854563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43443455574684888959236375 65165183362027333438854563)
        ·
          refine ⟨97747775043041000158281845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65165183362027333438854563 97747775043041000158281845)
          ·
            refine ⟨9163853910285093764838923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97747775043041000158281845 9163853910285093764838923)
            ·
              refine ⟨13745780865427640647258385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9163853910285093764838923 13745780865427640647258385)
              ·
                refine ⟨10309335649070730485443789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13745780865427640647258385 10309335649070730485443789)
                ·
                  refine ⟨3866000868401523932041421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10309335649070730485443789 3866000868401523932041421)
                  ·
                    refine ⟨1449750325650571474515533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3866000868401523932041421 1449750325650571474515533)
                    ·
                      refine ⟨543656372118964302943325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1449750325650571474515533 543656372118964302943325)
                      ·
                        rfl

theorem cell23_1058767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 3, 3].length) (baseStart_1058767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058767 prefixEnd_1058767 := by exact prefixLift 1058767
  have htrace : WordTrace (prefixWord ++ tailWord_1058767) baseStart_1058767 baseEnd_1058767 := by
    simpa [prefixWord, tailWord_1058767, baseEnd_1058767] using wordTrace_append hprefix tailTrace_1058767
  have hstable : (prefixWord ++ tailWord_1058767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058767).length < 2 ^ (prefixWord ++ tailWord_1058767).sum := by decide
  have hdescent : baseEnd_1058767 < baseStart_1058767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058781 : List Nat := [1, 4, 3, 1, 3, 1, 2, 1, 1, 2, 4]
def baseStart_1058781 : Nat := 118140960795 + 1058781 * 2 ^ 59
def prefixEnd_1058781 : Nat := 4983230072969 + 3 ^ 40 * 1058781 * 2
def baseEnd_1058781 : Nat := 543663560848127248168261

theorem tailTrace_1058781 : CollatzResearch.WordTrace tailWord_1058781 prefixEnd_1058781 543663560848127248168261 := by
  unfold tailWord_1058781
  simp only [CollatzResearch.WordTrace]
  refine ⟨38616915577224737243664197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25744610384816491495776131 38616915577224737243664197)
  ·
    refine ⟨7240671670729638233187037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38616915577224737243664197 7240671670729638233187037)
    ·
      refine ⟨2715251876523614337445139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7240671670729638233187037 2715251876523614337445139)
      ·
        refine ⟨4072877814785421506167709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2715251876523614337445139 4072877814785421506167709)
        ·
          refine ⟨1527329180544533064812891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4072877814785421506167709 1527329180544533064812891)
          ·
            refine ⟨2290993770816799597219337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1527329180544533064812891 2290993770816799597219337)
            ·
              refine ⟨1718245328112599697914503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2290993770816799597219337 1718245328112599697914503)
              ·
                refine ⟨2577367992168899546871755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1718245328112599697914503 2577367992168899546871755)
                ·
                  refine ⟨3866051988253349320307633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2577367992168899546871755 3866051988253349320307633)
                  ·
                    refine ⟨2899538991190011990230725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3866051988253349320307633 2899538991190011990230725)
                    ·
                      refine ⟨543663560848127248168261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2899538991190011990230725 543663560848127248168261)
                      ·
                        rfl

theorem cell23_1058781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_1058781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058781 prefixEnd_1058781 := by exact prefixLift 1058781
  have htrace : WordTrace (prefixWord ++ tailWord_1058781) baseStart_1058781 baseEnd_1058781 := by
    simpa [prefixWord, tailWord_1058781, baseEnd_1058781] using wordTrace_append hprefix tailTrace_1058781
  have hstable : (prefixWord ++ tailWord_1058781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058781).length < 2 ^ (prefixWord ++ tailWord_1058781).sum := by decide
  have hdescent : baseEnd_1058781 < baseStart_1058781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058817 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 4, 6]
def baseStart_1058817 : Nat := 118140960795 + 1058817 * 2 ^ 59
def prefixEnd_1058817 : Nat := 4983230072969 + 3 ^ 40 * 1058817 * 2
def baseEnd_1058817 : Nat := 181227348717229702439365

theorem tailTrace_1058817 : CollatzResearch.WordTrace tailWord_1058817 prefixEnd_1058817 181227348717229702439365 := by
  unfold tailWord_1058817
  simp only [CollatzResearch.WordTrace]
  refine ⟨38618228605094315391974705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25745485736729543594649803 38618228605094315391974705)
  ·
    refine ⟨28963671453820736543981029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38618228605094315391974705 28963671453820736543981029)
    ·
      refine ⟨5430688397591388101996443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28963671453820736543981029 5430688397591388101996443)
      ·
        refine ⟨8146032596387082152994665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5430688397591388101996443 8146032596387082152994665)
        ·
          refine ⟨6109524447290311614745999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8146032596387082152994665 6109524447290311614745999)
          ·
            refine ⟨9164286670935467422118999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6109524447290311614745999 9164286670935467422118999)
            ·
              refine ⟨13746430006403201133178499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9164286670935467422118999 13746430006403201133178499)
              ·
                refine ⟨20619645009604801699767749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13746430006403201133178499 20619645009604801699767749)
                ·
                  refine ⟨3866183439300900318706453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20619645009604801699767749 3866183439300900318706453)
                  ·
                    refine ⟨181227348717229702439365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3866183439300900318706453 181227348717229702439365)
                    ·
                      rfl

theorem cell23_1058817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_1058817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058817 prefixEnd_1058817 := by exact prefixLift 1058817
  have htrace : WordTrace (prefixWord ++ tailWord_1058817) baseStart_1058817 baseEnd_1058817 := by
    simpa [prefixWord, tailWord_1058817, baseEnd_1058817] using wordTrace_append hprefix tailTrace_1058817
  have hstable : (prefixWord ++ tailWord_1058817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058817).length < 2 ^ (prefixWord ++ tailWord_1058817).sum := by decide
  have hdescent : baseEnd_1058817 < baseStart_1058817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058847 : List Nat := [1, 1, 2, 4, 1, 2, 1, 4, 7]
def baseStart_1058847 : Nat := 118140960795 + 1058847 * 2 ^ 59
def prefixEnd_1058847 : Nat := 4983230072969 + 3 ^ 40 * 1058847 * 2
def baseEnd_1058847 : Nat := 60410827841258221104773

theorem tailTrace_1058847 : CollatzResearch.WordTrace tailWord_1058847 prefixEnd_1058847 60410827841258221104773 := by
  unfold tailWord_1058847
  simp only [CollatzResearch.WordTrace]
  refine ⟨38619322794985630515566795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25746215196657087010377863 38619322794985630515566795)
  ·
    refine ⟨57928984192478445773350193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38619322794985630515566795 57928984192478445773350193)
    ·
      refine ⟨43446738144358834330012645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57928984192478445773350193 43446738144358834330012645)
      ·
        refine ⟨8146263402067281436877371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43446738144358834330012645 8146263402067281436877371)
        ·
          refine ⟨12219395103100922155316057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8146263402067281436877371 12219395103100922155316057)
          ·
            refine ⟨9164546327325691616487043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12219395103100922155316057 9164546327325691616487043)
            ·
              refine ⟨13746819490988537424730565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9164546327325691616487043 13746819490988537424730565)
              ·
                refine ⟨2577528654560350767136981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13746819490988537424730565 2577528654560350767136981)
                ·
                  refine ⟨60410827841258221104773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2577528654560350767136981 60410827841258221104773)
                  ·
                    rfl

theorem cell23_1058847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 7].length) (baseStart_1058847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058847 prefixEnd_1058847 := by exact prefixLift 1058847
  have htrace : WordTrace (prefixWord ++ tailWord_1058847) baseStart_1058847 baseEnd_1058847 := by
    simpa [prefixWord, tailWord_1058847, baseEnd_1058847] using wordTrace_append hprefix tailTrace_1058847
  have hstable : (prefixWord ++ tailWord_1058847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058847).length < 2 ^ (prefixWord ++ tailWord_1058847).sum := by decide
  have hdescent : baseEnd_1058847 < baseStart_1058847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058858 : List Nat := [3, 1, 4, 1, 2, 1, 1, 2, 4, 2, 2]
def baseStart_1058858 : Nat := 118140960795 + 1058858 * 2 ^ 59
def prefixEnd_1058858 : Nat := 4983230072969 + 3 ^ 40 * 1058858 * 2
def baseEnd_1058858 : Nat := 543703098858523446905407

theorem tailTrace_1058858 : CollatzResearch.WordTrace tailWord_1058858 prefixEnd_1058858 543703098858523446905407 := by
  unfold tailWord_1058858
  simp only [CollatzResearch.WordTrace]
  refine ⟨9654930999486444848554307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25746482665297186262811485 9654930999486444848554307)
  ·
    refine ⟨14482396499229667272831461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9654930999486444848554307 14482396499229667272831461)
    ·
      refine ⟨2715449343605562613655899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14482396499229667272831461 2715449343605562613655899)
      ·
        refine ⟨4073174015408343920483849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2715449343605562613655899 4073174015408343920483849)
        ·
          refine ⟨3054880511556257940362887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4073174015408343920483849 3054880511556257940362887)
          ·
            refine ⟨4582320767334386910544331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3054880511556257940362887 4582320767334386910544331)
            ·
              refine ⟨6873481151001580365816497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4582320767334386910544331 6873481151001580365816497)
              ·
                refine ⟨5155110863251185274362373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6873481151001580365816497 5155110863251185274362373)
                ·
                  refine ⟨966583286859597238942945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5155110863251185274362373 966583286859597238942945)
                  ·
                    refine ⟨724937465144697929207209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 966583286859597238942945 724937465144697929207209)
                    ·
                      refine ⟨543703098858523446905407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 724937465144697929207209 543703098858523446905407)
                      ·
                        rfl

theorem cell23_1058858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_1058858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058858 prefixEnd_1058858 := by exact prefixLift 1058858
  have htrace : WordTrace (prefixWord ++ tailWord_1058858) baseStart_1058858 baseEnd_1058858 := by
    simpa [prefixWord, tailWord_1058858, baseEnd_1058858] using wordTrace_append hprefix tailTrace_1058858
  have hstable : (prefixWord ++ tailWord_1058858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058858).length < 2 ^ (prefixWord ++ tailWord_1058858).sum := by decide
  have hdescent : baseEnd_1058858 < baseStart_1058858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058881 : List Nat := [1, 2, 5, 1, 2, 3, 1, 1, 7]
def baseStart_1058881 : Nat := 118140960795 + 1058881 * 2 ^ 59
def prefixEnd_1058881 : Nat := 4983230072969 + 3 ^ 40 * 1058881 * 2
def baseEnd_1058881 : Nat := 60412767657064095213089

theorem tailTrace_1058881 : CollatzResearch.WordTrace tailWord_1058881 prefixEnd_1058881 60412767657064095213089 := by
  unfold tailWord_1058881
  simp only [CollatzResearch.WordTrace]
  refine ⟨38620562876862454322304497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25747041917908302881536331 38620562876862454322304497)
  ·
    refine ⟨28965422157646840741728373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38620562876862454322304497 28965422157646840741728373)
    ·
      refine ⟨2715508327279391319537035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28965422157646840741728373 2715508327279391319537035)
      ·
        refine ⟨4073262490919086979305553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2715508327279391319537035 4073262490919086979305553)
        ·
          refine ⟨3054946868189315234479165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4073262490919086979305553 3054946868189315234479165)
          ·
            refine ⟨1145605075570993212929687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3054946868189315234479165 1145605075570993212929687)
            ·
              refine ⟨1718407613356489819394531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1145605075570993212929687 1718407613356489819394531)
              ·
                refine ⟨2577611420034734729091797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1718407613356489819394531 2577611420034734729091797)
                ·
                  refine ⟨60412767657064095213089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2577611420034734729091797 60412767657064095213089)
                  ·
                    rfl

theorem cell23_1058881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 7].length) (baseStart_1058881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058881 prefixEnd_1058881 := by exact prefixLift 1058881
  have htrace : WordTrace (prefixWord ++ tailWord_1058881) baseStart_1058881 baseEnd_1058881 := by
    simpa [prefixWord, tailWord_1058881, baseEnd_1058881] using wordTrace_append hprefix tailTrace_1058881
  have hstable : (prefixWord ++ tailWord_1058881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058881).length < 2 ^ (prefixWord ++ tailWord_1058881).sum := by decide
  have hdescent : baseEnd_1058881 < baseStart_1058881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058958 : List Nat := [4, 1, 1, 3, 3, 1, 1, 2, 3, 4]
def baseStart_1058958 : Nat := 118140960795 + 1058958 * 2 ^ 59
def prefixEnd_1058958 : Nat := 4983230072969 + 3 ^ 40 * 1058958 * 2
def baseEnd_1058958 : Nat := 181251482307991018551649

theorem tailTrace_1058958 : CollatzResearch.WordTrace tailWord_1058958 prefixEnd_1058958 181251482307991018551649 := by
  unfold tailWord_1058958
  simp only [CollatzResearch.WordTrace]
  refine ⟨4827921412197937059107191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25748914198388997648571685 4827921412197937059107191)
  ·
    refine ⟨7241882118296905588660787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4827921412197937059107191 7241882118296905588660787)
    ·
      refine ⟨10862823177445358382991181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7241882118296905588660787 10862823177445358382991181)
      ·
        refine ⟨4073558691542009393621693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10862823177445358382991181 4073558691542009393621693)
        ·
          refine ⟨1527584509328253522608135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4073558691542009393621693 1527584509328253522608135)
          ·
            refine ⟨2291376763992380283912203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1527584509328253522608135 2291376763992380283912203)
            ·
              refine ⟨3437065145988570425868305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2291376763992380283912203 3437065145988570425868305)
              ·
                refine ⟨2577798859491427819401229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3437065145988570425868305 2577798859491427819401229)
                ·
                  refine ⟨966674572309285432275461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2577798859491427819401229 966674572309285432275461)
                  ·
                    refine ⟨181251482307991018551649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 966674572309285432275461 181251482307991018551649)
                    ·
                      rfl

theorem cell23_1058958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_1058958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058958 prefixEnd_1058958 := by exact prefixLift 1058958
  have htrace : WordTrace (prefixWord ++ tailWord_1058958) baseStart_1058958 baseEnd_1058958 := by
    simpa [prefixWord, tailWord_1058958, baseEnd_1058958] using wordTrace_append hprefix tailTrace_1058958
  have hstable : (prefixWord ++ tailWord_1058958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058958).length < 2 ^ (prefixWord ++ tailWord_1058958).sum := by decide
  have hdescent : baseEnd_1058958 < baseStart_1058958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058975 : List Nat := [1, 1, 2, 6, 1, 2, 2, 3, 1, 4]
def baseStart_1058975 : Nat := 118140960795 + 1058975 * 2 ^ 59
def prefixEnd_1058975 : Nat := 4983230072969 + 3 ^ 40 * 1058975 * 2
def baseEnd_1058975 : Nat := 181254392031699829714123

theorem tailTrace_1058975 : CollatzResearch.WordTrace tailWord_1058975 prefixEnd_1058975 181254392031699829714123 := by
  unfold tailWord_1058975
  simp only [CollatzResearch.WordTrace]
  refine ⟨38623991338521908376226379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25749327559014605584150919 38623991338521908376226379)
  ·
    refine ⟨57935987007782862564339569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38623991338521908376226379 57935987007782862564339569)
    ·
      refine ⟨43451990255837146923254677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57935987007782862564339569 43451990255837146923254677)
      ·
        refine ⟨2036812043242366262027563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 43451990255837146923254677 2036812043242366262027563)
        ·
          refine ⟨3055218064863549393041345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2036812043242366262027563 3055218064863549393041345)
          ·
            refine ⟨2291413548647662044781009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3055218064863549393041345 2291413548647662044781009)
            ·
              refine ⟨1718560161485746533585757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2291413548647662044781009 1718560161485746533585757)
              ·
                refine ⟨644460060557154950094659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1718560161485746533585757 644460060557154950094659)
                ·
                  refine ⟨966690090835732425141989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 644460060557154950094659 966690090835732425141989)
                  ·
                    refine ⟨181254392031699829714123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 966690090835732425141989 181254392031699829714123)
                    ·
                      rfl

theorem cell23_1058975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 3, 1, 4].length) (baseStart_1058975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058975 prefixEnd_1058975 := by exact prefixLift 1058975
  have htrace : WordTrace (prefixWord ++ tailWord_1058975) baseStart_1058975 baseEnd_1058975 := by
    simpa [prefixWord, tailWord_1058975, baseEnd_1058975] using wordTrace_append hprefix tailTrace_1058975
  have hstable : (prefixWord ++ tailWord_1058975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058975).length < 2 ^ (prefixWord ++ tailWord_1058975).sum := by decide
  have hdescent : baseEnd_1058975 < baseStart_1058975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058981 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 5, 1, 3]
def baseStart_1058981 : Nat := 118140960795 + 1058981 * 2 ^ 59
def prefixEnd_1058981 : Nat := 4983230072969 + 3 ^ 40 * 1058981 * 2
def baseEnd_1058981 : Nat := 543766256979026465667341

theorem tailTrace_1058981 : CollatzResearch.WordTrace tailWord_1058981 prefixEnd_1058981 543766256979026465667341 := by
  unfold tailWord_1058981
  simp only [CollatzResearch.WordTrace]
  refine ⟨38624210176500171400944797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25749473451000114267296531 38624210176500171400944797)
  ·
    refine ⟨14484078816187564275354299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38624210176500171400944797 14484078816187564275354299)
    ·
      refine ⟨21726118224281346413031449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14484078816187564275354299 21726118224281346413031449)
      ·
        refine ⟨16294588668211009809773587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21726118224281346413031449 16294588668211009809773587)
        ·
          refine ⟨24441883002316514714660381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16294588668211009809773587 24441883002316514714660381)
          ·
            refine ⟨9165706125868693017997643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24441883002316514714660381 9165706125868693017997643)
            ·
              refine ⟨13748559188803039526996465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9165706125868693017997643 13748559188803039526996465)
              ·
                refine ⟨10311419391602279645247349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13748559188803039526996465 10311419391602279645247349)
                ·
                  refine ⟨966695567962713716741939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10311419391602279645247349 966695567962713716741939)
                  ·
                    refine ⟨1450043351944070575112909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 966695567962713716741939 1450043351944070575112909)
                    ·
                      refine ⟨543766256979026465667341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1450043351944070575112909 543766256979026465667341)
                      ·
                        rfl

theorem cell23_1058981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_1058981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058981 prefixEnd_1058981 := by exact prefixLift 1058981
  have htrace : WordTrace (prefixWord ++ tailWord_1058981) baseStart_1058981 baseEnd_1058981 := by
    simpa [prefixWord, tailWord_1058981, baseEnd_1058981] using wordTrace_append hprefix tailTrace_1058981
  have hstable : (prefixWord ++ tailWord_1058981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058981).length < 2 ^ (prefixWord ++ tailWord_1058981).sum := by decide
  have hdescent : baseEnd_1058981 < baseStart_1058981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1058991 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 4, 3, 2]
def baseStart_1058991 : Nat := 118140960795 + 1058991 * 2 ^ 59
def prefixEnd_1058991 : Nat := 4983230072969 + 3 ^ 40 * 1058991 * 2
def baseEnd_1058991 : Nat := 543771391785571426542295

theorem tailTrace_1058991 : CollatzResearch.WordTrace tailWord_1058991 prefixEnd_1058991 543771391785571426542295 := by
  unfold tailWord_1058991
  simp only [CollatzResearch.WordTrace]
  refine ⟨38624574906463943108808827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25749716604309295405872551 38624574906463943108808827)
  ·
    refine ⟨57936862359695914663213241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38624574906463943108808827 57936862359695914663213241)
    ·
      refine ⟨43452646769771935997409931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57936862359695914663213241 43452646769771935997409931)
      ·
        refine ⟨65178970154657903996114897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43452646769771935997409931 65178970154657903996114897)
        ·
          refine ⟨48884227615993427997086173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65178970154657903996114897 48884227615993427997086173)
          ·
            refine ⟨18331585355997535498907315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48884227615993427997086173 18331585355997535498907315)
            ·
              refine ⟨27497378033996303248360973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18331585355997535498907315 27497378033996303248360973)
              ·
                refine ⟨10311516762748613718135365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27497378033996303248360973 10311516762748613718135365)
                ·
                  refine ⟨1933409393015365072150381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10311516762748613718135365 1933409393015365072150381)
                  ·
                    refine ⟨725028522380761902056393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1933409393015365072150381 725028522380761902056393)
                    ·
                      refine ⟨543771391785571426542295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 725028522380761902056393 543771391785571426542295)
                      ·
                        rfl

theorem cell23_1058991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 3, 2].length) (baseStart_1058991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1058991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1058991 prefixEnd_1058991 := by exact prefixLift 1058991
  have htrace : WordTrace (prefixWord ++ tailWord_1058991) baseStart_1058991 baseEnd_1058991 := by
    simpa [prefixWord, tailWord_1058991, baseEnd_1058991] using wordTrace_append hprefix tailTrace_1058991
  have hstable : (prefixWord ++ tailWord_1058991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1058991).length < 2 ^ (prefixWord ++ tailWord_1058991).sum := by decide
  have hdescent : baseEnd_1058991 < baseStart_1058991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1058991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059024 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 3]
def baseStart_1059024 : Nat := 118140960795 + 1059024 * 2 ^ 59
def prefixEnd_1059024 : Nat := 4983230072969 + 3 ^ 40 * 1059024 * 2
def baseEnd_1059024 : Nat := 543788336647169797429643

theorem tailTrace_1059024 : CollatzResearch.WordTrace tailWord_1059024 prefixEnd_1059024 543788336647169797429643 := by
  unfold tailWord_1059024
  simp only [CollatzResearch.WordTrace]
  refine ⟨19312889257672194872380063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25750519010229593163173417 19312889257672194872380063)
  ·
    refine ⟨28969333886508292308570095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19312889257672194872380063 28969333886508292308570095)
    ·
      refine ⟨43454000829762438462855143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28969333886508292308570095 43454000829762438462855143)
      ·
        refine ⟨65181001244643657694282715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43454000829762438462855143 65181001244643657694282715)
        ·
          refine ⟨97771501866965486541424073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65181001244643657694282715 97771501866965486541424073)
          ·
            refine ⟨73328626400224114906068055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97771501866965486541424073 73328626400224114906068055)
            ·
              refine ⟨109992939600336172359102083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73328626400224114906068055 109992939600336172359102083)
              ·
                refine ⟨164989409400504258538653125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109992939600336172359102083 164989409400504258538653125)
                ·
                  refine ⟨30935514262594548475997461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 164989409400504258538653125 30935514262594548475997461)
                  ·
                    refine ⟨1450102231059119459812381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30935514262594548475997461 1450102231059119459812381)
                    ·
                      refine ⟨543788336647169797429643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1450102231059119459812381 543788336647169797429643)
                      ·
                        rfl

theorem cell23_1059024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 3].length) (baseStart_1059024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059024 prefixEnd_1059024 := by exact prefixLift 1059024
  have htrace : WordTrace (prefixWord ++ tailWord_1059024) baseStart_1059024 baseEnd_1059024 := by
    simpa [prefixWord, tailWord_1059024, baseEnd_1059024] using wordTrace_append hprefix tailTrace_1059024
  have hstable : (prefixWord ++ tailWord_1059024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059024).length < 2 ^ (prefixWord ++ tailWord_1059024).sum := by decide
  have hdescent : baseEnd_1059024 < baseStart_1059024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059032 : List Nat := [2, 1, 2, 2, 4, 3, 1, 3, 1, 1, 3]
def baseStart_1059032 : Nat := 118140960795 + 1059032 * 2 ^ 59
def prefixEnd_1059032 : Nat := 4983230072969 + 3 ^ 40 * 1059032 * 2
def baseEnd_1059032 : Nat := 543792444492405766129607

theorem tailTrace_1059032 : CollatzResearch.WordTrace tailWord_1059032 prefixEnd_1059032 543792444492405766129607 := by
  unfold tailWord_1059032
  simp only [CollatzResearch.WordTrace]
  refine ⟨19313035149657703555525675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25750713532876938074034233 19313035149657703555525675)
  ·
    refine ⟨28969552724486555333288513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19313035149657703555525675 28969552724486555333288513)
    ·
      refine ⟨21727164543364916499966385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28969552724486555333288513 21727164543364916499966385)
      ·
        refine ⟨16295373407523687374974789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21727164543364916499966385 16295373407523687374974789)
        ·
          refine ⟨3055382513910691382807773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16295373407523687374974789 3055382513910691382807773)
          ·
            refine ⟨1145768442716509268552915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3055382513910691382807773 1145768442716509268552915)
            ·
              refine ⟨1718652664074763902829373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1145768442716509268552915 1718652664074763902829373)
              ·
                refine ⟨644494749028036463561015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1718652664074763902829373 644494749028036463561015)
                ·
                  refine ⟨966742123542054695341523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 644494749028036463561015 966742123542054695341523)
                  ·
                    refine ⟨1450113185313082043012285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 966742123542054695341523 1450113185313082043012285)
                    ·
                      refine ⟨543792444492405766129607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1450113185313082043012285 543792444492405766129607)
                      ·
                        rfl

theorem cell23_1059032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 3, 1, 1, 3].length) (baseStart_1059032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059032 prefixEnd_1059032 := by exact prefixLift 1059032
  have htrace : WordTrace (prefixWord ++ tailWord_1059032) baseStart_1059032 baseEnd_1059032 := by
    simpa [prefixWord, tailWord_1059032, baseEnd_1059032] using wordTrace_append hprefix tailTrace_1059032
  have hstable : (prefixWord ++ tailWord_1059032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059032).length < 2 ^ (prefixWord ++ tailWord_1059032).sum := by decide
  have hdescent : baseEnd_1059032 < baseStart_1059032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059041 : List Nat := [1, 2, 3, 1, 3, 1, 4, 1, 1, 1, 5]
def baseStart_1059041 : Nat := 118140960795 + 1059041 * 2 ^ 59
def prefixEnd_1059041 : Nat := 4983230072969 + 3 ^ 40 * 1059041 * 2
def baseEnd_1059041 : Nat := 543797065818296230917065

theorem tailTrace_1059041 : CollatzResearch.WordTrace tailWord_1059041 prefixEnd_1059041 543797065818296230917065 := by
  unfold tailWord_1059041
  simp only [CollatzResearch.WordTrace]
  refine ⟨38626398556282801648128977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25750932370855201098752651 38626398556282801648128977)
  ·
    refine ⟨28969798917212101236096733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38626398556282801648128977 28969798917212101236096733)
    ·
      refine ⟨10863674593954537963536275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28969798917212101236096733 10863674593954537963536275)
      ·
        refine ⟨16295511890931806945304413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10863674593954537963536275 16295511890931806945304413)
        ·
          refine ⟨6110816959099427604489155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16295511890931806945304413 6110816959099427604489155)
          ·
            refine ⟨9166225438649141406733733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6110816959099427604489155 9166225438649141406733733)
            ·
              refine ⟨1718667269746714013762575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9166225438649141406733733 1718667269746714013762575)
              ·
                refine ⟨2578000904620071020643863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1718667269746714013762575 2578000904620071020643863)
                ·
                  refine ⟨3867001356930106530965795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2578000904620071020643863 3867001356930106530965795)
                  ·
                    refine ⟨5800502035395159796448693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3867001356930106530965795 5800502035395159796448693)
                    ·
                      refine ⟨543797065818296230917065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5800502035395159796448693 543797065818296230917065)
                      ·
                        rfl

theorem cell23_1059041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_1059041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059041 prefixEnd_1059041 := by exact prefixLift 1059041
  have htrace : WordTrace (prefixWord ++ tailWord_1059041) baseStart_1059041 baseEnd_1059041 := by
    simpa [prefixWord, tailWord_1059041, baseEnd_1059041] using wordTrace_append hprefix tailTrace_1059041
  have hstable : (prefixWord ++ tailWord_1059041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059041).length < 2 ^ (prefixWord ++ tailWord_1059041).sum := by decide
  have hdescent : baseEnd_1059041 < baseStart_1059041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059055 : List Nat := [1, 1, 2, 1, 6, 1, 3, 1, 3, 2, 2]
def baseStart_1059055 : Nat := 118140960795 + 1059055 * 2 ^ 59
def prefixEnd_1059055 : Nat := 4983230072969 + 3 ^ 40 * 1059055 * 2
def baseEnd_1059055 : Nat := 543804254547459176142001

theorem tailTrace_1059055 : CollatzResearch.WordTrace tailWord_1059055 prefixEnd_1059055 543804254547459176142001 := by
  unfold tailWord_1059055
  simp only [CollatzResearch.WordTrace]
  refine ⟨38626909178232082039138619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25751272785488054692759079 38626909178232082039138619)
  ·
    refine ⟨57940363767348123058707929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38626909178232082039138619 57940363767348123058707929)
    ·
      refine ⟨43455272825511092294030947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57940363767348123058707929 43455272825511092294030947)
      ·
        refine ⟨65182909238266638441046421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43455272825511092294030947 65182909238266638441046421)
        ·
          refine ⟨3055448870543748676924051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 65182909238266638441046421 3055448870543748676924051)
          ·
            refine ⟨4583173305815623015386077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3055448870543748676924051 4583173305815623015386077)
            ·
              refine ⟨1718689989680858630769779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4583173305815623015386077 1718689989680858630769779)
              ·
                refine ⟨2578034984521287946154669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1718689989680858630769779 2578034984521287946154669)
                ·
                  refine ⟨966763119195482979808001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2578034984521287946154669 966763119195482979808001)
                  ·
                    refine ⟨725072339396612234856001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 966763119195482979808001 725072339396612234856001)
                    ·
                      refine ⟨543804254547459176142001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 725072339396612234856001 543804254547459176142001)
                      ·
                        rfl

theorem cell23_1059055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 3, 2, 2].length) (baseStart_1059055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059055 prefixEnd_1059055 := by exact prefixLift 1059055
  have htrace : WordTrace (prefixWord ++ tailWord_1059055) baseStart_1059055 baseEnd_1059055 := by
    simpa [prefixWord, tailWord_1059055, baseEnd_1059055] using wordTrace_append hprefix tailTrace_1059055
  have hstable : (prefixWord ++ tailWord_1059055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059055).length < 2 ^ (prefixWord ++ tailWord_1059055).sum := by decide
  have hdescent : baseEnd_1059055 < baseStart_1059055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059071 : List Nat := [1, 1, 2, 2, 1, 4, 2, 3, 1, 3, 3]
def baseStart_1059071 : Nat := 118140960795 + 1059071 * 2 ^ 59
def prefixEnd_1059071 : Nat := 4983230072969 + 3 ^ 40 * 1059071 * 2
def baseEnd_1059071 : Nat := 543812470237931113541927

theorem tailTrace_1059071 : CollatzResearch.WordTrace tailWord_1059071 prefixEnd_1059071 543812470237931113541927 := by
  unfold tailWord_1059071
  simp only [CollatzResearch.WordTrace]
  refine ⟨38627492746174116771721067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25751661830782744514480711 38627492746174116771721067)
  ·
    refine ⟨57941239119261175157581601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38627492746174116771721067 57941239119261175157581601)
    ·
      refine ⟨43455929339445881368186201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57941239119261175157581601 43455929339445881368186201)
      ·
        refine ⟨32591947004584411026139651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43455929339445881368186201 32591947004584411026139651)
        ·
          refine ⟨48887920506876616539209477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32591947004584411026139651 48887920506876616539209477)
          ·
            refine ⟨9166485095039365601101777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48887920506876616539209477 9166485095039365601101777)
            ·
              refine ⟨6874863821279524200826333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9166485095039365601101777 6874863821279524200826333)
              ·
                refine ⟨2578073932979821575309875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6874863821279524200826333 2578073932979821575309875)
                ·
                  refine ⟨3867110899469732362964813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2578073932979821575309875 3867110899469732362964813)
                  ·
                    refine ⟨1450166587301149636111805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3867110899469732362964813 1450166587301149636111805)
                    ·
                      refine ⟨543812470237931113541927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1450166587301149636111805 543812470237931113541927)
                      ·
                        rfl

theorem cell23_1059071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 3, 3].length) (baseStart_1059071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059071 prefixEnd_1059071 := by exact prefixLift 1059071
  have htrace : WordTrace (prefixWord ++ tailWord_1059071) baseStart_1059071 baseEnd_1059071 := by
    simpa [prefixWord, tailWord_1059071, baseEnd_1059071] using wordTrace_append hprefix tailTrace_1059071
  have hstable : (prefixWord ++ tailWord_1059071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059071).length < 2 ^ (prefixWord ++ tailWord_1059071).sum := by decide
  have hdescent : baseEnd_1059071 < baseStart_1059071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059106 : List Nat := [3, 3, 1, 1, 3, 3, 2, 2, 1, 2, 2]
def baseStart_1059106 : Nat := 118140960795 + 1059106 * 2 ^ 59
def prefixEnd_1059106 : Nat := 4983230072969 + 3 ^ 40 * 1059106 * 2
def baseEnd_1059106 : Nat := 543830442060838476604267

theorem tailTrace_1059106 : CollatzResearch.WordTrace tailWord_1059106 prefixEnd_1059106 543830442060838476604267 := by
  unfold tailWord_1059106
  simp only [CollatzResearch.WordTrace]
  refine ⟨9657192325261829437311293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25752512867364878499496781 9657192325261829437311293)
  ·
    refine ⟨3621447121973186038991735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9657192325261829437311293 3621447121973186038991735)
    ·
      refine ⟨5432170682959779058487603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3621447121973186038991735 5432170682959779058487603)
      ·
        refine ⟨8148256024439668587731405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5432170682959779058487603 8148256024439668587731405)
        ·
          refine ⟨3055596009164875720399277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8148256024439668587731405 3055596009164875720399277)
          ·
            refine ⟨1145848503436828395149729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3055596009164875720399277 1145848503436828395149729)
            ·
              refine ⟨859386377577621296362297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1145848503436828395149729 859386377577621296362297)
              ·
                refine ⟨644539783183215972271723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 859386377577621296362297 644539783183215972271723)
                ·
                  refine ⟨966809674774823958407585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 644539783183215972271723 966809674774823958407585)
                  ·
                    refine ⟨725107256081117968805689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 966809674774823958407585 725107256081117968805689)
                    ·
                      refine ⟨543830442060838476604267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 725107256081117968805689 543830442060838476604267)
                      ·
                        rfl

theorem cell23_1059106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_1059106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059106 prefixEnd_1059106 := by exact prefixLift 1059106
  have htrace : WordTrace (prefixWord ++ tailWord_1059106) baseStart_1059106 baseEnd_1059106 := by
    simpa [prefixWord, tailWord_1059106, baseEnd_1059106] using wordTrace_append hprefix tailTrace_1059106
  have hstable : (prefixWord ++ tailWord_1059106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059106).length < 2 ^ (prefixWord ++ tailWord_1059106).sum := by decide
  have hdescent : baseEnd_1059106 < baseStart_1059106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059128 : List Nat := [2, 1, 2, 1, 3, 1, 3, 3, 1, 4, 2]
def baseStart_1059128 : Nat := 118140960795 + 1059128 * 2 ^ 59
def prefixEnd_1059128 : Nat := 4983230072969 + 3 ^ 40 * 1059128 * 2
def baseEnd_1059128 : Nat := 543841738635237390529165

theorem tailTrace_1059128 : CollatzResearch.WordTrace tailWord_1059128 prefixEnd_1059128 543841738635237390529165 := by
  unfold tailWord_1059128
  simp only [CollatzResearch.WordTrace]
  refine ⟨19314785853483807753273019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25753047804645077004364025 19314785853483807753273019)
  ·
    refine ⟨28972178780225711629909529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19314785853483807753273019 28972178780225711629909529)
    ·
      refine ⟨21729134085169283722432147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28972178780225711629909529 21729134085169283722432147)
      ·
        refine ⟨32593701127753925583648221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21729134085169283722432147 32593701127753925583648221)
        ·
          refine ⟨12222637922907722093868083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32593701127753925583648221 12222637922907722093868083)
          ·
            refine ⟨18333956884361583140802125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12222637922907722093868083 18333956884361583140802125)
            ·
              refine ⟨6875233831635593677800797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18333956884361583140802125 6875233831635593677800797)
              ·
                refine ⟨2578212686863347629175299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6875233831635593677800797 2578212686863347629175299)
                ·
                  refine ⟨3867319030295021443762949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2578212686863347629175299 3867319030295021443762949)
                  ·
                    refine ⟨725122318180316520705553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3867319030295021443762949 725122318180316520705553)
                    ·
                      refine ⟨543841738635237390529165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 725122318180316520705553 543841738635237390529165)
                      ·
                        rfl

theorem cell23_1059128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 1, 4, 2].length) (baseStart_1059128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059128 prefixEnd_1059128 := by exact prefixLift 1059128
  have htrace : WordTrace (prefixWord ++ tailWord_1059128) baseStart_1059128 baseEnd_1059128 := by
    simpa [prefixWord, tailWord_1059128, baseEnd_1059128] using wordTrace_append hprefix tailTrace_1059128
  have hstable : (prefixWord ++ tailWord_1059128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059128).length < 2 ^ (prefixWord ++ tailWord_1059128).sum := by decide
  have hdescent : baseEnd_1059128 < baseStart_1059128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059168 : List Nat := [2, 1, 1, 3, 5, 1, 2, 1, 7]
def baseStart_1059168 : Nat := 118140960795 + 1059168 * 2 ^ 59
def prefixEnd_1059168 : Nat := 4983230072969 + 3 ^ 40 * 1059168 * 2
def baseEnd_1059168 : Nat := 60429141984601914892109

theorem tailTrace_1059168 : CollatzResearch.WordTrace tailWord_1059168 prefixEnd_1059168 60429141984601914892109 := by
  unfold tailWord_1059168
  simp only [CollatzResearch.WordTrace]
  refine ⟨19315515313411351169001079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25754020417881801558668105 19315515313411351169001079)
  ·
    refine ⟨28973272970117026753501619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19315515313411351169001079 28973272970117026753501619)
    ·
      refine ⟨43459909455175540130252429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28973272970117026753501619 43459909455175540130252429)
      ·
        refine ⟨16297466045690827548844661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43459909455175540130252429 16297466045690827548844661)
        ·
          refine ⟨1527887441783515082704187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16297466045690827548844661 1527887441783515082704187)
          ·
            refine ⟨2291831162675272624056281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1527887441783515082704187 2291831162675272624056281)
            ·
              refine ⟨1718873372006454468042211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2291831162675272624056281 1718873372006454468042211)
              ·
                refine ⟨2578310058009681702063317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1718873372006454468042211 2578310058009681702063317)
                ·
                  refine ⟨60429141984601914892109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2578310058009681702063317 60429141984601914892109)
                  ·
                    rfl

theorem cell23_1059168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 7].length) (baseStart_1059168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059168 prefixEnd_1059168 := by exact prefixLift 1059168
  have htrace : WordTrace (prefixWord ++ tailWord_1059168) baseStart_1059168 baseEnd_1059168 := by
    simpa [prefixWord, tailWord_1059168, baseEnd_1059168] using wordTrace_append hprefix tailTrace_1059168
  have hstable : (prefixWord ++ tailWord_1059168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059168).length < 2 ^ (prefixWord ++ tailWord_1059168).sum := by decide
  have hdescent : baseEnd_1059168 < baseStart_1059168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059181 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 3, 7]
def baseStart_1059181 : Nat := 118140960795 + 1059181 * 2 ^ 59
def prefixEnd_1059181 : Nat := 4983230072969 + 3 ^ 40 * 1059181 * 2
def baseEnd_1059181 : Nat := 181289651036641894388807

theorem tailTrace_1059181 : CollatzResearch.WordTrace tailWord_1059181 prefixEnd_1059181 181289651036641894388807 := by
  unfold tailWord_1059181
  simp only [CollatzResearch.WordTrace]
  refine ⟨38631504775775605558225397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25754336517183737038816931 38631504775775605558225397)
  ·
    refine ⟨3621703572728963021083631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38631504775775605558225397 3621703572728963021083631)
    ·
      refine ⟨5432555359093444531625447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3621703572728963021083631 5432555359093444531625447)
      ·
        refine ⟨8148833038640166797438171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5432555359093444531625447 8148833038640166797438171)
        ·
          refine ⟨12223249557960250196157257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8148833038640166797438171 12223249557960250196157257)
          ·
            refine ⟨9167437168470187647117943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12223249557960250196157257 9167437168470187647117943)
            ·
              refine ⟨13751155752705281470676915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9167437168470187647117943 13751155752705281470676915)
              ·
                refine ⟨20626733629057922206015373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13751155752705281470676915 20626733629057922206015373)
                ·
                  refine ⟨7735025110896720827255765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20626733629057922206015373 7735025110896720827255765)
                  ·
                    refine ⟨181289651036641894388807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7735025110896720827255765 181289651036641894388807)
                    ·
                      rfl

theorem cell23_1059181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_1059181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059181 prefixEnd_1059181 := by exact prefixLift 1059181
  have htrace : WordTrace (prefixWord ++ tailWord_1059181) baseStart_1059181 baseEnd_1059181 := by
    simpa [prefixWord, tailWord_1059181, baseEnd_1059181] using wordTrace_append hprefix tailTrace_1059181
  have hstable : (prefixWord ++ tailWord_1059181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059181).length < 2 ^ (prefixWord ++ tailWord_1059181).sum := by decide
  have hdescent : baseEnd_1059181 < baseStart_1059181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059255 : List Nat := [1, 1, 3, 1, 3, 4, 2, 1, 2, 2, 3]
def baseStart_1059255 : Nat := 118140960795 + 1059255 * 2 ^ 59
def prefixEnd_1059255 : Nat := 4983230072969 + 3 ^ 40 * 1059255 * 2
def baseEnd_1059255 : Nat := 543906950678358393641081

theorem tailTrace_1059255 : CollatzResearch.WordTrace tailWord_1059255 prefixEnd_1059255 543906950678358393641081 := by
  unfold tailWord_1059255
  simp only [CollatzResearch.WordTrace]
  refine ⟨38634203777507516196419219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25756135851671677464279479 38634203777507516196419219)
  ·
    refine ⟨57951305666261274294628829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38634203777507516196419219 57951305666261274294628829)
    ·
      refine ⟨21731739624847977860485811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57951305666261274294628829 21731739624847977860485811)
      ·
        refine ⟨32597609437271966790728717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21731739624847977860485811 32597609437271966790728717)
        ·
          refine ⟨12224103538976987546523269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32597609437271966790728717 12224103538976987546523269)
          ·
            refine ⟨2292019413558185164973113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12224103538976987546523269 2292019413558185164973113)
            ·
              refine ⟨1719014560168638873729835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2292019413558185164973113 1719014560168638873729835)
              ·
                refine ⟨2578521840252958310594753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1719014560168638873729835 2578521840252958310594753)
                ·
                  refine ⟨1933891380189718732946065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2578521840252958310594753 1933891380189718732946065)
                  ·
                    refine ⟨1450418535142289049709549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1933891380189718732946065 1450418535142289049709549)
                    ·
                      refine ⟨543906950678358393641081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1450418535142289049709549 543906950678358393641081)
                      ·
                        rfl

theorem cell23_1059255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 2, 3].length) (baseStart_1059255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059255 prefixEnd_1059255 := by exact prefixLift 1059255
  have htrace : WordTrace (prefixWord ++ tailWord_1059255) baseStart_1059255 baseEnd_1059255 := by
    simpa [prefixWord, tailWord_1059255, baseEnd_1059255] using wordTrace_append hprefix tailTrace_1059255
  have hstable : (prefixWord ++ tailWord_1059255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059255).length < 2 ^ (prefixWord ++ tailWord_1059255).sum := by decide
  have hdescent : baseEnd_1059255 < baseStart_1059255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059281 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 2, 4, 5]
def baseStart_1059281 : Nat := 118140960795 + 1059281 * 2 ^ 59
def prefixEnd_1059281 : Nat := 4983230072969 + 3 ^ 40 * 1059281 * 2
def baseEnd_1059281 : Nat := 543920301175375291915961

theorem tailTrace_1059281 : CollatzResearch.WordTrace tailWord_1059281 prefixEnd_1059281 543920301175375291915961 := by
  unfold tailWord_1059281
  simp only [CollatzResearch.WordTrace]
  refine ⟨38635152075413322636865697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25756768050275548424577131 38635152075413322636865697)
  ·
    refine ⟨28976364056559991977649273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38635152075413322636865697 28976364056559991977649273)
    ·
      refine ⟨21732273042419993983236955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28976364056559991977649273 21732273042419993983236955)
      ·
        refine ⟨32598409563629990974855433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21732273042419993983236955 32598409563629990974855433)
        ·
          refine ⟨24448807172722493231141575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32598409563629990974855433 24448807172722493231141575)
          ·
            refine ⟨36673210759083739846712363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24448807172722493231141575 36673210759083739846712363)
            ·
              refine ⟨55009816138625609770068545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36673210759083739846712363 55009816138625609770068545)
              ·
                refine ⟨41257362103969207327551409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55009816138625609770068545 41257362103969207327551409)
                ·
                  refine ⟨30943021577976905495663557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41257362103969207327551409 30943021577976905495663557)
                  ·
                    refine ⟨5801816545870669780436917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30943021577976905495663557 5801816545870669780436917)
                    ·
                      refine ⟨543920301175375291915961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5801816545870669780436917 543920301175375291915961)
                      ·
                        rfl

theorem cell23_1059281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_1059281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059281 prefixEnd_1059281 := by exact prefixLift 1059281
  have htrace : WordTrace (prefixWord ++ tailWord_1059281) baseStart_1059281 baseEnd_1059281 := by
    simpa [prefixWord, tailWord_1059281, baseEnd_1059281] using wordTrace_append hprefix tailTrace_1059281
  have hstable : (prefixWord ++ tailWord_1059281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059281).length < 2 ^ (prefixWord ++ tailWord_1059281).sum := by decide
  have hdescent : baseEnd_1059281 < baseStart_1059281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059308 : List Nat := [2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 4]
def baseStart_1059308 : Nat := 118140960795 + 1059308 * 2 ^ 59
def prefixEnd_1059308 : Nat := 4983230072969 + 3 ^ 40 * 1059308 * 2
def baseEnd_1059308 : Nat := 543934165153046686278337

theorem tailTrace_1059308 : CollatzResearch.WordTrace tailWord_1059308 prefixEnd_1059308 543934165153046686278337 := by
  unfold tailWord_1059308
  simp only [CollatzResearch.WordTrace]
  refine ⟨19318068423157753124049289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25757424564210337498732385 19318068423157753124049289)
  ·
    refine ⟨14488551317368314843036967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19318068423157753124049289 14488551317368314843036967)
    ·
      refine ⟨21732826976052472264555451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14488551317368314843036967 21732826976052472264555451)
      ·
        refine ⟨32599240464078708396833177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21732826976052472264555451 32599240464078708396833177)
        ·
          refine ⟨24449430348059031297624883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32599240464078708396833177 24449430348059031297624883)
          ·
            refine ⟨36674145522088546946437325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24449430348059031297624883 36674145522088546946437325)
            ·
              refine ⟨13752804570783205104913997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36674145522088546946437325 13752804570783205104913997)
              ·
                refine ⟨5157301714043701914342749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13752804570783205104913997 5157301714043701914342749)
                ·
                  refine ⟨1933988142766388217878531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5157301714043701914342749 1933988142766388217878531)
                  ·
                    refine ⟨2900982214149582326817797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1933988142766388217878531 2900982214149582326817797)
                    ·
                      refine ⟨543934165153046686278337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2900982214149582326817797 543934165153046686278337)
                      ·
                        rfl

theorem cell23_1059308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_1059308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059308 prefixEnd_1059308 := by exact prefixLift 1059308
  have htrace : WordTrace (prefixWord ++ tailWord_1059308) baseStart_1059308 baseEnd_1059308 := by
    simpa [prefixWord, tailWord_1059308, baseEnd_1059308] using wordTrace_append hprefix tailTrace_1059308
  have hstable : (prefixWord ++ tailWord_1059308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059308).length < 2 ^ (prefixWord ++ tailWord_1059308).sum := by decide
  have hdescent : baseEnd_1059308 < baseStart_1059308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059325 : List Nat := [1, 4, 1, 1, 1, 3, 3, 3, 1, 1, 4]
def baseStart_1059325 : Nat := 118140960795 + 1059325 * 2 ^ 59
def prefixEnd_1059325 : Nat := 4983230072969 + 3 ^ 40 * 1059325 * 2
def baseEnd_1059325 : Nat := 543942894324173119765759

theorem tailTrace_1059325 : CollatzResearch.WordTrace tailWord_1059325 prefixEnd_1059325 543942894324173119765759 := by
  unfold tailWord_1059325
  simp only [CollatzResearch.WordTrace]
  refine ⟨38636756887253918151467429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25757837924835945434311619 38636756887253918151467429)
  ·
    refine ⟨7244391916360109653400143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38636756887253918151467429 7244391916360109653400143)
    ·
      refine ⟨10866587874540164480100215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7244391916360109653400143 10866587874540164480100215)
      ·
        refine ⟨16299881811810246720150323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10866587874540164480100215 16299881811810246720150323)
        ·
          refine ⟨24449822717715370080225485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16299881811810246720150323 24449822717715370080225485)
          ·
            refine ⟨9168683519143263780084557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24449822717715370080225485 9168683519143263780084557)
            ·
              refine ⟨3438256319678723917531709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9168683519143263780084557 3438256319678723917531709)
              ·
                refine ⟨1289346119879521469074391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3438256319678723917531709 1289346119879521469074391)
                ·
                  refine ⟨1934019179819282203611587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1289346119879521469074391 1934019179819282203611587)
                  ·
                    refine ⟨2901028769728923305417381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1934019179819282203611587 2901028769728923305417381)
                    ·
                      refine ⟨543942894324173119765759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2901028769728923305417381 543942894324173119765759)
                      ·
                        rfl

theorem cell23_1059325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_1059325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059325 prefixEnd_1059325 := by exact prefixLift 1059325
  have htrace : WordTrace (prefixWord ++ tailWord_1059325) baseStart_1059325 baseEnd_1059325 := by
    simpa [prefixWord, tailWord_1059325, baseEnd_1059325] using wordTrace_append hprefix tailTrace_1059325
  have hstable : (prefixWord ++ tailWord_1059325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059325).length < 2 ^ (prefixWord ++ tailWord_1059325).sum := by decide
  have hdescent : baseEnd_1059325 < baseStart_1059325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059331 : List Nat := [1, 1, 1, 3, 2, 1, 14]
def baseStart_1059331 : Nat := 118140960795 + 1059331 * 2 ^ 59
def prefixEnd_1059331 : Nat := 4983230072969 + 3 ^ 40 * 1059331 * 2
def baseEnd_1059331 : Nat := 6715382409976544398651

theorem tailTrace_1059331 : CollatzResearch.WordTrace tailWord_1059331 prefixEnd_1059331 6715382409976544398651 := by
  unfold tailWord_1059331
  simp only [CollatzResearch.WordTrace]
  refine ⟨38636975725232181176185847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25757983816821454117457231 38636975725232181176185847)
  ·
    refine ⟨57955463587848271764278771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38636975725232181176185847 57955463587848271764278771)
    ·
      refine ⟨86933195381772407646418157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57955463587848271764278771 86933195381772407646418157)
      ·
        refine ⟨32599948268164652867406809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86933195381772407646418157 32599948268164652867406809)
        ·
          refine ⟨24449961201123489650555107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32599948268164652867406809 24449961201123489650555107)
          ·
            refine ⟨36674941801685234475832661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24449961201123489650555107 36674941801685234475832661)
            ·
              refine ⟨6715382409976544398651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 36674941801685234475832661 6715382409976544398651)
              ·
                rfl

theorem cell23_1059331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 14].length) (baseStart_1059331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059331 prefixEnd_1059331 := by exact prefixLift 1059331
  have htrace : WordTrace (prefixWord ++ tailWord_1059331) baseStart_1059331 baseEnd_1059331 := by
    simpa [prefixWord, tailWord_1059331, baseEnd_1059331] using wordTrace_append hprefix tailTrace_1059331
  have hstable : (prefixWord ++ tailWord_1059331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059331).length < 2 ^ (prefixWord ++ tailWord_1059331).sum := by decide
  have hdescent : baseEnd_1059331 < baseStart_1059331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059338 : List Nat := [3, 1, 2, 2, 2, 1, 2, 2, 1, 1, 6]
def baseStart_1059338 : Nat := 118140960795 + 1059338 * 2 ^ 59
def prefixEnd_1059338 : Nat := 4983230072969 + 3 ^ 40 * 1059338 * 2
def baseEnd_1059338 : Nat := 543949569572681568903199

theorem tailTrace_1059338 : CollatzResearch.WordTrace tailWord_1059338 prefixEnd_1059338 543949569572681568903199 := by
  unfold tailWord_1059338
  simp only [CollatzResearch.WordTrace]
  refine ⟨9659307759051705342922667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25758154024137880914460445 9659307759051705342922667)
  ·
    refine ⟨14488961638577558014384001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9659307759051705342922667 14488961638577558014384001)
    ·
      refine ⟨10866721228933168510788001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14488961638577558014384001 10866721228933168510788001)
      ·
        refine ⟨8150040921699876383091001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10866721228933168510788001 8150040921699876383091001)
        ·
          refine ⟨6112530691274907287318251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8150040921699876383091001 6112530691274907287318251)
          ·
            refine ⟨9168796036912360930977377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6112530691274907287318251 9168796036912360930977377)
            ·
              refine ⟨6876597027684270698233033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9168796036912360930977377 6876597027684270698233033)
              ·
                refine ⟨5157447770763203023674775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6876597027684270698233033 5157447770763203023674775)
                ·
                  refine ⟨7736171656144804535512163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5157447770763203023674775 7736171656144804535512163)
                  ·
                    refine ⟨11604257484217206803268245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7736171656144804535512163 11604257484217206803268245)
                    ·
                      refine ⟨543949569572681568903199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11604257484217206803268245 543949569572681568903199)
                      ·
                        rfl

theorem cell23_1059338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_1059338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059338 prefixEnd_1059338 := by exact prefixLift 1059338
  have htrace : WordTrace (prefixWord ++ tailWord_1059338) baseStart_1059338 baseEnd_1059338 := by
    simpa [prefixWord, tailWord_1059338, baseEnd_1059338] using wordTrace_append hprefix tailTrace_1059338
  have hstable : (prefixWord ++ tailWord_1059338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059338).length < 2 ^ (prefixWord ++ tailWord_1059338).sum := by decide
  have hdescent : baseEnd_1059338 < baseStart_1059338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059393 : List Nat := [1, 2, 5, 1, 1, 3, 3, 2, 1, 2, 2]
def baseStart_1059393 : Nat := 118140960795 + 1059393 * 2 ^ 59
def prefixEnd_1059393 : Nat := 4983230072969 + 3 ^ 40 * 1059393 * 2
def baseEnd_1059393 : Nat := 543977811008678853715447

theorem tailTrace_1059393 : CollatzResearch.WordTrace tailWord_1059393 prefixEnd_1059393 543977811008678853715447 := by
  unfold tailWord_1059393
  simp only [CollatzResearch.WordTrace]
  refine ⟨38639237051007565764942833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25759491367338377176628555 38639237051007565764942833)
  ·
    refine ⟨28979427788255674323707125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38639237051007565764942833 28979427788255674323707125)
    ·
      refine ⟨2716821355148969467847543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28979427788255674323707125 2716821355148969467847543)
      ·
        refine ⟨4075232032723454201771315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2716821355148969467847543 4075232032723454201771315)
        ·
          refine ⟨6112848049085181302656973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4075232032723454201771315 6112848049085181302656973)
          ·
            refine ⟨2292318018406942988496365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6112848049085181302656973 2292318018406942988496365)
            ·
              refine ⟨859619256902603620686137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2292318018406942988496365 859619256902603620686137)
              ·
                refine ⟨644714442676952715514603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 859619256902603620686137 644714442676952715514603)
                ·
                  refine ⟨967071664015429073271905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 644714442676952715514603 967071664015429073271905)
                  ·
                    refine ⟨725303748011571804953929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 967071664015429073271905 725303748011571804953929)
                    ·
                      refine ⟨543977811008678853715447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 725303748011571804953929 543977811008678853715447)
                      ·
                        rfl

theorem cell23_1059393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_1059393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059393 prefixEnd_1059393 := by exact prefixLift 1059393
  have htrace : WordTrace (prefixWord ++ tailWord_1059393) baseStart_1059393 baseEnd_1059393 := by
    simpa [prefixWord, tailWord_1059393, baseEnd_1059393] using wordTrace_append hprefix tailTrace_1059393
  have hstable : (prefixWord ++ tailWord_1059393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059393).length < 2 ^ (prefixWord ++ tailWord_1059393).sum := by decide
  have hdescent : baseEnd_1059393 < baseStart_1059393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059409 : List Nat := [1, 2, 2, 1, 3, 3, 4, 1, 2, 1, 3]
def baseStart_1059409 : Nat := 118140960795 + 1059409 * 2 ^ 59
def prefixEnd_1059409 : Nat := 4983230072969 + 3 ^ 40 * 1059409 * 2
def baseEnd_1059409 : Nat := 543986026699150791115373

theorem tailTrace_1059409 : CollatzResearch.WordTrace tailWord_1059409 prefixEnd_1059409 543986026699150791115373 := by
  unfold tailWord_1059409
  simp only [CollatzResearch.WordTrace]
  refine ⟨38639820618949600497525281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25759880412633066998350187 38639820618949600497525281)
  ·
    refine ⟨28979865464212200373143961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38639820618949600497525281 28979865464212200373143961)
    ·
      refine ⟨21734899098159150279857971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28979865464212200373143961 21734899098159150279857971)
      ·
        refine ⟨32602348647238725419786957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21734899098159150279857971 32602348647238725419786957)
        ·
          refine ⟨12225880742714522032420109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32602348647238725419786957 12225880742714522032420109)
          ·
            refine ⟨4584705278517945762157541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12225880742714522032420109 4584705278517945762157541)
            ·
              refine ⟨859632239722114830404539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4584705278517945762157541 859632239722114830404539)
              ·
                refine ⟨1289448359583172245606809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 859632239722114830404539 1289448359583172245606809)
                ·
                  refine ⟨967086269687379184205107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1289448359583172245606809 967086269687379184205107)
                  ·
                    refine ⟨1450629404531068776307661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 967086269687379184205107 1450629404531068776307661)
                    ·
                      refine ⟨543986026699150791115373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1450629404531068776307661 543986026699150791115373)
                      ·
                        rfl

theorem cell23_1059409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 2, 1, 3].length) (baseStart_1059409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059409 prefixEnd_1059409 := by exact prefixLift 1059409
  have htrace : WordTrace (prefixWord ++ tailWord_1059409) baseStart_1059409 baseEnd_1059409 := by
    simpa [prefixWord, tailWord_1059409, baseEnd_1059409] using wordTrace_append hprefix tailTrace_1059409
  have hstable : (prefixWord ++ tailWord_1059409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059409).length < 2 ^ (prefixWord ++ tailWord_1059409).sum := by decide
  have hdescent : baseEnd_1059409 < baseStart_1059409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
