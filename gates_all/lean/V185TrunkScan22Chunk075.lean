import V185TrunkScan22Chunk074

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_673905 : List Nat := [1, 2, 2, 2, 1, 1, 6, 3, 1, 3]
def baseStart_673905 : Nat := 118140960795 + 673905 * 2 ^ 59
def prefixEnd_673905 : Nat := 4983230072969 + 3 ^ 40 * 673905 * 2
def baseEnd_673905 : Nat := 230691453645527384858849

theorem tailTrace_673905 : CollatzResearch.WordTrace tailWord_673905 prefixEnd_673905 230691453645527384858849 := by
  unfold tailWord_673905
  simp only [CollatzResearch.WordTrace]
  refine ⟨24579334623564753656023169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16386223082376502437348779 24579334623564753656023169)
  ·
    refine ⟨18434500967673565242017377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24579334623564753656023169 18434500967673565242017377)
    ·
      refine ⟨13825875725755173931513033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18434500967673565242017377 13825875725755173931513033)
      ·
        refine ⟨10369406794316380448634775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13825875725755173931513033 10369406794316380448634775)
        ·
          refine ⟨15554110191474570672952163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10369406794316380448634775 15554110191474570672952163)
          ·
            refine ⟨23331165287211856009428245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15554110191474570672952163 23331165287211856009428245)
            ·
              refine ⟨1093648372838055750441949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23331165287211856009428245 1093648372838055750441949)
              ·
                refine ⟨410118139814270906415731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1093648372838055750441949 410118139814270906415731)
                ·
                  refine ⟨615177209721406359623597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 410118139814270906415731 615177209721406359623597)
                  ·
                    refine ⟨230691453645527384858849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 615177209721406359623597 230691453645527384858849)
                    ·
                      rfl

theorem cell22_673905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 3, 1, 3].length) (baseStart_673905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673905 prefixEnd_673905 := by exact prefixLift 673905
  have htrace : WordTrace (prefixWord ++ tailWord_673905) baseStart_673905 baseEnd_673905 := by
    simpa [prefixWord, tailWord_673905, baseEnd_673905] using wordTrace_append hprefix tailTrace_673905
  have hstable : (prefixWord ++ tailWord_673905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673905).length < 2 ^ (prefixWord ++ tailWord_673905).sum := by decide
  have hdescent : baseEnd_673905 < baseStart_673905 := by decide
  rcases family_descends (prefixWord ++ tailWord_673905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673916 : List Nat := [2, 2, 2, 1, 1, 4, 1, 2, 2, 5]
def baseStart_673916 : Nat := 118140960795 + 673916 * 2 ^ 59
def prefixEnd_673916 : Nat := 4983230072969 + 3 ^ 40 * 673916 * 2
def baseEnd_673916 : Nat := 230695219170327022833815

theorem tailTrace_673916 : CollatzResearch.WordTrace tailWord_673916 prefixEnd_673916 230695219170327022833815 := by
  unfold tailWord_673916
  simp only [CollatzResearch.WordTrace]
  refine ⟨12289867913262451267336801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16386490551016601689782401 12289867913262451267336801)
  ·
    refine ⟨9217400934946838450502601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12289867913262451267336801 9217400934946838450502601)
    ·
      refine ⟨6913050701210128837876951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9217400934946838450502601 6913050701210128837876951)
      ·
        refine ⟨10369576051815193256815427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6913050701210128837876951 10369576051815193256815427)
        ·
          refine ⟨15554364077722789885223141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10369576051815193256815427 15554364077722789885223141)
          ·
            refine ⟨2916443264573023103479339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15554364077722789885223141 2916443264573023103479339)
            ·
              refine ⟨4374664896859534655219009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2916443264573023103479339 4374664896859534655219009)
              ·
                refine ⟨3280998672644650991414257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4374664896859534655219009 3280998672644650991414257)
                ·
                  refine ⟨2460749004483488243560693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3280998672644650991414257 2460749004483488243560693)
                  ·
                    refine ⟨230695219170327022833815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2460749004483488243560693 230695219170327022833815)
                    ·
                      rfl

theorem cell22_673916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_673916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673916 prefixEnd_673916 := by exact prefixLift 673916
  have htrace : WordTrace (prefixWord ++ tailWord_673916) baseStart_673916 baseEnd_673916 := by
    simpa [prefixWord, tailWord_673916, baseEnd_673916] using wordTrace_append hprefix tailTrace_673916
  have hstable : (prefixWord ++ tailWord_673916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673916).length < 2 ^ (prefixWord ++ tailWord_673916).sum := by decide
  have hdescent : baseEnd_673916 < baseStart_673916 := by decide
  rcases family_descends (prefixWord ++ tailWord_673916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673965 : List Nat := [1, 5, 2, 1, 2, 1, 2, 3, 1, 4]
def baseStart_673965 : Nat := 118140960795 + 673965 * 2 ^ 59
def prefixEnd_673965 : Nat := 4983230072969 + 3 ^ 40 * 673965 * 2
def baseEnd_673965 : Nat := 230711992871707228358665

theorem tailTrace_673965 : CollatzResearch.WordTrace tailWord_673965 prefixEnd_673965 230711992871707228358665 := by
  unfold tailWord_673965
  simp only [CollatzResearch.WordTrace]
  refine ⟨24581523003347383903207349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16387682002231589268804899 24581523003347383903207349)
  ·
    refine ⟨2304517781563817240925689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24581523003347383903207349 2304517781563817240925689)
    ·
      refine ⟨1728388336172862930694267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2304517781563817240925689 1728388336172862930694267)
      ·
        refine ⟨2592582504259294396041401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1728388336172862930694267 2592582504259294396041401)
        ·
          refine ⟨1944436878194470797031051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2592582504259294396041401 1944436878194470797031051)
          ·
            refine ⟨2916655317291706195546577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1944436878194470797031051 2916655317291706195546577)
            ·
              refine ⟨2187491487968779646659933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2916655317291706195546577 2187491487968779646659933)
              ·
                refine ⟨820309307988292367497475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2187491487968779646659933 820309307988292367497475)
                ·
                  refine ⟨1230463961982438551246213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 820309307988292367497475 1230463961982438551246213)
                  ·
                    refine ⟨230711992871707228358665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1230463961982438551246213 230711992871707228358665)
                    ·
                      rfl

theorem cell22_673965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_673965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673965 prefixEnd_673965 := by exact prefixLift 673965
  have htrace : WordTrace (prefixWord ++ tailWord_673965) baseStart_673965 baseEnd_673965 := by
    simpa [prefixWord, tailWord_673965, baseEnd_673965] using wordTrace_append hprefix tailTrace_673965
  have hstable : (prefixWord ++ tailWord_673965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673965).length < 2 ^ (prefixWord ++ tailWord_673965).sum := by decide
  have hdescent : baseEnd_673965 < baseStart_673965 := by decide
  rcases family_descends (prefixWord ++ tailWord_673965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673978 : List Nat := [3, 1, 1, 1, 2, 2, 4, 1, 4, 3]
def baseStart_673978 : Nat := 118140960795 + 673978 * 2 ^ 59
def prefixEnd_673978 : Nat := 4983230072969 + 3 ^ 40 * 673978 * 2
def baseEnd_673978 : Nat := 230716443037379527783625

theorem tailTrace_673978 : CollatzResearch.WordTrace tailWord_673978 prefixEnd_673978 230716443037379527783625 := by
  unfold tailWord_673978
  simp only [CollatzResearch.WordTrace]
  refine ⟨6145499288075071780857647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16387998101533524748953725 6145499288075071780857647)
  ·
    refine ⟨9218248932112607671286471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6145499288075071780857647 9218248932112607671286471)
    ·
      refine ⟨13827373398168911506929707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9218248932112607671286471 13827373398168911506929707)
      ·
        refine ⟨20741060097253367260394561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13827373398168911506929707 20741060097253367260394561)
        ·
          refine ⟨15555795072940025445295921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20741060097253367260394561 15555795072940025445295921)
          ·
            refine ⟨11666846304705019083971941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15555795072940025445295921 11666846304705019083971941)
            ·
              refine ⟨2187533682132191078244739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11666846304705019083971941 2187533682132191078244739)
              ·
                refine ⟨3281300523198286617367109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2187533682132191078244739 3281300523198286617367109)
                ·
                  refine ⟨615243848099678740756333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3281300523198286617367109 615243848099678740756333)
                  ·
                    refine ⟨230716443037379527783625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 615243848099678740756333 230716443037379527783625)
                    ·
                      rfl

theorem cell22_673978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 4, 3].length) (baseStart_673978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673978 prefixEnd_673978 := by exact prefixLift 673978
  have htrace : WordTrace (prefixWord ++ tailWord_673978) baseStart_673978 baseEnd_673978 := by
    simpa [prefixWord, tailWord_673978, baseEnd_673978] using wordTrace_append hprefix tailTrace_673978
  have hstable : (prefixWord ++ tailWord_673978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673978).length < 2 ^ (prefixWord ++ tailWord_673978).sum := by decide
  have hdescent : baseEnd_673978 < baseStart_673978 := by decide
  rcases family_descends (prefixWord ++ tailWord_673978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673980 : List Nat := [2, 2, 2, 3, 3, 2, 1, 1, 6]
def baseStart_673980 : Nat := 118140960795 + 673980 * 2 ^ 59
def prefixEnd_673980 : Nat := 4983230072969 + 3 ^ 40 * 673980 * 2
def baseEnd_673980 : Nat := 76905709226084063077873

theorem tailTrace_673980 : CollatzResearch.WordTrace tailWord_673980 prefixEnd_673980 76905709226084063077873 := by
  unfold tailWord_673980
  simp only [CollatzResearch.WordTrace]
  refine ⟨12291035049146520732501697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16388046732195360976668929 12291035049146520732501697)
  ·
    refine ⟨9218276286859890549376273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12291035049146520732501697 9218276286859890549376273)
    ·
      refine ⟨6913707215144917912032205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9218276286859890549376273 6913707215144917912032205)
      ·
        refine ⟨2592640205679344217012077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6913707215144917912032205 2592640205679344217012077)
        ·
          refine ⟨972240077129754081379529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2592640205679344217012077 972240077129754081379529)
          ·
            refine ⟨729180057847315561034647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 972240077129754081379529 729180057847315561034647)
            ·
              refine ⟨1093770086770973341551971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 729180057847315561034647 1093770086770973341551971)
              ·
                refine ⟨1640655130156460012327957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1093770086770973341551971 1640655130156460012327957)
                ·
                  refine ⟨76905709226084063077873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1640655130156460012327957 76905709226084063077873)
                  ·
                    rfl

theorem cell22_673980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 6].length) (baseStart_673980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673980 prefixEnd_673980 := by exact prefixLift 673980
  have htrace : WordTrace (prefixWord ++ tailWord_673980) baseStart_673980 baseEnd_673980 := by
    simpa [prefixWord, tailWord_673980, baseEnd_673980] using wordTrace_append hprefix tailTrace_673980
  have hstable : (prefixWord ++ tailWord_673980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673980).length < 2 ^ (prefixWord ++ tailWord_673980).sum := by decide
  have hdescent : baseEnd_673980 < baseStart_673980 := by decide
  rcases family_descends (prefixWord ++ tailWord_673980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674012 : List Nat := [2, 2, 5, 2, 1, 1, 1, 2, 1, 5]
def baseStart_674012 : Nat := 118140960795 + 674012 * 2 ^ 59
def prefixEnd_674012 : Nat := 4983230072969 + 3 ^ 40 * 674012 * 2
def baseEnd_674012 : Nat := 230728081932214772433521

theorem tailTrace_674012 : CollatzResearch.WordTrace tailWord_674012 prefixEnd_674012 230728081932214772433521 := by
  unfold tailWord_674012
  simp only [CollatzResearch.WordTrace]
  refine ⟨12291618617088555465084145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16388824822784740620112193 12291618617088555465084145)
  ·
    refine ⟨9218713962816416598813109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12291618617088555465084145 9218713962816416598813109)
    ·
      refine ⟨864254434014039056138729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9218713962816416598813109 864254434014039056138729)
      ·
        refine ⟨648190825510529292104047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 864254434014039056138729 648190825510529292104047)
        ·
          refine ⟨972286238265793938156071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 648190825510529292104047 972286238265793938156071)
          ·
            refine ⟨1458429357398690907234107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 972286238265793938156071 1458429357398690907234107)
            ·
              refine ⟨2187644036098036360851161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1458429357398690907234107 2187644036098036360851161)
              ·
                refine ⟨1640733027073527270638371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2187644036098036360851161 1640733027073527270638371)
                ·
                  refine ⟨2461099540610290905957557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1640733027073527270638371 2461099540610290905957557)
                  ·
                    refine ⟨230728081932214772433521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2461099540610290905957557 230728081932214772433521)
                    ·
                      rfl

theorem cell22_674012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_674012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_674012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_674012 prefixEnd_674012 := by exact prefixLift 674012
  have htrace : WordTrace (prefixWord ++ tailWord_674012) baseStart_674012 baseEnd_674012 := by
    simpa [prefixWord, tailWord_674012, baseEnd_674012] using wordTrace_append hprefix tailTrace_674012
  have hstable : (prefixWord ++ tailWord_674012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674012).length < 2 ^ (prefixWord ++ tailWord_674012).sum := by decide
  have hdescent : baseEnd_674012 < baseStart_674012 := by decide
  rcases family_descends (prefixWord ++ tailWord_674012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674038 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 2, 6]
def baseStart_674038 : Nat := 118140960795 + 674038 * 2 ^ 59
def prefixEnd_674038 : Nat := 4983230072969 + 3 ^ 40 * 674038 * 2
def baseEnd_674038 : Nat := 230736982263559371283441

theorem tailTrace_674038 : CollatzResearch.WordTrace tailWord_674038 prefixEnd_674038 230736982263559371283441 := by
  unfold tailWord_674038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1536511595755182335663423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16389457021388611580409845 1536511595755182335663423)
  ·
    refine ⟨2304767393632773503495135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1536511595755182335663423 2304767393632773503495135)
    ·
      refine ⟨3457151090449160255242703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2304767393632773503495135 3457151090449160255242703)
      ·
        refine ⟨5185726635673740382864055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3457151090449160255242703 5185726635673740382864055)
        ·
          refine ⟨7778589953510610574296083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5185726635673740382864055 7778589953510610574296083)
          ·
            refine ⟨11667884930265915861444125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7778589953510610574296083 11667884930265915861444125)
            ·
              refine ⟨4375456848849718448041547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11667884930265915861444125 4375456848849718448041547)
              ·
                refine ⟨6563185273274577672062321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4375456848849718448041547 6563185273274577672062321)
                ·
                  refine ⟨4922388954955933254046741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6563185273274577672062321 4922388954955933254046741)
                  ·
                    refine ⟨230736982263559371283441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4922388954955933254046741 230736982263559371283441)
                    ·
                      rfl

theorem cell22_674038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_674038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_674038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_674038 prefixEnd_674038 := by exact prefixLift 674038
  have htrace : WordTrace (prefixWord ++ tailWord_674038) baseStart_674038 baseEnd_674038 := by
    simpa [prefixWord, tailWord_674038, baseEnd_674038] using wordTrace_append hprefix tailTrace_674038
  have hstable : (prefixWord ++ tailWord_674038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674038).length < 2 ^ (prefixWord ++ tailWord_674038).sum := by decide
  have hdescent : baseEnd_674038 < baseStart_674038 := by decide
  rcases family_descends (prefixWord ++ tailWord_674038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674074 : List Nat := [3, 1, 1, 3, 4, 1, 2, 3, 1, 3]
def baseStart_674074 : Nat := 118140960795 + 674074 * 2 ^ 59
def prefixEnd_674074 : Nat := 4983230072969 + 3 ^ 40 * 674074 * 2
def baseEnd_674074 : Nat := 230749305799267277383331

theorem tailTrace_674074 : CollatzResearch.WordTrace tailWord_674074 prefixEnd_674074 230749305799267277383331 := by
  unfold tailWord_674074
  simp only [CollatzResearch.WordTrace]
  refine ⟨6146374639988123879731319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16390332373301663679283517 6146374639988123879731319)
  ·
    refine ⟨9219561959982185819596979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6146374639988123879731319 9219561959982185819596979)
    ·
      refine ⟨13829342939973278729395469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9219561959982185819596979 13829342939973278729395469)
      ·
        refine ⟨5186003602489979523523301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13829342939973278729395469 5186003602489979523523301)
        ·
          refine ⟨972375675466871160660619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5186003602489979523523301 972375675466871160660619)
          ·
            refine ⟨1458563513200306740990929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 972375675466871160660619 1458563513200306740990929)
            ·
              refine ⟨1093922634900230055743197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1458563513200306740990929 1093922634900230055743197)
              ·
                refine ⟨410220988087586270903699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1093922634900230055743197 410220988087586270903699)
                ·
                  refine ⟨615331482131379406355549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 410220988087586270903699 615331482131379406355549)
                  ·
                    refine ⟨230749305799267277383331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 615331482131379406355549 230749305799267277383331)
                    ·
                      rfl

theorem cell22_674074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 3, 1, 3].length) (baseStart_674074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_674074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_674074 prefixEnd_674074 := by exact prefixLift 674074
  have htrace : WordTrace (prefixWord ++ tailWord_674074) baseStart_674074 baseEnd_674074 := by
    simpa [prefixWord, tailWord_674074, baseEnd_674074] using wordTrace_append hprefix tailTrace_674074
  have hstable : (prefixWord ++ tailWord_674074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674074).length < 2 ^ (prefixWord ++ tailWord_674074).sum := by decide
  have hdescent : baseEnd_674074 < baseStart_674074 := by decide
  rcases family_descends (prefixWord ++ tailWord_674074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674128 : List Nat := [2, 1, 1, 1, 1, 6, 2, 1, 1, 6]
def baseStart_674128 : Nat := 118140960795 + 674128 * 2 ^ 59
def prefixEnd_674128 : Nat := 4983230072969 + 3 ^ 40 * 674128 * 2
def baseEnd_674128 : Nat := 230767791102829136533165

theorem tailTrace_674128 : CollatzResearch.WordTrace tailWord_674128 prefixEnd_674128 230767791102829136533165 := by
  unfold tailWord_674128
  simp only [CollatzResearch.WordTrace]
  refine ⟨12293734050878431370695519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16391645401171241827594025 12293734050878431370695519)
  ·
    refine ⟨18440601076317647056043279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12293734050878431370695519 18440601076317647056043279)
    ·
      refine ⟨27660901614476470584064919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18440601076317647056043279 27660901614476470584064919)
      ·
        refine ⟨41491352421714705876097379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27660901614476470584064919 41491352421714705876097379)
        ·
          refine ⟨62237028632572058814146069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41491352421714705876097379 62237028632572058814146069)
          ·
            refine ⟨2917360717151815256913097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62237028632572058814146069 2917360717151815256913097)
            ·
              refine ⟨2188020537863861442684823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2917360717151815256913097 2188020537863861442684823)
              ·
                refine ⟨3282030806795792164027235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2188020537863861442684823 3282030806795792164027235)
                ·
                  refine ⟨4923046210193688246040853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3282030806795792164027235 4923046210193688246040853)
                  ·
                    refine ⟨230767791102829136533165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4923046210193688246040853 230767791102829136533165)
                    ·
                      rfl

theorem cell22_674128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 1, 6].length) (baseStart_674128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_674128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_674128 prefixEnd_674128 := by exact prefixLift 674128
  have htrace : WordTrace (prefixWord ++ tailWord_674128) baseStart_674128 baseEnd_674128 := by
    simpa [prefixWord, tailWord_674128, baseEnd_674128] using wordTrace_append hprefix tailTrace_674128
  have hstable : (prefixWord ++ tailWord_674128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674128).length < 2 ^ (prefixWord ++ tailWord_674128).sum := by decide
  have hdescent : baseEnd_674128 < baseStart_674128 := by decide
  rcases family_descends (prefixWord ++ tailWord_674128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674130 : List Nat := [3, 2, 2, 1, 1, 1, 3, 2, 4, 3]
def baseStart_674130 : Nat := 118140960795 + 674130 * 2 ^ 59
def prefixEnd_674130 : Nat := 4983230072969 + 3 ^ 40 * 674130 * 2
def baseEnd_674130 : Nat := 230768475743701797983159

theorem tailTrace_674130 : CollatzResearch.WordTrace tailWord_674130 prefixEnd_674130 230768475743701797983159 := by
  unfold tailWord_674130
  simp only [CollatzResearch.WordTrace]
  refine ⟨6146885261937404270740961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16391694031833078055309229 6146885261937404270740961)
  ·
    refine ⟨4610163946453053203055721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6146885261937404270740961 4610163946453053203055721)
    ·
      refine ⟨3457622959839789902291791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4610163946453053203055721 3457622959839789902291791)
      ·
        refine ⟨5186434439759684853437687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3457622959839789902291791 5186434439759684853437687)
        ·
          refine ⟨7779651659639527280156531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5186434439759684853437687 7779651659639527280156531)
          ·
            refine ⟨11669477489459290920234797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7779651659639527280156531 11669477489459290920234797)
            ·
              refine ⟨4376054058547234095088049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11669477489459290920234797 4376054058547234095088049)
              ·
                refine ⟨3282040543910425571316037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4376054058547234095088049 3282040543910425571316037)
                ·
                  refine ⟨615382601983204794621757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3282040543910425571316037 615382601983204794621757)
                  ·
                    refine ⟨230768475743701797983159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 615382601983204794621757 230768475743701797983159)
                    ·
                      rfl

theorem cell22_674130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_674130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_674130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_674130 prefixEnd_674130 := by exact prefixLift 674130
  have htrace : WordTrace (prefixWord ++ tailWord_674130) baseStart_674130 baseEnd_674130 := by
    simpa [prefixWord, tailWord_674130, baseEnd_674130] using wordTrace_append hprefix tailTrace_674130
  have hstable : (prefixWord ++ tailWord_674130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674130).length < 2 ^ (prefixWord ++ tailWord_674130).sum := by decide
  have hdescent : baseEnd_674130 < baseStart_674130 := by decide
  rcases family_descends (prefixWord ++ tailWord_674130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674132 : List Nat := [2, 4, 1, 1, 2, 2, 3, 3, 4]
def baseStart_674132 : Nat := 118140960795 + 674132 * 2 ^ 59
def prefixEnd_674132 : Nat := 4983230072969 + 3 ^ 40 * 674132 * 2
def baseEnd_674132 : Nat := 76923053461524819811051

theorem tailTrace_674132 : CollatzResearch.WordTrace tailWord_674132 prefixEnd_674132 76923053461524819811051 := by
  unfold tailWord_674132
  simp only [CollatzResearch.WordTrace]
  refine ⟨12293806996871185712268325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16391742662494914283024433 12293806996871185712268325)
  ·
    refine ⟨2305088811913347321050311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12293806996871185712268325 2305088811913347321050311)
    ·
      refine ⟨3457633217870020981575467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2305088811913347321050311 3457633217870020981575467)
      ·
        refine ⟨5186449826805031472363201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3457633217870020981575467 5186449826805031472363201)
        ·
          refine ⟨3889837370103773604272401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5186449826805031472363201 3889837370103773604272401)
          ·
            refine ⟨2917378027577830203204301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3889837370103773604272401 2917378027577830203204301)
            ·
              refine ⟨1094016760341686326201613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2917378027577830203204301 1094016760341686326201613)
              ·
                refine ⟨410256285128132372325605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1094016760341686326201613 410256285128132372325605)
                ·
                  refine ⟨76923053461524819811051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 410256285128132372325605 76923053461524819811051)
                  ·
                    rfl

theorem cell22_674132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_674132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_674132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_674132 prefixEnd_674132 := by exact prefixLift 674132
  have htrace : WordTrace (prefixWord ++ tailWord_674132) baseStart_674132 baseEnd_674132 := by
    simpa [prefixWord, tailWord_674132, baseEnd_674132] using wordTrace_append hprefix tailTrace_674132
  have hstable : (prefixWord ++ tailWord_674132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674132).length < 2 ^ (prefixWord ++ tailWord_674132).sum := by decide
  have hdescent : baseEnd_674132 < baseStart_674132 := by decide
  rcases family_descends (prefixWord ++ tailWord_674132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674142 : List Nat := [4, 4, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_674142 : Nat := 118140960795 + 674142 * 2 ^ 59
def prefixEnd_674142 : Nat := 4983230072969 + 3 ^ 40 * 674142 * 2
def baseEnd_674142 : Nat := 230772583588937766683123

theorem tailTrace_674142 : CollatzResearch.WordTrace tailWord_674142 prefixEnd_674142 230772583588937766683123 := by
  unfold tailWord_674142
  simp only [CollatzResearch.WordTrace]
  refine ⟨3073497340463267891550085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16391985815804095421600453 3073497340463267891550085)
  ·
    refine ⟨576280751336862729665641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3073497340463267891550085 576280751336862729665641)
    ·
      refine ⟨432210563502647047249231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 576280751336862729665641 432210563502647047249231)
      ·
        refine ⟨648315845253970570873847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432210563502647047249231 648315845253970570873847)
        ·
          refine ⟨972473767880955856310771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 648315845253970570873847 972473767880955856310771)
          ·
            refine ⟨1458710651821433784466157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 972473767880955856310771 1458710651821433784466157)
            ·
              refine ⟨547016494433037669174809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1458710651821433784466157 547016494433037669174809)
              ·
                refine ⟨410262370824778251881107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 547016494433037669174809 410262370824778251881107)
                ·
                  refine ⟨615393556237167377821661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 410262370824778251881107 615393556237167377821661)
                  ·
                    refine ⟨230772583588937766683123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 615393556237167377821661 230772583588937766683123)
                    ·
                      rfl

theorem cell22_674142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_674142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_674142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_674142 prefixEnd_674142 := by exact prefixLift 674142
  have htrace : WordTrace (prefixWord ++ tailWord_674142) baseStart_674142 baseEnd_674142 := by
    simpa [prefixWord, tailWord_674142, baseEnd_674142] using wordTrace_append hprefix tailTrace_674142
  have hstable : (prefixWord ++ tailWord_674142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674142).length < 2 ^ (prefixWord ++ tailWord_674142).sum := by decide
  have hdescent : baseEnd_674142 < baseStart_674142 := by decide
  rcases family_descends (prefixWord ++ tailWord_674142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674280 : List Nat := [2, 1, 4, 1, 1, 3, 1, 2, 1, 6]
def baseStart_674280 : Nat := 118140960795 + 674280 * 2 ^ 59
def prefixEnd_674280 : Nat := 4983230072969 + 3 ^ 40 * 674280 * 2
def baseEnd_674280 : Nat := 230819823809151406732699

theorem tailTrace_674280 : CollatzResearch.WordTrace tailWord_674280 prefixEnd_674280 230819823809151406732699 := by
  unfold tailWord_674280
  simp only [CollatzResearch.WordTrace]
  refine ⟨12296505998603096350462147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16395341331470795133949529 12296505998603096350462147)
  ·
    refine ⟨18444758997904644525693221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12296505998603096350462147 18444758997904644525693221)
    ·
      refine ⟨3458392312107120848567479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18444758997904644525693221 3458392312107120848567479)
      ·
        refine ⟨5187588468160681272851219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3458392312107120848567479 5187588468160681272851219)
        ·
          refine ⟨7781382702241021909276829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5187588468160681272851219 7781382702241021909276829)
          ·
            refine ⟨2918018513340383215978811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7781382702241021909276829 2918018513340383215978811)
            ·
              refine ⟨4377027770010574823968217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2918018513340383215978811 4377027770010574823968217)
              ·
                refine ⟨3282770827507931117976163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4377027770010574823968217 3282770827507931117976163)
                ·
                  refine ⟨4924156241261896676964245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3282770827507931117976163 4924156241261896676964245)
                  ·
                    refine ⟨230819823809151406732699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4924156241261896676964245 230819823809151406732699)
                    ·
                      rfl

theorem cell22_674280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_674280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_674280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_674280 prefixEnd_674280 := by exact prefixLift 674280
  have htrace : WordTrace (prefixWord ++ tailWord_674280) baseStart_674280 baseEnd_674280 := by
    simpa [prefixWord, tailWord_674280, baseEnd_674280] using wordTrace_append hprefix tailTrace_674280
  have hstable : (prefixWord ++ tailWord_674280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674280).length < 2 ^ (prefixWord ++ tailWord_674280).sum := by decide
  have hdescent : baseEnd_674280 < baseStart_674280 := by decide
  rcases family_descends (prefixWord ++ tailWord_674280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674282 : List Nat := [3, 1, 3, 1, 3, 1, 3, 1, 1, 5]
def baseStart_674282 : Nat := 118140960795 + 674282 * 2 ^ 59
def prefixEnd_674282 : Nat := 4983230072969 + 3 ^ 40 * 674282 * 2
def baseEnd_674282 : Nat := 230820508450024068182693

theorem tailTrace_674282 : CollatzResearch.WordTrace tailWord_674282 prefixEnd_674282 230820508450024068182693 := by
  unfold tailWord_674282
  simp only [CollatzResearch.WordTrace]
  refine ⟨6148271235799736760624275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16395389962132631361664733 6148271235799736760624275)
  ·
    refine ⟨9222406853699605140936413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6148271235799736760624275 9222406853699605140936413)
    ·
      refine ⟨3458402570137351927851155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9222406853699605140936413 3458402570137351927851155)
      ·
        refine ⟨5187603855206027891776733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3458402570137351927851155 5187603855206027891776733)
        ·
          refine ⟨1945351445702260459416275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5187603855206027891776733 1945351445702260459416275)
          ·
            refine ⟨2918027168553390689124413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1945351445702260459416275 2918027168553390689124413)
            ·
              refine ⟨1094260188207521508421655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2918027168553390689124413 1094260188207521508421655)
              ·
                refine ⟨1641390282311282262632483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1094260188207521508421655 1641390282311282262632483)
                ·
                  refine ⟨2462085423466923393948725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1641390282311282262632483 2462085423466923393948725)
                  ·
                    refine ⟨230820508450024068182693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2462085423466923393948725 230820508450024068182693)
                    ·
                      rfl

theorem cell22_674282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_674282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_674282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_674282 prefixEnd_674282 := by exact prefixLift 674282
  have htrace : WordTrace (prefixWord ++ tailWord_674282) baseStart_674282 baseEnd_674282 := by
    simpa [prefixWord, tailWord_674282, baseEnd_674282] using wordTrace_append hprefix tailTrace_674282
  have hstable : (prefixWord ++ tailWord_674282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674282).length < 2 ^ (prefixWord ++ tailWord_674282).sum := by decide
  have hdescent : baseEnd_674282 < baseStart_674282 := by decide
  rcases family_descends (prefixWord ++ tailWord_674282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674325 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 2, 6]
def baseStart_674325 : Nat := 118140960795 + 674325 * 2 ^ 59
def prefixEnd_674325 : Nat := 4983230072969 + 3 ^ 40 * 674325 * 2
def baseEnd_674325 : Nat := 230835228228786289357561

theorem tailTrace_674325 : CollatzResearch.WordTrace tailWord_674325 prefixEnd_674325 230835228228786289357561 := by
  unfold tailWord_674325
  simp only [CollatzResearch.WordTrace]
  refine ⟨24594653282043165386312429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16396435521362110257541619 24594653282043165386312429)
  ·
    refine ⟨9222994980766187019867161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24594653282043165386312429 9222994980766187019867161)
    ·
      refine ⟨6917246235574640264900371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9222994980766187019867161 6917246235574640264900371)
      ·
        refine ⟨10375869353361960397350557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6917246235574640264900371 10375869353361960397350557)
        ·
          refine ⟨3890951007510735149006459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10375869353361960397350557 3890951007510735149006459)
          ·
            refine ⟨5836426511266102723509689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3890951007510735149006459 5836426511266102723509689)
            ·
              refine ⟨4377319883449577042632267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5836426511266102723509689 4377319883449577042632267)
              ·
                refine ⟨6565979825174365563948401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4377319883449577042632267 6565979825174365563948401)
                ·
                  refine ⟨4924484868880774172961301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6565979825174365563948401 4924484868880774172961301)
                  ·
                    refine ⟨230835228228786289357561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4924484868880774172961301 230835228228786289357561)
                    ·
                      rfl

theorem cell22_674325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_674325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_674325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_674325 prefixEnd_674325 := by exact prefixLift 674325
  have htrace : WordTrace (prefixWord ++ tailWord_674325) baseStart_674325 baseEnd_674325 := by
    simpa [prefixWord, tailWord_674325, baseEnd_674325] using wordTrace_append hprefix tailTrace_674325
  have hstable : (prefixWord ++ tailWord_674325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674325).length < 2 ^ (prefixWord ++ tailWord_674325).sum := by decide
  have hdescent : baseEnd_674325 < baseStart_674325 := by decide
  rcases family_descends (prefixWord ++ tailWord_674325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674378 : List Nat := [3, 1, 2, 1, 1, 6, 2, 2, 1, 3]
def baseStart_674378 : Nat := 118140960795 + 674378 * 2 ^ 59
def prefixEnd_674378 : Nat := 4983230072969 + 3 ^ 40 * 674378 * 2
def baseEnd_674378 : Nat := 230853371211911817782399

theorem tailTrace_674378 : CollatzResearch.WordTrace tailWord_674378 prefixEnd_674378 230853371211911817782399 := by
  unfold tailWord_674378
  simp only [CollatzResearch.WordTrace]
  refine ⟨6149146587712788859497947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16397724233900770291994525 6149146587712788859497947)
  ·
    refine ⟨9223719881569183289246921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6149146587712788859497947 9223719881569183289246921)
    ·
      refine ⟨6917789911176887466935191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9223719881569183289246921 6917789911176887466935191)
      ·
        refine ⟨10376684866765331200402787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6917789911176887466935191 10376684866765331200402787)
        ·
          refine ⟨15565027300147996800604181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10376684866765331200402787 15565027300147996800604181)
          ·
            refine ⟨729610654694437350028321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15565027300147996800604181 729610654694437350028321)
            ·
              refine ⟨547207991020828012521241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 729610654694437350028321 547207991020828012521241)
              ·
                refine ⟨410405993265621009390931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 547207991020828012521241 410405993265621009390931)
                ·
                  refine ⟨615608989898431514086397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 410405993265621009390931 615608989898431514086397)
                  ·
                    refine ⟨230853371211911817782399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 615608989898431514086397 230853371211911817782399)
                    ·
                      rfl

theorem cell22_674378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_674378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_674378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_674378 prefixEnd_674378 := by exact prefixLift 674378
  have htrace : WordTrace (prefixWord ++ tailWord_674378) baseStart_674378 baseEnd_674378 := by
    simpa [prefixWord, tailWord_674378, baseEnd_674378] using wordTrace_append hprefix tailTrace_674378
  have hstable : (prefixWord ++ tailWord_674378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674378).length < 2 ^ (prefixWord ++ tailWord_674378).sum := by decide
  have hdescent : baseEnd_674378 < baseStart_674378 := by decide
  rcases family_descends (prefixWord ++ tailWord_674378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674421 : List Nat := [1, 3, 4, 2, 2, 1, 1, 3, 1, 4]
def baseStart_674421 : Nat := 118140960795 + 674421 * 2 ^ 59
def prefixEnd_674421 : Nat := 4983230072969 + 3 ^ 40 * 674421 * 2
def baseEnd_674421 : Nat := 230868090990674038957267

theorem tailTrace_674421 : CollatzResearch.WordTrace tailWord_674421 prefixEnd_674421 230868090990674038957267 := by
  unfold tailWord_674421
  simp only [CollatzResearch.WordTrace]
  refine ⟨24598154689695373781807117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16398769793130249187871411 24598154689695373781807117)
  ·
    refine ⟨9224308008635765168177669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24598154689695373781807117 9224308008635765168177669)
    ·
      refine ⟨1729557751619205969033313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9224308008635765168177669 1729557751619205969033313)
      ·
        refine ⟨1297168313714404476774985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1729557751619205969033313 1297168313714404476774985)
        ·
          refine ⟨972876235285803357581239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1297168313714404476774985 972876235285803357581239)
          ·
            refine ⟨1459314352928705036371859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 972876235285803357581239 1459314352928705036371859)
            ·
              refine ⟨2188971529393057554557789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1459314352928705036371859 2188971529393057554557789)
              ·
                refine ⟨820864323522396582959171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2188971529393057554557789 820864323522396582959171)
                ·
                  refine ⟨1231296485283594874438757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 820864323522396582959171 1231296485283594874438757)
                  ·
                    refine ⟨230868090990674038957267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1231296485283594874438757 230868090990674038957267)
                    ·
                      rfl

theorem cell22_674421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_674421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_674421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_674421 prefixEnd_674421 := by exact prefixLift 674421
  have htrace : WordTrace (prefixWord ++ tailWord_674421) baseStart_674421 baseEnd_674421 := by
    simpa [prefixWord, tailWord_674421, baseEnd_674421] using wordTrace_append hprefix tailTrace_674421
  have hstable : (prefixWord ++ tailWord_674421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674421).length < 2 ^ (prefixWord ++ tailWord_674421).sum := by decide
  have hdescent : baseEnd_674421 < baseStart_674421 := by decide
  rcases family_descends (prefixWord ++ tailWord_674421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674481 : List Nat := [1, 2, 2, 6, 2, 1, 8]
def baseStart_674481 : Nat := 118140960795 + 674481 * 2 ^ 59
def prefixEnd_674481 : Nat := 4983230072969 + 3 ^ 40 * 674481 * 2
def baseEnd_674481 : Nat := 8551430748772366016929

theorem tailTrace_674481 : CollatzResearch.WordTrace tailWord_674481 prefixEnd_674481 8551430748772366016929 := by
  unfold tailWord_674481
  simp only [CollatzResearch.WordTrace]
  refine ⟨24600343069478004028991297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16400228712985336019327531 24600343069478004028991297)
  ·
    refine ⟨18450257302108503021743473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24600343069478004028991297 18450257302108503021743473)
    ·
      refine ⟨13837692976581377266307605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18450257302108503021743473 13837692976581377266307605)
      ·
        refine ⟨648641858277252059358169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13837692976581377266307605 648641858277252059358169)
        ·
          refine ⟨486481393707939044518627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 648641858277252059358169 486481393707939044518627)
          ·
            refine ⟨729722090561908566777941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486481393707939044518627 729722090561908566777941)
            ·
              refine ⟨8551430748772366016929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 729722090561908566777941 8551430748772366016929)
              ·
                rfl

theorem cell22_674481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 8].length) (baseStart_674481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_674481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_674481 prefixEnd_674481 := by exact prefixLift 674481
  have htrace : WordTrace (prefixWord ++ tailWord_674481) baseStart_674481 baseEnd_674481 := by
    simpa [prefixWord, tailWord_674481, baseEnd_674481] using wordTrace_append hprefix tailTrace_674481
  have hstable : (prefixWord ++ tailWord_674481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674481).length < 2 ^ (prefixWord ++ tailWord_674481).sum := by decide
  have hdescent : baseEnd_674481 < baseStart_674481 := by decide
  rcases family_descends (prefixWord ++ tailWord_674481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674492 : List Nat := [2, 2, 2, 3, 1, 1, 1, 3, 7]
def baseStart_674492 : Nat := 118140960795 + 674492 * 2 ^ 59
def prefixEnd_674492 : Nat := 4983230072969 + 3 ^ 40 * 674492 * 2
def baseEnd_674492 : Nat := 76964131913884506810683

theorem tailTrace_674492 : CollatzResearch.WordTrace tailWord_674492 prefixEnd_674492 76964131913884506810683 := by
  unfold tailWord_674492
  simp only [CollatzResearch.WordTrace]
  refine ⟨12300372136219076453820865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16400496181625435271761153 12300372136219076453820865)
  ·
    refine ⟨9225279102164307340365649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12300372136219076453820865 9225279102164307340365649)
    ·
      refine ⟨6918959326623230505274237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9225279102164307340365649 6918959326623230505274237)
      ·
        refine ⟨2594609747483711439477839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6918959326623230505274237 2594609747483711439477839)
        ·
          refine ⟨3891914621225567159216759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2594609747483711439477839 3891914621225567159216759)
          ·
            refine ⟨5837871931838350738825139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3891914621225567159216759 5837871931838350738825139)
            ·
              refine ⟨8756807897757526108237709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5837871931838350738825139 8756807897757526108237709)
              ·
                refine ⟨3283802961659072290589141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8756807897757526108237709 3283802961659072290589141)
                ·
                  refine ⟨76964131913884506810683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3283802961659072290589141 76964131913884506810683)
                  ·
                    rfl

theorem cell22_674492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 7].length) (baseStart_674492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_674492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_674492 prefixEnd_674492 := by exact prefixLift 674492
  have htrace : WordTrace (prefixWord ++ tailWord_674492) baseStart_674492 baseEnd_674492 := by
    simpa [prefixWord, tailWord_674492, baseEnd_674492] using wordTrace_append hprefix tailTrace_674492
  have hstable : (prefixWord ++ tailWord_674492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674492).length < 2 ^ (prefixWord ++ tailWord_674492).sum := by decide
  have hdescent : baseEnd_674492 < baseStart_674492 := by decide
  rcases family_descends (prefixWord ++ tailWord_674492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674496 : List Nat := [2, 1, 1, 2, 4, 4, 1, 1, 3, 3]
def baseStart_674496 : Nat := 118140960795 + 674496 * 2 ^ 59
def prefixEnd_674496 : Nat := 4983230072969 + 3 ^ 40 * 674496 * 2
def baseEnd_674496 : Nat := 230893765023398843332037

theorem tailTrace_674496 : CollatzResearch.WordTrace tailWord_674496 prefixEnd_674496 230893765023398843332037 := by
  unfold tailWord_674496
  simp only [CollatzResearch.WordTrace]
  refine ⟨12300445082211830795393671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16400593442949107727191561 12300445082211830795393671)
  ·
    refine ⟨18450667623317746193090507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12300445082211830795393671 18450667623317746193090507)
    ·
      refine ⟨27676001434976619289635761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18450667623317746193090507 27676001434976619289635761)
      ·
        refine ⟨20757001076232464467226821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27676001434976619289635761 20757001076232464467226821)
        ·
          refine ⟨3891937701793587087605029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20757001076232464467226821 3891937701793587087605029)
          ·
            refine ⟨729738319086297578925943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3891937701793587087605029 729738319086297578925943)
            ·
              refine ⟨1094607478629446368388915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 729738319086297578925943 1094607478629446368388915)
              ·
                refine ⟨1641911217944169552583373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1094607478629446368388915 1641911217944169552583373)
                ·
                  refine ⟨615716706729063582218765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1641911217944169552583373 615716706729063582218765)
                  ·
                    refine ⟨230893765023398843332037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 615716706729063582218765 230893765023398843332037)
                    ·
                      rfl

theorem cell22_674496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 3, 3].length) (baseStart_674496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_674496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_674496 prefixEnd_674496 := by exact prefixLift 674496
  have htrace : WordTrace (prefixWord ++ tailWord_674496) baseStart_674496 baseEnd_674496 := by
    simpa [prefixWord, tailWord_674496, baseEnd_674496] using wordTrace_append hprefix tailTrace_674496
  have hstable : (prefixWord ++ tailWord_674496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674496).length < 2 ^ (prefixWord ++ tailWord_674496).sum := by decide
  have hdescent : baseEnd_674496 < baseStart_674496 := by decide
  rcases family_descends (prefixWord ++ tailWord_674496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674552 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 3, 5]
def baseStart_674552 : Nat := 118140960795 + 674552 * 2 ^ 59
def prefixEnd_674552 : Nat := 4983230072969 + 3 ^ 40 * 674552 * 2
def baseEnd_674552 : Nat := 230912934967833363931865

theorem tailTrace_674552 : CollatzResearch.WordTrace tailWord_674552 prefixEnd_674552 230912934967833363931865 := by
  unfold tailWord_674552
  simp only [CollatzResearch.WordTrace]
  refine ⟨12301466326110391577412955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16401955101480522103217273 12301466326110391577412955)
  ·
    refine ⟨18452199489165587366119433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12301466326110391577412955 18452199489165587366119433)
    ·
      refine ⟨13839149616874190524589575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18452199489165587366119433 13839149616874190524589575)
      ·
        refine ⟨20758724425311285786884363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13839149616874190524589575 20758724425311285786884363)
        ·
          refine ⟨31138086637966928680326545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20758724425311285786884363 31138086637966928680326545)
          ·
            refine ⟨23353564978475196510244909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31138086637966928680326545 23353564978475196510244909)
            ·
              refine ⟨8757586866928198691341841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23353564978475196510244909 8757586866928198691341841)
              ·
                refine ⟨6568190150196149018506381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8757586866928198691341841 6568190150196149018506381)
                ·
                  refine ⟨2463071306323555881939893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6568190150196149018506381 2463071306323555881939893)
                  ·
                    refine ⟨230912934967833363931865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2463071306323555881939893 230912934967833363931865)
                    ·
                      rfl

theorem cell22_674552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_674552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_674552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_674552 prefixEnd_674552 := by exact prefixLift 674552
  have htrace : WordTrace (prefixWord ++ tailWord_674552) baseStart_674552 baseEnd_674552 := by
    simpa [prefixWord, tailWord_674552, baseEnd_674552] using wordTrace_append hprefix tailTrace_674552
  have hstable : (prefixWord ++ tailWord_674552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674552).length < 2 ^ (prefixWord ++ tailWord_674552).sum := by decide
  have hdescent : baseEnd_674552 < baseStart_674552 := by decide
  rcases family_descends (prefixWord ++ tailWord_674552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674678 : List Nat := [5, 1, 1, 3, 1, 2, 1, 3, 5]
def baseStart_674678 : Nat := 118140960795 + 674678 * 2 ^ 59
def prefixEnd_674678 : Nat := 4983230072969 + 3 ^ 40 * 674678 * 2
def baseEnd_674678 : Nat := 76985355780937011760493

theorem tailTrace_674678 : CollatzResearch.WordTrace tailWord_674678 prefixEnd_674678 76985355780937011760493 := by
  unfold tailWord_674678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1537970515610269167119543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16405018833176204449275125 1537970515610269167119543)
  ·
    refine ⟨2306955773415403750679315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1537970515610269167119543 2306955773415403750679315)
    ·
      refine ⟨3460433660123105626018973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2306955773415403750679315 3460433660123105626018973)
      ·
        refine ⟨1297662622546164609757115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3460433660123105626018973 1297662622546164609757115)
        ·
          refine ⟨1946493933819246914635673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1297662622546164609757115 1946493933819246914635673)
          ·
            refine ⟨1459870450364435185976755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1946493933819246914635673 1459870450364435185976755)
            ·
              refine ⟨2189805675546652778965133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1459870450364435185976755 2189805675546652778965133)
              ·
                refine ⟨821177128329994792111925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2189805675546652778965133 821177128329994792111925)
                ·
                  refine ⟨76985355780937011760493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 821177128329994792111925 76985355780937011760493)
                  ·
                    rfl

theorem cell22_674678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_674678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_674678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_674678 prefixEnd_674678 := by exact prefixLift 674678
  have htrace : WordTrace (prefixWord ++ tailWord_674678) baseStart_674678 baseEnd_674678 := by
    simpa [prefixWord, tailWord_674678, baseEnd_674678] using wordTrace_append hprefix tailTrace_674678
  have hstable : (prefixWord ++ tailWord_674678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674678).length < 2 ^ (prefixWord ++ tailWord_674678).sum := by decide
  have hdescent : baseEnd_674678 < baseStart_674678 := by decide
  rcases family_descends (prefixWord ++ tailWord_674678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674723 : List Nat := [1, 1, 1, 4, 1, 2, 6, 2, 4]
def baseStart_674723 : Nat := 118140960795 + 674723 * 2 ^ 59
def prefixEnd_674723 : Nat := 4983230072969 + 3 ^ 40 * 674723 * 2
def baseEnd_674723 : Nat := 76990490587481972635447

theorem tailTrace_674723 : CollatzResearch.WordTrace tailWord_674723 prefixEnd_674723 76990490587481972635447 := by
  unfold tailWord_674723
  simp only [CollatzResearch.WordTrace]
  refine ⟨24609169534601279359300823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16406113023067519572867215 24609169534601279359300823)
  ·
    refine ⟨36913754301901919038951235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24609169534601279359300823 36913754301901919038951235)
    ·
      refine ⟨55370631452852878558426853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36913754301901919038951235 55370631452852878558426853)
      ·
        refine ⟨10381993397409914729705035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55370631452852878558426853 10381993397409914729705035)
        ·
          refine ⟨15572990096114872094557553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10381993397409914729705035 15572990096114872094557553)
          ·
            refine ⟨11679742572086154070918165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15572990096114872094557553 11679742572086154070918165)
            ·
              refine ⟨547487933066538472074289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11679742572086154070918165 547487933066538472074289)
              ·
                refine ⟨410615949799903854055717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 547487933066538472074289 410615949799903854055717)
                ·
                  refine ⟨76990490587481972635447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 410615949799903854055717 76990490587481972635447)
                  ·
                    rfl

theorem cell22_674723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 2, 4].length) (baseStart_674723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_674723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_674723 prefixEnd_674723 := by exact prefixLift 674723
  have htrace : WordTrace (prefixWord ++ tailWord_674723) baseStart_674723 baseEnd_674723 := by
    simpa [prefixWord, tailWord_674723, baseEnd_674723] using wordTrace_append hprefix tailTrace_674723
  have hstable : (prefixWord ++ tailWord_674723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674723).length < 2 ^ (prefixWord ++ tailWord_674723).sum := by decide
  have hdescent : baseEnd_674723 < baseStart_674723 := by decide
  rcases family_descends (prefixWord ++ tailWord_674723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674802 : List Nat := [3, 2, 1, 5, 2, 1, 2, 6]
def baseStart_674802 : Nat := 118140960795 + 674802 * 2 ^ 59
def prefixEnd_674802 : Nat := 4983230072969 + 3 ^ 40 * 674802 * 2
def baseEnd_674802 : Nat := 25666501675212893909011

theorem tailTrace_674802 : CollatzResearch.WordTrace tailWord_674802 prefixEnd_674802 25666501675212893909011 := by
  unfold tailWord_674802
  simp only [CollatzResearch.WordTrace]
  refine ⟨6153012725328768962856665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16408033934210050567617773 6153012725328768962856665)
  ·
    refine ⟨4614759543996576722142499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6153012725328768962856665 4614759543996576722142499)
    ·
      refine ⟨6922139315994865083213749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4614759543996576722142499 6922139315994865083213749)
      ·
        refine ⟨648950560874518601551289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6922139315994865083213749 648950560874518601551289)
        ·
          refine ⟨486712920655888951163467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 648950560874518601551289 486712920655888951163467)
          ·
            refine ⟨730069380983833426745201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486712920655888951163467 730069380983833426745201)
            ·
              refine ⟨547552035737875070058901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 730069380983833426745201 547552035737875070058901)
              ·
                refine ⟨25666501675212893909011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 547552035737875070058901 25666501675212893909011)
                ·
                  rfl

theorem cell22_674802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 6].length) (baseStart_674802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_674802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_674802 prefixEnd_674802 := by exact prefixLift 674802
  have htrace : WordTrace (prefixWord ++ tailWord_674802) baseStart_674802 baseEnd_674802 := by
    simpa [prefixWord, tailWord_674802, baseEnd_674802] using wordTrace_append hprefix tailTrace_674802
  have hstable : (prefixWord ++ tailWord_674802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674802).length < 2 ^ (prefixWord ++ tailWord_674802).sum := by decide
  have hdescent : baseEnd_674802 < baseStart_674802 := by decide
  rcases family_descends (prefixWord ++ tailWord_674802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674817 : List Nat := [1, 2, 4, 1, 2, 4, 1, 3, 1, 3]
def baseStart_674817 : Nat := 118140960795 + 674817 * 2 ^ 59
def prefixEnd_674817 : Nat := 4983230072969 + 3 ^ 40 * 674817 * 2
def baseEnd_674817 : Nat := 231003649883461006056053

theorem tailTrace_674817 : CollatzResearch.WordTrace tailWord_674817 prefixEnd_674817 231003649883461006056053 := by
  unfold tailWord_674817
  simp only [CollatzResearch.WordTrace]
  refine ⟨24612597996260733413222705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16408398664173822275481803 24612597996260733413222705)
  ·
    refine ⟨18459448497195550059917029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24612597996260733413222705 18459448497195550059917029)
    ·
      refine ⟨3461146593224165636234443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18459448497195550059917029 3461146593224165636234443)
      ·
        refine ⟨5191719889836248454351665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3461146593224165636234443 5191719889836248454351665)
        ·
          refine ⟨3893789917377186340763749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5191719889836248454351665 3893789917377186340763749)
          ·
            refine ⟨730085609508222438893203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3893789917377186340763749 730085609508222438893203)
            ·
              refine ⟨1095128414262333658339805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730085609508222438893203 1095128414262333658339805)
              ·
                refine ⟨410673155348375121877427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1095128414262333658339805 410673155348375121877427)
                ·
                  refine ⟨616009733022562682816141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 410673155348375121877427 616009733022562682816141)
                  ·
                    refine ⟨231003649883461006056053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 616009733022562682816141 231003649883461006056053)
                    ·
                      rfl

theorem cell22_674817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_674817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_674817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_674817 prefixEnd_674817 := by exact prefixLift 674817
  have htrace : WordTrace (prefixWord ++ tailWord_674817) baseStart_674817 baseEnd_674817 := by
    simpa [prefixWord, tailWord_674817, baseEnd_674817] using wordTrace_append hprefix tailTrace_674817
  have hstable : (prefixWord ++ tailWord_674817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674817).length < 2 ^ (prefixWord ++ tailWord_674817).sum := by decide
  have hdescent : baseEnd_674817 < baseStart_674817 := by decide
  rcases family_descends (prefixWord ++ tailWord_674817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674841 : List Nat := [1, 2, 1, 2, 1, 1, 7, 1, 6]
def baseStart_674841 : Nat := 118140960795 + 674841 * 2 ^ 59
def prefixEnd_674841 : Nat := 4983230072969 + 3 ^ 40 * 674841 * 2
def baseEnd_674841 : Nat := 77003955191310981151993

theorem tailTrace_674841 : CollatzResearch.WordTrace tailWord_674841 prefixEnd_674841 77003955191310981151993 := by
  unfold tailWord_674841
  simp only [CollatzResearch.WordTrace]
  refine ⟨24613473348173785512096377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16408982232115857008064251 24613473348173785512096377)
  ·
    refine ⟨18460105011130339134072283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24613473348173785512096377 18460105011130339134072283)
    ·
      refine ⟨27690157516695508701108425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18460105011130339134072283 27690157516695508701108425)
      ·
        refine ⟨20767618137521631525831319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27690157516695508701108425 20767618137521631525831319)
        ·
          refine ⟨31151427206282447288746979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20767618137521631525831319 31151427206282447288746979)
          ·
            refine ⟨46727140809423670933120469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31151427206282447288746979 46727140809423670933120469)
            ·
              refine ⟨1095167362720867287495011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 46727140809423670933120469 1095167362720867287495011)
              ·
                refine ⟨1642751044081300931242517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1095167362720867287495011 1642751044081300931242517)
                ·
                  refine ⟨77003955191310981151993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1642751044081300931242517 77003955191310981151993)
                  ·
                    rfl

theorem cell22_674841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 6].length) (baseStart_674841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_674841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_674841 prefixEnd_674841 := by exact prefixLift 674841
  have htrace : WordTrace (prefixWord ++ tailWord_674841) baseStart_674841 baseEnd_674841 := by
    simpa [prefixWord, tailWord_674841, baseEnd_674841] using wordTrace_append hprefix tailTrace_674841
  have hstable : (prefixWord ++ tailWord_674841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674841).length < 2 ^ (prefixWord ++ tailWord_674841).sum := by decide
  have hdescent : baseEnd_674841 < baseStart_674841 := by decide
  rcases family_descends (prefixWord ++ tailWord_674841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674873 : List Nat := [1, 2, 1, 5, 2, 2, 1, 2, 1, 5]
def baseStart_674873 : Nat := 118140960795 + 674873 * 2 ^ 59
def prefixEnd_674873 : Nat := 4983230072969 + 3 ^ 40 * 674873 * 2
def baseEnd_674873 : Nat := 231022819827895526655881

theorem tailTrace_674873 : CollatzResearch.WordTrace tailWord_674873 prefixEnd_674873 231022819827895526655881 := by
  unfold tailWord_674873
  simp only [CollatzResearch.WordTrace]
  refine ⟨24614640484057854977261273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16409760322705236651507515 24614640484057854977261273)
  ·
    refine ⟨18460980363043391232945955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24614640484057854977261273 18460980363043391232945955)
    ·
      refine ⟨27691470544565086849418933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18460980363043391232945955 27691470544565086849418933)
      ·
        refine ⟨2596075363552976892133025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27691470544565086849418933 2596075363552976892133025)
        ·
          refine ⟨1947056522664732669099769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2596075363552976892133025 1947056522664732669099769)
          ·
            refine ⟨1460292391998549501824827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1947056522664732669099769 1460292391998549501824827)
            ·
              refine ⟨2190438587997824252737241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1460292391998549501824827 2190438587997824252737241)
              ·
                refine ⟨1642828940998368189552931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2190438587997824252737241 1642828940998368189552931)
                ·
                  refine ⟨2464243411497552284329397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1642828940998368189552931 2464243411497552284329397)
                  ·
                    refine ⟨231022819827895526655881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2464243411497552284329397 231022819827895526655881)
                    ·
                      rfl

theorem cell22_674873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 5].length) (baseStart_674873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_674873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_674873 prefixEnd_674873 := by exact prefixLift 674873
  have htrace : WordTrace (prefixWord ++ tailWord_674873) baseStart_674873 baseEnd_674873 := by
    simpa [prefixWord, tailWord_674873, baseEnd_674873] using wordTrace_append hprefix tailTrace_674873
  have hstable : (prefixWord ++ tailWord_674873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674873).length < 2 ^ (prefixWord ++ tailWord_674873).sum := by decide
  have hdescent : baseEnd_674873 < baseStart_674873 := by decide
  rcases family_descends (prefixWord ++ tailWord_674873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674916 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 4, 6]
def baseStart_674916 : Nat := 118140960795 + 674916 * 2 ^ 59
def prefixEnd_674916 : Nat := 4983230072969 + 3 ^ 40 * 674916 * 2
def baseEnd_674916 : Nat := 231037539606657747830749

theorem tailTrace_674916 : CollatzResearch.WordTrace tailWord_674916 prefixEnd_674916 231037539606657747830749 := by
  unfold tailWord_674916
  simp only [CollatzResearch.WordTrace]
  refine ⟨12308104411451036660538301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16410805881934715547384401 12308104411451036660538301)
  ·
    refine ⟨4615539154294138747701863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12308104411451036660538301 4615539154294138747701863)
    ·
      refine ⟨6923308731441208121552795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4615539154294138747701863 6923308731441208121552795)
      ·
        refine ⟨10384963097161812182329193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6923308731441208121552795 10384963097161812182329193)
        ·
          refine ⟨7788722322871359136746895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10384963097161812182329193 7788722322871359136746895)
          ·
            refine ⟨11683083484307038705120343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7788722322871359136746895 11683083484307038705120343)
            ·
              refine ⟨17524625226460558057680515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11683083484307038705120343 17524625226460558057680515)
              ·
                refine ⟨26286937839690837086520773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17524625226460558057680515 26286937839690837086520773)
                ·
                  refine ⟨4928800844942031953722645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26286937839690837086520773 4928800844942031953722645)
                  ·
                    refine ⟨231037539606657747830749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4928800844942031953722645 231037539606657747830749)
                    ·
                      rfl

theorem cell22_674916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_674916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_674916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_674916 prefixEnd_674916 := by exact prefixLift 674916
  have htrace : WordTrace (prefixWord ++ tailWord_674916) baseStart_674916 baseEnd_674916 := by
    simpa [prefixWord, tailWord_674916, baseEnd_674916] using wordTrace_append hprefix tailTrace_674916
  have hstable : (prefixWord ++ tailWord_674916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674916).length < 2 ^ (prefixWord ++ tailWord_674916).sum := by decide
  have hdescent : baseEnd_674916 < baseStart_674916 := by decide
  rcases family_descends (prefixWord ++ tailWord_674916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674948 : List Nat := [2, 3, 2, 1, 2, 3, 1, 1, 7]
def baseStart_674948 : Nat := 118140960795 + 674948 * 2 ^ 59
def prefixEnd_674948 : Nat := 4983230072969 + 3 ^ 40 * 674948 * 2
def baseEnd_674948 : Nat := 77016164620206777010217

theorem tailTrace_674948 : CollatzResearch.WordTrace tailWord_674948 prefixEnd_674948 77016164620206777010217 := by
  unfold tailWord_674948
  simp only [CollatzResearch.WordTrace]
  refine ⟨12308687979393071393120749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16411583972524095190827665 12308687979393071393120749)
  ·
    refine ⟨4615757992272401772420281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12308687979393071393120749 4615757992272401772420281)
    ·
      refine ⟨3461818494204301329315211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4615757992272401772420281 3461818494204301329315211)
      ·
        refine ⟨5192727741306451993972817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3461818494204301329315211 5192727741306451993972817)
        ·
          refine ⟨3894545805979838995479613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5192727741306451993972817 3894545805979838995479613)
          ·
            refine ⟨1460454677242439623304855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3894545805979838995479613 1460454677242439623304855)
            ·
              refine ⟨2190682015863659434957283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1460454677242439623304855 2190682015863659434957283)
              ·
                refine ⟨3286023023795489152435925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2190682015863659434957283 3286023023795489152435925)
                ·
                  refine ⟨77016164620206777010217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3286023023795489152435925 77016164620206777010217)
                  ·
                    rfl

theorem cell22_674948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_674948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_674948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_674948 prefixEnd_674948 := by exact prefixLift 674948
  have htrace : WordTrace (prefixWord ++ tailWord_674948) baseStart_674948 baseEnd_674948 := by
    simpa [prefixWord, tailWord_674948, baseEnd_674948] using wordTrace_append hprefix tailTrace_674948
  have hstable : (prefixWord ++ tailWord_674948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674948).length < 2 ^ (prefixWord ++ tailWord_674948).sum := by decide
  have hdescent : baseEnd_674948 < baseStart_674948 := by decide
  rcases family_descends (prefixWord ++ tailWord_674948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674952 : List Nat := [2, 1, 3, 4, 2, 1, 2, 1, 3, 3]
def baseStart_674952 : Nat := 118140960795 + 674952 * 2 ^ 59
def prefixEnd_674952 : Nat := 4983230072969 + 3 ^ 40 * 674952 * 2
def baseEnd_674952 : Nat := 231049863142365653930639

theorem tailTrace_674952 : CollatzResearch.WordTrace tailWord_674952 prefixEnd_674952 231049863142365653930639 := by
  unfold tailWord_674952
  simp only [CollatzResearch.WordTrace]
  refine ⟨12308760925385825734693555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16411681233847767646258073 12308760925385825734693555)
  ·
    refine ⟨18463141388078738602040333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12308760925385825734693555 18463141388078738602040333)
    ·
      refine ⟨6923678020529526975765125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18463141388078738602040333 6923678020529526975765125)
      ·
        refine ⟨1298189628849286307955961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6923678020529526975765125 1298189628849286307955961)
        ·
          refine ⟨973642221636964730966971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1298189628849286307955961 973642221636964730966971)
          ·
            refine ⟨1460463332455447096450457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 973642221636964730966971 1460463332455447096450457)
            ·
              refine ⟨1095347499341585322337843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1460463332455447096450457 1095347499341585322337843)
              ·
                refine ⟨1643021249012377983506765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1095347499341585322337843 1643021249012377983506765)
                ·
                  refine ⟨616132968379641743815037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1643021249012377983506765 616132968379641743815037)
                  ·
                    refine ⟨231049863142365653930639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 616132968379641743815037 231049863142365653930639)
                    ·
                      rfl

theorem cell22_674952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_674952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_674952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_674952 prefixEnd_674952 := by exact prefixLift 674952
  have htrace : WordTrace (prefixWord ++ tailWord_674952) baseStart_674952 baseEnd_674952 := by
    simpa [prefixWord, tailWord_674952, baseEnd_674952] using wordTrace_append hprefix tailTrace_674952
  have hstable : (prefixWord ++ tailWord_674952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674952).length < 2 ^ (prefixWord ++ tailWord_674952).sum := by decide
  have hdescent : baseEnd_674952 < baseStart_674952 := by decide
  rcases family_descends (prefixWord ++ tailWord_674952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674986 : List Nat := [3, 1, 5, 1, 1, 3, 1, 3, 1, 3]
def baseStart_674986 : Nat := 118140960795 + 674986 * 2 ^ 59
def prefixEnd_674986 : Nat := 4983230072969 + 3 ^ 40 * 674986 * 2
def baseEnd_674986 : Nat := 231061502037200898580535

theorem tailTrace_674986 : CollatzResearch.WordTrace tailWord_674986 prefixEnd_674986 231061502037200898580535 := by
  unfold tailWord_674986
  simp only [CollatzResearch.WordTrace]
  refine ⟨6154690483162118819031203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16412507955098983517416541 6154690483162118819031203)
  ·
    refine ⟨9232035724743178228546805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6154690483162118819031203 9232035724743178228546805)
    ·
      refine ⟨865503349194672958926263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9232035724743178228546805 865503349194672958926263)
      ·
        refine ⟨1298255023792009438389395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 865503349194672958926263 1298255023792009438389395)
        ·
          refine ⟨1947382535688014157584093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1298255023792009438389395 1947382535688014157584093)
          ·
            refine ⟨730268450883005309094035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1947382535688014157584093 730268450883005309094035)
            ·
              refine ⟨1095402676324507963641053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730268450883005309094035 1095402676324507963641053)
              ·
                refine ⟨410776003621690486365395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1095402676324507963641053 410776003621690486365395)
                ·
                  refine ⟨616164005432535729548093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 410776003621690486365395 616164005432535729548093)
                  ·
                    refine ⟨231061502037200898580535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 616164005432535729548093 231061502037200898580535)
                    ·
                      rfl

theorem cell22_674986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_674986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_674986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_674986 prefixEnd_674986 := by exact prefixLift 674986
  have htrace : WordTrace (prefixWord ++ tailWord_674986) baseStart_674986 baseEnd_674986 := by
    simpa [prefixWord, tailWord_674986, baseEnd_674986] using wordTrace_append hprefix tailTrace_674986
  have hstable : (prefixWord ++ tailWord_674986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674986).length < 2 ^ (prefixWord ++ tailWord_674986).sum := by decide
  have hdescent : baseEnd_674986 < baseStart_674986 := by decide
  rcases family_descends (prefixWord ++ tailWord_674986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675040 : List Nat := [2, 1, 1, 3, 1, 5, 2, 1, 2, 4]
def baseStart_675040 : Nat := 118140960795 + 675040 * 2 ^ 59
def prefixEnd_675040 : Nat := 4983230072969 + 3 ^ 40 * 675040 * 2
def baseEnd_675040 : Nat := 231079987340762757730369

theorem tailTrace_675040 : CollatzResearch.WordTrace tailWord_675040 prefixEnd_675040 231079987340762757730369 := by
  unfold tailWord_675040
  simp only [CollatzResearch.WordTrace]
  refine ⟨12310365737226421249295287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16413820982968561665727049 12310365737226421249295287)
  ·
    refine ⟨18465548605839631873942931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12310365737226421249295287 18465548605839631873942931)
    ·
      refine ⟨27698322908759447810914397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18465548605839631873942931 27698322908759447810914397)
      ·
        refine ⟨10386871090784792929092899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27698322908759447810914397 10386871090784792929092899)
        ·
          refine ⟨15580306636177189393639349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10386871090784792929092899 15580306636177189393639349)
          ·
            refine ⟨1460653747141611505653689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15580306636177189393639349 1460653747141611505653689)
            ·
              refine ⟨1095490310356208629240267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1460653747141611505653689 1095490310356208629240267)
              ·
                refine ⟨1643235465534312943860401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1095490310356208629240267 1643235465534312943860401)
                ·
                  refine ⟨1232426599150734707895301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1643235465534312943860401 1232426599150734707895301)
                  ·
                    refine ⟨231079987340762757730369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1232426599150734707895301 231079987340762757730369)
                    ·
                      rfl

theorem cell22_675040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 2, 4].length) (baseStart_675040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675040 prefixEnd_675040 := by exact prefixLift 675040
  have htrace : WordTrace (prefixWord ++ tailWord_675040) baseStart_675040 baseEnd_675040 := by
    simpa [prefixWord, tailWord_675040, baseEnd_675040] using wordTrace_append hprefix tailTrace_675040
  have hstable : (prefixWord ++ tailWord_675040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675040).length < 2 ^ (prefixWord ++ tailWord_675040).sum := by decide
  have hdescent : baseEnd_675040 < baseStart_675040 := by decide
  rcases family_descends (prefixWord ++ tailWord_675040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675117 : List Nat := [1, 5, 3, 1, 1, 2, 1, 1, 7]
def baseStart_675117 : Nat := 118140960795 + 675117 * 2 ^ 59
def prefixEnd_675117 : Nat := 4983230072969 + 3 ^ 40 * 675117 * 2
def baseEnd_675117 : Nat := 77035448671453407851711

theorem tailTrace_675117 : CollatzResearch.WordTrace tailWord_675117 prefixEnd_675117 77035448671453407851711 := by
  unfold tailWord_675117
  simp only [CollatzResearch.WordTrace]
  refine ⟨24623539895173884649143605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16415693263449256432762403 24623539895173884649143605)
  ·
    refine ⟨2308456865172551685857213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24623539895173884649143605 2308456865172551685857213)
    ·
      refine ⟨865671324439706882196455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2308456865172551685857213 865671324439706882196455)
      ·
        refine ⟨1298506986659560323294683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 865671324439706882196455 1298506986659560323294683)
        ·
          refine ⟨1947760479989340484942025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1298506986659560323294683 1947760479989340484942025)
          ·
            refine ⟨1460820359992005363706519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1947760479989340484942025 1460820359992005363706519)
            ·
              refine ⟨2191230539988008045559779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1460820359992005363706519 2191230539988008045559779)
              ·
                refine ⟨3286845809982012068339669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2191230539988008045559779 3286845809982012068339669)
                ·
                  refine ⟨77035448671453407851711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3286845809982012068339669 77035448671453407851711)
                  ·
                    rfl

theorem cell22_675117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_675117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675117 prefixEnd_675117 := by exact prefixLift 675117
  have htrace : WordTrace (prefixWord ++ tailWord_675117) baseStart_675117 baseEnd_675117 := by
    simpa [prefixWord, tailWord_675117, baseEnd_675117] using wordTrace_append hprefix tailTrace_675117
  have hstable : (prefixWord ++ tailWord_675117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675117).length < 2 ^ (prefixWord ++ tailWord_675117).sum := by decide
  have hdescent : baseEnd_675117 < baseStart_675117 := by decide
  rcases family_descends (prefixWord ++ tailWord_675117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675160 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 6, 3]
def baseStart_675160 : Nat := 118140960795 + 675160 * 2 ^ 59
def prefixEnd_675160 : Nat := 4983230072969 + 3 ^ 40 * 675160 * 2
def baseEnd_675160 : Nat := 231121065793122444730001

theorem tailTrace_675160 : CollatzResearch.WordTrace tailWord_675160 prefixEnd_675160 231121065793122444730001 := by
  unfold tailWord_675160
  simp only [CollatzResearch.WordTrace]
  refine ⟨12312554117009051496479467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16416738822678735328639289 12312554117009051496479467)
  ·
    refine ⟨18468831175513577244719201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12312554117009051496479467 18468831175513577244719201)
    ·
      refine ⟨13851623381635182933539401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18468831175513577244719201 13851623381635182933539401)
      ·
        refine ⟨10388717536226387200154551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13851623381635182933539401 10388717536226387200154551)
        ·
          refine ⟨15583076304339580800231827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10388717536226387200154551 15583076304339580800231827)
          ·
            refine ⟨23374614456509371200347741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15583076304339580800231827 23374614456509371200347741)
            ·
              refine ⟨8765480421191014200130403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23374614456509371200347741 8765480421191014200130403)
              ·
                refine ⟨13148220631786521300195605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8765480421191014200130403 13148220631786521300195605)
                ·
                  refine ⟨616322842114993185946669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13148220631786521300195605 616322842114993185946669)
                  ·
                    refine ⟨231121065793122444730001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 616322842114993185946669 231121065793122444730001)
                    ·
                      rfl

theorem cell22_675160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 6, 3].length) (baseStart_675160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675160 prefixEnd_675160 := by exact prefixLift 675160
  have htrace : WordTrace (prefixWord ++ tailWord_675160) baseStart_675160 baseEnd_675160 := by
    simpa [prefixWord, tailWord_675160, baseEnd_675160] using wordTrace_append hprefix tailTrace_675160
  have hstable : (prefixWord ++ tailWord_675160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675160).length < 2 ^ (prefixWord ++ tailWord_675160).sum := by decide
  have hdescent : baseEnd_675160 < baseStart_675160 := by decide
  rcases family_descends (prefixWord ++ tailWord_675160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675162 : List Nat := [3, 1, 1, 2, 1, 2, 5, 3, 4]
def baseStart_675162 : Nat := 118140960795 + 675162 * 2 ^ 59
def prefixEnd_675162 : Nat := 4983230072969 + 3 ^ 40 * 675162 * 2
def baseEnd_675162 : Nat := 77040583477998368726665

theorem tailTrace_675162 : CollatzResearch.WordTrace tailWord_675162 prefixEnd_675162 77040583477998368726665 := by
  unfold tailWord_675162
  simp only [CollatzResearch.WordTrace]
  refine ⟨6156295295002714333632935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16416787453340571556354493 6156295295002714333632935)
  ·
    refine ⟨9234442942504071500449403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6156295295002714333632935 9234442942504071500449403)
    ·
      refine ⟨13851664413756107250674105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9234442942504071500449403 13851664413756107250674105)
      ·
        refine ⟨10388748310317080438005579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13851664413756107250674105 10388748310317080438005579)
        ·
          refine ⟨15583122465475620657008369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10388748310317080438005579 15583122465475620657008369)
          ·
            refine ⟨11687341849106715492756277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15583122465475620657008369 11687341849106715492756277)
            ·
              refine ⟨1095688298353754577445901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11687341849106715492756277 1095688298353754577445901)
              ·
                refine ⟨410883111882657966542213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1095688298353754577445901 410883111882657966542213)
                ·
                  refine ⟨77040583477998368726665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 410883111882657966542213 77040583477998368726665)
                  ·
                    rfl

theorem cell22_675162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 3, 4].length) (baseStart_675162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675162 prefixEnd_675162 := by exact prefixLift 675162
  have htrace : WordTrace (prefixWord ++ tailWord_675162) baseStart_675162 baseEnd_675162 := by
    simpa [prefixWord, tailWord_675162, baseEnd_675162] using wordTrace_append hprefix tailTrace_675162
  have hstable : (prefixWord ++ tailWord_675162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675162).length < 2 ^ (prefixWord ++ tailWord_675162).sum := by decide
  have hdescent : baseEnd_675162 < baseStart_675162 := by decide
  rcases family_descends (prefixWord ++ tailWord_675162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675198 : List Nat := [4, 2, 3, 2, 1, 2, 1, 2, 1, 4]
def baseStart_675198 : Nat := 118140960795 + 675198 * 2 ^ 59
def prefixEnd_675198 : Nat := 4983230072969 + 3 ^ 40 * 675198 * 2
def baseEnd_675198 : Nat := 231134073969703012279885

theorem tailTrace_675198 : CollatzResearch.WordTrace tailWord_675198 prefixEnd_675198 231134073969703012279885 := by
  unfold tailWord_675198
  simp only [CollatzResearch.WordTrace]
  refine ⟨3078311775985054435355281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16417662805253623655228165 3078311775985054435355281)
  ·
    refine ⟨2308733831988790826516461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3078311775985054435355281 2308733831988790826516461)
    ·
      refine ⟨865775186995796559943673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2308733831988790826516461 865775186995796559943673)
      ·
        refine ⟨649331390246847419957755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 865775186995796559943673 649331390246847419957755)
        ·
          refine ⟨973997085370271129936633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 649331390246847419957755 973997085370271129936633)
          ·
            refine ⟨730497814027703347452475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 973997085370271129936633 730497814027703347452475)
            ·
              refine ⟨1095746721041555021178713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730497814027703347452475 1095746721041555021178713)
              ·
                refine ⟨821810040781166265884035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1095746721041555021178713 821810040781166265884035)
                ·
                  refine ⟨1232715061171749398826053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 821810040781166265884035 1232715061171749398826053)
                  ·
                    refine ⟨231134073969703012279885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1232715061171749398826053 231134073969703012279885)
                    ·
                      rfl

theorem cell22_675198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_675198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675198 prefixEnd_675198 := by exact prefixLift 675198
  have htrace : WordTrace (prefixWord ++ tailWord_675198) baseStart_675198 baseEnd_675198 := by
    simpa [prefixWord, tailWord_675198, baseEnd_675198] using wordTrace_append hprefix tailTrace_675198
  have hstable : (prefixWord ++ tailWord_675198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675198).length < 2 ^ (prefixWord ++ tailWord_675198).sum := by decide
  have hdescent : baseEnd_675198 < baseStart_675198 := by decide
  rcases family_descends (prefixWord ++ tailWord_675198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675230 : List Nat := [4, 3, 1, 2, 3, 1, 2, 2, 4]
def baseStart_675230 : Nat := 118140960795 + 675230 * 2 ^ 59
def prefixEnd_675230 : Nat := 4983230072969 + 3 ^ 40 * 675230 * 2
def baseEnd_675230 : Nat := 77048342741221865159929

theorem tailTrace_675230 : CollatzResearch.WordTrace tailWord_675230 prefixEnd_675230 77048342741221865159929 := by
  unfold tailWord_675230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3078457667970563118500893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16418440895843003298671429 3078457667970563118500893)
  ·
    refine ⟨1154421625488961169437835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3078457667970563118500893 1154421625488961169437835)
    ·
      refine ⟨1731632438233441754156753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1154421625488961169437835 1731632438233441754156753)
      ·
        refine ⟨1298724328675081315617565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1731632438233441754156753 1298724328675081315617565)
        ·
          refine ⟨487021623253155493356587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1298724328675081315617565 487021623253155493356587)
          ·
            refine ⟨730532434879733240034881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487021623253155493356587 730532434879733240034881)
            ·
              refine ⟨547899326159799930026161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 730532434879733240034881 547899326159799930026161)
              ·
                refine ⟨410924494619849947519621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 547899326159799930026161 410924494619849947519621)
                ·
                  refine ⟨77048342741221865159929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 410924494619849947519621 77048342741221865159929)
                  ·
                    rfl

theorem cell22_675230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_675230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675230 prefixEnd_675230 := by exact prefixLift 675230
  have htrace : WordTrace (prefixWord ++ tailWord_675230) baseStart_675230 baseEnd_675230 := by
    simpa [prefixWord, tailWord_675230, baseEnd_675230] using wordTrace_append hprefix tailTrace_675230
  have hstable : (prefixWord ++ tailWord_675230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675230).length < 2 ^ (prefixWord ++ tailWord_675230).sum := by decide
  have hdescent : baseEnd_675230 < baseStart_675230 := by decide
  rcases family_descends (prefixWord ++ tailWord_675230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675286 : List Nat := [5, 2, 1, 1, 1, 4, 1, 2, 5]
def baseStart_675286 : Nat := 118140960795 + 675286 * 2 ^ 59
def prefixEnd_675286 : Nat := 4983230072969 + 3 ^ 40 * 675286 * 2
def baseEnd_675286 : Nat := 77054732722700038693205

theorem tailTrace_675286 : CollatzResearch.WordTrace tailWord_675286 prefixEnd_675286 77054732722700038693205 := by
  unfold tailWord_675286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1539356489472601657002857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16419802554374417674697141 1539356489472601657002857)
  ·
    refine ⟨1154517367104451242752143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1539356489472601657002857 1154517367104451242752143)
    ·
      refine ⟨1731776050656676864128215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1154517367104451242752143 1731776050656676864128215)
      ·
        refine ⟨2597664075985015296192323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1731776050656676864128215 2597664075985015296192323)
        ·
          refine ⟨3896496113977522944288485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2597664075985015296192323 3896496113977522944288485)
          ·
            refine ⟨730593021370785552054091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3896496113977522944288485 730593021370785552054091)
            ·
              refine ⟨1095889532056178328081137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730593021370785552054091 1095889532056178328081137)
              ·
                refine ⟨821917149042133746060853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1095889532056178328081137 821917149042133746060853)
                ·
                  refine ⟨77054732722700038693205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 821917149042133746060853 77054732722700038693205)
                  ·
                    rfl

theorem cell22_675286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_675286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675286 prefixEnd_675286 := by exact prefixLift 675286
  have htrace : WordTrace (prefixWord ++ tailWord_675286) baseStart_675286 baseEnd_675286 := by
    simpa [prefixWord, tailWord_675286, baseEnd_675286] using wordTrace_append hprefix tailTrace_675286
  have hstable : (prefixWord ++ tailWord_675286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675286).length < 2 ^ (prefixWord ++ tailWord_675286).sum := by decide
  have hdescent : baseEnd_675286 < baseStart_675286 := by decide
  rcases family_descends (prefixWord ++ tailWord_675286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675297 : List Nat := [1, 2, 3, 1, 2, 4, 2, 1, 6]
def baseStart_675297 : Nat := 118140960795 + 675297 * 2 ^ 59
def prefixEnd_675297 : Nat := 4983230072969 + 3 ^ 40 * 675297 * 2
def baseEnd_675297 : Nat := 77055987897633251351527

theorem tailTrace_675297 : CollatzResearch.WordTrace tailWord_675297 prefixEnd_675297 77055987897633251351527 := by
  unfold tailWord_675297
  simp only [CollatzResearch.WordTrace]
  refine ⟨24630105034521775390696145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16420070023014516927130763 24630105034521775390696145)
  ·
    refine ⟨18472578775891331543022109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24630105034521775390696145 18472578775891331543022109)
    ·
      refine ⟨6927217040959249328633291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18472578775891331543022109 6927217040959249328633291)
      ·
        refine ⟨10390825561438873992949937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6927217040959249328633291 10390825561438873992949937)
        ·
          refine ⟨7793119171079155494712453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10390825561438873992949937 7793119171079155494712453)
          ·
            refine ⟨1461209844577341655258585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7793119171079155494712453 1461209844577341655258585)
            ·
              refine ⟨1095907383433006241443939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1461209844577341655258585 1095907383433006241443939)
              ·
                refine ⟨1643861075149509362165909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1095907383433006241443939 1643861075149509362165909)
                ·
                  refine ⟨77055987897633251351527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1643861075149509362165909 77055987897633251351527)
                  ·
                    rfl

theorem cell22_675297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 6].length) (baseStart_675297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675297 prefixEnd_675297 := by exact prefixLift 675297
  have htrace : WordTrace (prefixWord ++ tailWord_675297) baseStart_675297 baseEnd_675297 := by
    simpa [prefixWord, tailWord_675297, baseEnd_675297] using wordTrace_append hprefix tailTrace_675297
  have hstable : (prefixWord ++ tailWord_675297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675297).length < 2 ^ (prefixWord ++ tailWord_675297).sum := by decide
  have hdescent : baseEnd_675297 < baseStart_675297 := by decide
  rcases family_descends (prefixWord ++ tailWord_675297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675312 : List Nat := [2, 1, 1, 1, 3, 4, 3, 1, 1, 5]
def baseStart_675312 : Nat := 118140960795 + 675312 * 2 ^ 59
def prefixEnd_675312 : Nat := 4983230072969 + 3 ^ 40 * 675312 * 2
def baseEnd_675312 : Nat := 231173098499444714929535

theorem tailTrace_675312 : CollatzResearch.WordTrace tailWord_675312 prefixEnd_675312 231173098499444714929535 := by
  unfold tailWord_675312
  simp only [CollatzResearch.WordTrace]
  refine ⟨12315326064733716476246095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16420434752978288634994793 12315326064733716476246095)
  ·
    refine ⟨18472989097100574714369143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12315326064733716476246095 18472989097100574714369143)
    ·
      refine ⟨27709483645650862071553715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18472989097100574714369143 27709483645650862071553715)
      ·
        refine ⟨41564225468476293107330573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27709483645650862071553715 41564225468476293107330573)
        ·
          refine ⟨15586584550678609915248965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41564225468476293107330573 15586584550678609915248965)
          ·
            refine ⟨2922484603252239359109181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15586584550678609915248965 2922484603252239359109181)
            ·
              refine ⟨1095931726219589759665943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2922484603252239359109181 1095931726219589759665943)
              ·
                refine ⟨1643897589329384639498915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1095931726219589759665943 1643897589329384639498915)
                ·
                  refine ⟨2465846383994076959248373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1643897589329384639498915 2465846383994076959248373)
                  ·
                    refine ⟨231173098499444714929535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2465846383994076959248373 231173098499444714929535)
                    ·
                      rfl

theorem cell22_675312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 1, 5].length) (baseStart_675312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675312 prefixEnd_675312 := by exact prefixLift 675312
  have htrace : WordTrace (prefixWord ++ tailWord_675312) baseStart_675312 baseEnd_675312 := by
    simpa [prefixWord, tailWord_675312, baseEnd_675312] using wordTrace_append hprefix tailTrace_675312
  have hstable : (prefixWord ++ tailWord_675312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675312).length < 2 ^ (prefixWord ++ tailWord_675312).sum := by decide
  have hdescent : baseEnd_675312 < baseStart_675312 := by decide
  rcases family_descends (prefixWord ++ tailWord_675312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675348 : List Nat := [2, 4, 3, 1, 3, 1, 1, 1, 6]
def baseStart_675348 : Nat := 118140960795 + 675348 * 2 ^ 59
def prefixEnd_675348 : Nat := 4983230072969 + 3 ^ 40 * 675348 * 2
def baseEnd_675348 : Nat := 77061807345050873676475

theorem tailTrace_675348 : CollatzResearch.WordTrace tailWord_675348 prefixEnd_675348 77061807345050873676475 := by
  unfold tailWord_675348
  simp only [CollatzResearch.WordTrace]
  refine ⟨12315982578668505550401349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16421310104891340733868465 12315982578668505550401349)
  ·
    refine ⟨2309246733500344790700253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12315982578668505550401349 2309246733500344790700253)
    ·
      refine ⟨865967525062629296512595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2309246733500344790700253 865967525062629296512595)
      ·
        refine ⟨1298951287593943944768893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 865967525062629296512595 1298951287593943944768893)
        ·
          refine ⟨487106732847728979288335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1298951287593943944768893 487106732847728979288335)
          ·
            refine ⟨730660099271593468932503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487106732847728979288335 730660099271593468932503)
            ·
              refine ⟨1095990148907390203398755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730660099271593468932503 1095990148907390203398755)
              ·
                refine ⟨1643985223361085305098133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1095990148907390203398755 1643985223361085305098133)
                ·
                  refine ⟨77061807345050873676475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1643985223361085305098133 77061807345050873676475)
                  ·
                    rfl

theorem cell22_675348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_675348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675348 prefixEnd_675348 := by exact prefixLift 675348
  have htrace : WordTrace (prefixWord ++ tailWord_675348) baseStart_675348 baseEnd_675348 := by
    simpa [prefixWord, tailWord_675348, baseEnd_675348] using wordTrace_append hprefix tailTrace_675348
  have hstable : (prefixWord ++ tailWord_675348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675348).length < 2 ^ (prefixWord ++ tailWord_675348).sum := by decide
  have hdescent : baseEnd_675348 < baseStart_675348 := by decide
  rcases family_descends (prefixWord ++ tailWord_675348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675363 : List Nat := [1, 1, 1, 4, 5, 2, 2, 1, 2, 3]
def baseStart_675363 : Nat := 118140960795 + 675363 * 2 ^ 59
def prefixEnd_675363 : Nat := 4983230072969 + 3 ^ 40 * 675363 * 2
def baseEnd_675363 : Nat := 231190556841697581904379

theorem tailTrace_675363 : CollatzResearch.WordTrace tailWord_675363 prefixEnd_675363 231190556841697581904379 := by
  unfold tailWord_675363
  simp only [CollatzResearch.WordTrace]
  refine ⟨24632512252282668662598743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16421674834855112441732495 24632512252282668662598743)
  ·
    refine ⟨36948768378424002993898115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24632512252282668662598743 36948768378424002993898115)
    ·
      refine ⟨55423152567636004490847173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36948768378424002993898115 55423152567636004490847173)
      ·
        refine ⟨10391841106431750842033845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55423152567636004490847173 10391841106431750842033845)
        ·
          refine ⟨974235103727976641440673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10391841106431750842033845 974235103727976641440673)
          ·
            refine ⟨730676327795982481080505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 974235103727976641440673 730676327795982481080505)
            ·
              refine ⟨548007245846986860810379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 730676327795982481080505 548007245846986860810379)
              ·
                refine ⟨822010868770480291215569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 548007245846986860810379 822010868770480291215569)
                ·
                  refine ⟨616508151577860218411677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 822010868770480291215569 616508151577860218411677)
                  ·
                    refine ⟨231190556841697581904379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 616508151577860218411677 231190556841697581904379)
                    ·
                      rfl

theorem cell22_675363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 2, 3].length) (baseStart_675363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675363 prefixEnd_675363 := by exact prefixLift 675363
  have htrace : WordTrace (prefixWord ++ tailWord_675363) baseStart_675363 baseEnd_675363 := by
    simpa [prefixWord, tailWord_675363, baseEnd_675363] using wordTrace_append hprefix tailTrace_675363
  have hstable : (prefixWord ++ tailWord_675363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675363).length < 2 ^ (prefixWord ++ tailWord_675363).sum := by decide
  have hdescent : baseEnd_675363 < baseStart_675363 := by decide
  rcases family_descends (prefixWord ++ tailWord_675363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675402 : List Nat := [3, 1, 2, 1, 1, 3, 2, 2, 2, 5]
def baseStart_675402 : Nat := 118140960795 + 675402 * 2 ^ 59
def prefixEnd_675402 : Nat := 4983230072969 + 3 ^ 40 * 675402 * 2
def baseEnd_675402 : Nat := 231203907338714480179259

theorem tailTrace_675402 : CollatzResearch.WordTrace tailWord_675402 prefixEnd_675402 231203907338714480179259 := by
  unfold tailWord_675402
  simp only [CollatzResearch.WordTrace]
  refine ⟨6158483674785344580817115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16422623132760918882178973 6158483674785344580817115)
  ·
    refine ⟨9237725512178016871225673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6158483674785344580817115 9237725512178016871225673)
    ·
      refine ⟨6928294134133512653419255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9237725512178016871225673 6928294134133512653419255)
      ·
        refine ⟨10392441201200268980128883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6928294134133512653419255 10392441201200268980128883)
        ·
          refine ⟨15588661801800403470193325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10392441201200268980128883 15588661801800403470193325)
          ·
            refine ⟨5845748175675151301322497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15588661801800403470193325 5845748175675151301322497)
            ·
              refine ⟨4384311131756363475991873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5845748175675151301322497 4384311131756363475991873)
              ·
                refine ⟨3288233348817272606993905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4384311131756363475991873 3288233348817272606993905)
                ·
                  refine ⟨2466175011612954455245429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3288233348817272606993905 2466175011612954455245429)
                  ·
                    refine ⟨231203907338714480179259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2466175011612954455245429 231203907338714480179259)
                    ·
                      rfl

theorem cell22_675402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_675402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675402 prefixEnd_675402 := by exact prefixLift 675402
  have htrace : WordTrace (prefixWord ++ tailWord_675402) baseStart_675402 baseEnd_675402 := by
    simpa [prefixWord, tailWord_675402, baseEnd_675402] using wordTrace_append hprefix tailTrace_675402
  have hstable : (prefixWord ++ tailWord_675402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675402).length < 2 ^ (prefixWord ++ tailWord_675402).sum := by decide
  have hdescent : baseEnd_675402 < baseStart_675402 := by decide
  rcases family_descends (prefixWord ++ tailWord_675402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675404 : List Nat := [2, 2, 1, 3, 1, 4, 2, 2, 5]
def baseStart_675404 : Nat := 118140960795 + 675404 * 2 ^ 59
def prefixEnd_675404 : Nat := 4983230072969 + 3 ^ 40 * 675404 * 2
def baseEnd_675404 : Nat := 77068197326529047209751

theorem tailTrace_675404 : CollatzResearch.WordTrace tailWord_675404 prefixEnd_675404 77068197326529047209751 := by
  unfold tailWord_675404
  simp only [CollatzResearch.WordTrace]
  refine ⟨12317003822567066332420633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16422671763422755109894177 12317003822567066332420633)
  ·
    refine ⟨9237752866925299749315475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12317003822567066332420633 9237752866925299749315475)
    ·
      refine ⟨13856629300387949623973213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9237752866925299749315475 13856629300387949623973213)
      ·
        refine ⟨5196235987645481108989955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13856629300387949623973213 5196235987645481108989955)
        ·
          refine ⟨7794353981468221663484933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5196235987645481108989955 7794353981468221663484933)
          ·
            refine ⟨1461441371525291561903425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7794353981468221663484933 1461441371525291561903425)
            ·
              refine ⟨1096081028643968671427569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1461441371525291561903425 1096081028643968671427569)
              ·
                refine ⟨822060771482976503570677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1096081028643968671427569 822060771482976503570677)
                ·
                  refine ⟨77068197326529047209751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 822060771482976503570677 77068197326529047209751)
                  ·
                    rfl

theorem cell22_675404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 5].length) (baseStart_675404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675404 prefixEnd_675404 := by exact prefixLift 675404
  have htrace : WordTrace (prefixWord ++ tailWord_675404) baseStart_675404 baseEnd_675404 := by
    simpa [prefixWord, tailWord_675404, baseEnd_675404] using wordTrace_append hprefix tailTrace_675404
  have hstable : (prefixWord ++ tailWord_675404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675404).length < 2 ^ (prefixWord ++ tailWord_675404).sum := by decide
  have hdescent : baseEnd_675404 < baseStart_675404 := by decide
  rcases family_descends (prefixWord ++ tailWord_675404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675434 : List Nat := [3, 1, 3, 2, 1, 2, 2, 1, 3, 4]
def baseStart_675434 : Nat := 118140960795 + 675434 * 2 ^ 59
def prefixEnd_675434 : Nat := 4983230072969 + 3 ^ 40 * 675434 * 2
def baseEnd_675434 : Nat := 231214861592677063379161

theorem tailTrace_675434 : CollatzResearch.WordTrace tailWord_675434 prefixEnd_675434 231214861592677063379161 := by
  unfold tailWord_675434
  simp only [CollatzResearch.WordTrace]
  refine ⟨6158775458756361947108339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16423401223350298525622237 6158775458756361947108339)
  ·
    refine ⟨9238163188134542920662509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6158775458756361947108339 9238163188134542920662509)
    ·
      refine ⟨3464311195550453595248441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9238163188134542920662509 3464311195550453595248441)
      ·
        refine ⟨2598233396662840196436331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3464311195550453595248441 2598233396662840196436331)
        ·
          refine ⟨3897350094994260294654497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2598233396662840196436331 3897350094994260294654497)
          ·
            refine ⟨2923012571245695220990873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3897350094994260294654497 2923012571245695220990873)
            ·
              refine ⟨2192259428434271415743155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2923012571245695220990873 2192259428434271415743155)
              ·
                refine ⟨3288389142651407123614733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2192259428434271415743155 3288389142651407123614733)
                ·
                  refine ⟨1233145928494277671355525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3288389142651407123614733 1233145928494277671355525)
                  ·
                    refine ⟨231214861592677063379161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1233145928494277671355525 231214861592677063379161)
                    ·
                      rfl

theorem cell22_675434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_675434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675434 prefixEnd_675434 := by exact prefixLift 675434
  have htrace : WordTrace (prefixWord ++ tailWord_675434) baseStart_675434 baseEnd_675434 := by
    simpa [prefixWord, tailWord_675434, baseEnd_675434] using wordTrace_append hprefix tailTrace_675434
  have hstable : (prefixWord ++ tailWord_675434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675434).length < 2 ^ (prefixWord ++ tailWord_675434).sum := by decide
  have hdescent : baseEnd_675434 < baseStart_675434 := by decide
  rcases family_descends (prefixWord ++ tailWord_675434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675466 : List Nat := [3, 1, 2, 3, 2, 1, 2, 4, 4]
def baseStart_675466 : Nat := 118140960795 + 675466 * 2 ^ 59
def prefixEnd_675466 : Nat := 4983230072969 + 3 ^ 40 * 675466 * 2
def baseEnd_675466 : Nat := 77075271948879882193021

theorem tailTrace_675466 : CollatzResearch.WordTrace tailWord_675466 prefixEnd_675466 77075271948879882193021 := by
  unfold tailWord_675466
  simp only [CollatzResearch.WordTrace]
  refine ⟨6159067242727379313399563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16424179313939678169065501 6159067242727379313399563)
  ·
    refine ⟨9238600864091068970099345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6159067242727379313399563 9238600864091068970099345)
    ·
      refine ⟨6928950648068301727574509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9238600864091068970099345 6928950648068301727574509)
      ·
        refine ⟨2598356493025613147840441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6928950648068301727574509 2598356493025613147840441)
        ·
          refine ⟨1948767369769209860880331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2598356493025613147840441 1948767369769209860880331)
          ·
            refine ⟨2923151054653814791320497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1948767369769209860880331 2923151054653814791320497)
            ·
              refine ⟨2192363290990361093490373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2923151054653814791320497 2192363290990361093490373)
              ·
                refine ⟨411068117060692705029445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2192363290990361093490373 411068117060692705029445)
                ·
                  refine ⟨77075271948879882193021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 411068117060692705029445 77075271948879882193021)
                  ·
                    rfl

theorem cell22_675466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 4, 4].length) (baseStart_675466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675466 prefixEnd_675466 := by exact prefixLift 675466
  have htrace : WordTrace (prefixWord ++ tailWord_675466) baseStart_675466 baseEnd_675466 := by
    simpa [prefixWord, tailWord_675466, baseEnd_675466] using wordTrace_append hprefix tailTrace_675466
  have hstable : (prefixWord ++ tailWord_675466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675466).length < 2 ^ (prefixWord ++ tailWord_675466).sum := by decide
  have hdescent : baseEnd_675466 < baseStart_675466 := by decide
  rcases family_descends (prefixWord ++ tailWord_675466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675524 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 2, 6]
def baseStart_675524 : Nat := 118140960795 + 675524 * 2 ^ 59
def prefixEnd_675524 : Nat := 4983230072969 + 3 ^ 40 * 675524 * 2
def baseEnd_675524 : Nat := 231245670431946828628885

theorem tailTrace_675524 : CollatzResearch.WordTrace tailWord_675524 prefixEnd_675524 231245670431946828628885 := by
  unfold tailWord_675524
  simp only [CollatzResearch.WordTrace]
  refine ⟨12319192202349696579604813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16425589603132928772806417 12319192202349696579604813)
  ·
    refine ⟨4619697075881136217351805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12319192202349696579604813 4619697075881136217351805)
    ·
      refine ⟨1732386403455426081506927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4619697075881136217351805 1732386403455426081506927)
      ·
        refine ⟨2598579605183139122260391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1732386403455426081506927 2598579605183139122260391)
        ·
          refine ⟨3897869407774708683390587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2598579605183139122260391 3897869407774708683390587)
          ·
            refine ⟨5846804111662063025085881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3897869407774708683390587 5846804111662063025085881)
            ·
              refine ⟨4385103083746547268814411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5846804111662063025085881 4385103083746547268814411)
              ·
                refine ⟨6577654625619820903221617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4385103083746547268814411 6577654625619820903221617)
                ·
                  refine ⟨4933240969214865677416213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6577654625619820903221617 4933240969214865677416213)
                  ·
                    refine ⟨231245670431946828628885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4933240969214865677416213 231245670431946828628885)
                    ·
                      rfl

theorem cell22_675524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_675524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675524 prefixEnd_675524 := by exact prefixLift 675524
  have htrace : WordTrace (prefixWord ++ tailWord_675524) baseStart_675524 baseEnd_675524 := by
    simpa [prefixWord, tailWord_675524, baseEnd_675524] using wordTrace_append hprefix tailTrace_675524
  have hstable : (prefixWord ++ tailWord_675524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675524).length < 2 ^ (prefixWord ++ tailWord_675524).sum := by decide
  have hdescent : baseEnd_675524 < baseStart_675524 := by decide
  rcases family_descends (prefixWord ++ tailWord_675524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675532 : List Nat := [2, 2, 1, 5, 3, 1, 2, 1, 2, 3]
def baseStart_675532 : Nat := 118140960795 + 675532 * 2 ^ 59
def prefixEnd_675532 : Nat := 4983230072969 + 3 ^ 40 * 675532 * 2
def baseEnd_675532 : Nat := 231248408995437474428861

theorem tailTrace_675532 : CollatzResearch.WordTrace tailWord_675532 prefixEnd_675532 231248408995437474428861 := by
  unfold tailWord_675532
  simp only [CollatzResearch.WordTrace]
  refine ⟨12319338094335205262750425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16425784125780273683667233 12319338094335205262750425)
  ·
    refine ⟨9239503570751403947062819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12319338094335205262750425 9239503570751403947062819)
    ·
      refine ⟨13859255356127105920594229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9239503570751403947062819 13859255356127105920594229)
      ·
        refine ⟨1299305189636916180055709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13859255356127105920594229 1299305189636916180055709)
        ·
          refine ⟨487239446113843567520891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1299305189636916180055709 487239446113843567520891)
          ·
            refine ⟨730859169170765351281337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487239446113843567520891 730859169170765351281337)
            ·
              refine ⟨548144376878074013461003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 730859169170765351281337 548144376878074013461003)
              ·
                refine ⟨822216565317111020191505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 548144376878074013461003 822216565317111020191505)
                ·
                  refine ⟨616662423987833265143629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 822216565317111020191505 616662423987833265143629)
                  ·
                    refine ⟨231248408995437474428861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 616662423987833265143629 231248408995437474428861)
                    ·
                      rfl

theorem cell22_675532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 2, 3].length) (baseStart_675532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675532 prefixEnd_675532 := by exact prefixLift 675532
  have htrace : WordTrace (prefixWord ++ tailWord_675532) baseStart_675532 baseEnd_675532 := by
    simpa [prefixWord, tailWord_675532, baseEnd_675532] using wordTrace_append hprefix tailTrace_675532
  have hstable : (prefixWord ++ tailWord_675532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675532).length < 2 ^ (prefixWord ++ tailWord_675532).sum := by decide
  have hdescent : baseEnd_675532 < baseStart_675532 := by decide
  rcases family_descends (prefixWord ++ tailWord_675532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675586 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_675586 : Nat := 118140960795 + 675586 * 2 ^ 59
def prefixEnd_675586 : Nat := 4983230072969 + 3 ^ 40 * 675586 * 2
def baseEnd_675586 : Nat := 231266894298999333578695

theorem tailTrace_675586 : CollatzResearch.WordTrace tailWord_675586 prefixEnd_675586 231266894298999333578695 := by
  unfold tailWord_675586
  simp only [CollatzResearch.WordTrace]
  refine ⟨6160161432618694436991653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16427097153649851831977741 6160161432618694436991653)
  ·
    refine ⟨1155030268616005206935935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6160161432618694436991653 1155030268616005206935935)
    ·
      refine ⟨1732545402924007810403903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1155030268616005206935935 1732545402924007810403903)
      ·
        refine ⟨2598818104386011715605855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1732545402924007810403903 2598818104386011715605855)
        ·
          refine ⟨3898227156579017573408783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2598818104386011715605855 3898227156579017573408783)
          ·
            refine ⟨5847340734868526360113175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3898227156579017573408783 5847340734868526360113175)
            ·
              refine ⟨8771011102302789540169763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5847340734868526360113175 8771011102302789540169763)
              ·
                refine ⟨13156516653454184310254645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8771011102302789540169763 13156516653454184310254645)
                ·
                  refine ⟨1233423436261329779086373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13156516653454184310254645 1233423436261329779086373)
                  ·
                    refine ⟨231266894298999333578695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1233423436261329779086373 231266894298999333578695)
                    ·
                      rfl

theorem cell22_675586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_675586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675586 prefixEnd_675586 := by exact prefixLift 675586
  have htrace : WordTrace (prefixWord ++ tailWord_675586) baseStart_675586 baseEnd_675586 := by
    simpa [prefixWord, tailWord_675586, baseEnd_675586] using wordTrace_append hprefix tailTrace_675586
  have hstable : (prefixWord ++ tailWord_675586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675586).length < 2 ^ (prefixWord ++ tailWord_675586).sum := by decide
  have hdescent : baseEnd_675586 < baseStart_675586 := by decide
  rcases family_descends (prefixWord ++ tailWord_675586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675616 : List Nat := [2, 1, 1, 5, 1, 1, 2, 2, 4, 3]
def baseStart_675616 : Nat := 118140960795 + 675616 * 2 ^ 59
def prefixEnd_675616 : Nat := 4983230072969 + 3 ^ 40 * 675616 * 2
def baseEnd_675616 : Nat := 231277163912089255328603

theorem tailTrace_675616 : CollatzResearch.WordTrace tailWord_675616 prefixEnd_675616 231277163912089255328603 := by
  unfold tailWord_675616
  simp only [CollatzResearch.WordTrace]
  refine ⟨12320869960183046435779351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16427826613577395247705801 12320869960183046435779351)
  ·
    refine ⟨18481304940274569653669027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12320869960183046435779351 18481304940274569653669027)
    ·
      refine ⟨27721957410411854480503541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18481304940274569653669027 27721957410411854480503541)
      ·
        refine ⟨2598933507226111357547207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27721957410411854480503541 2598933507226111357547207)
        ·
          refine ⟨3898400260839167036320811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2598933507226111357547207 3898400260839167036320811)
          ·
            refine ⟨5847600391258750554481217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3898400260839167036320811 5847600391258750554481217)
            ·
              refine ⟨4385700293444062915860913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5847600391258750554481217 4385700293444062915860913)
              ·
                refine ⟨3289275220083047186895685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4385700293444062915860913 3289275220083047186895685)
                ·
                  refine ⟨616739103765571347542941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3289275220083047186895685 616739103765571347542941)
                  ·
                    refine ⟨231277163912089255328603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 616739103765571347542941 231277163912089255328603)
                    ·
                      rfl

theorem cell22_675616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 4, 3].length) (baseStart_675616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675616 prefixEnd_675616 := by exact prefixLift 675616
  have htrace : WordTrace (prefixWord ++ tailWord_675616) baseStart_675616 baseEnd_675616 := by
    simpa [prefixWord, tailWord_675616, baseEnd_675616] using wordTrace_append hprefix tailTrace_675616
  have hstable : (prefixWord ++ tailWord_675616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675616).length < 2 ^ (prefixWord ++ tailWord_675616).sum := by decide
  have hdescent : baseEnd_675616 < baseStart_675616 := by decide
  rcases family_descends (prefixWord ++ tailWord_675616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675618 : List Nat := [3, 3, 1, 1, 2, 1, 4, 3, 4]
def baseStart_675618 : Nat := 118140960795 + 675618 * 2 ^ 59
def prefixEnd_675618 : Nat := 4983230072969 + 3 ^ 40 * 675618 * 2
def baseEnd_675618 : Nat := 77092616184320638926199

theorem tailTrace_675618 : CollatzResearch.WordTrace tailWord_675618 prefixEnd_675618 77092616184320638926199 := by
  unfold tailWord_675618
  simp only [CollatzResearch.WordTrace]
  refine ⟨6160453216589711803282877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16427875244239231475421005 6160453216589711803282877)
  ·
    refine ⟨2310169956221141926231079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6160453216589711803282877 2310169956221141926231079)
    ·
      refine ⟨3465254934331712889346619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2310169956221141926231079 3465254934331712889346619)
      ·
        refine ⟨5197882401497569334019929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3465254934331712889346619 5197882401497569334019929)
        ·
          refine ⟨3898411801123177000514947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5197882401497569334019929 3898411801123177000514947)
          ·
            refine ⟨5847617701684765500772421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3898411801123177000514947 5847617701684765500772421)
            ·
              refine ⟨1096428319065893531394829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5847617701684765500772421 1096428319065893531394829)
              ·
                refine ⟨411160619649710074273061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1096428319065893531394829 411160619649710074273061)
                ·
                  refine ⟨77092616184320638926199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 411160619649710074273061 77092616184320638926199)
                  ·
                    rfl

theorem cell22_675618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_675618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675618 prefixEnd_675618 := by exact prefixLift 675618
  have htrace : WordTrace (prefixWord ++ tailWord_675618) baseStart_675618 baseEnd_675618 := by
    simpa [prefixWord, tailWord_675618, baseEnd_675618] using wordTrace_append hprefix tailTrace_675618
  have hstable : (prefixWord ++ tailWord_675618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675618).length < 2 ^ (prefixWord ++ tailWord_675618).sum := by decide
  have hdescent : baseEnd_675618 < baseStart_675618 := by decide
  rcases family_descends (prefixWord ++ tailWord_675618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675620 : List Nat := [2, 3, 1, 3, 2, 3, 2, 1, 1, 4]
def baseStart_675620 : Nat := 118140960795 + 675620 * 2 ^ 59
def prefixEnd_675620 : Nat := 4983230072969 + 3 ^ 40 * 675620 * 2
def baseEnd_675620 : Nat := 231278533193834578228591

theorem tailTrace_675620 : CollatzResearch.WordTrace tailWord_675620 prefixEnd_675620 231278533193834578228591 := by
  unfold tailWord_675620
  simp only [CollatzResearch.WordTrace]
  refine ⟨12320942906175800777352157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16427923874901067703136209 12320942906175800777352157)
  ·
    refine ⟨4620353589815925291507059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12320942906175800777352157 4620353589815925291507059)
    ·
      refine ⟨6930530384723887937260589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4620353589815925291507059 6930530384723887937260589)
      ·
        refine ⟨2598948894271457976472721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6930530384723887937260589 2598948894271457976472721)
        ·
          refine ⟨1949211670703593482354541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2598948894271457976472721 1949211670703593482354541)
          ·
            refine ⟨730954376513847555882953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1949211670703593482354541 730954376513847555882953)
            ·
              refine ⟨548215782385385666912215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 730954376513847555882953 548215782385385666912215)
              ·
                refine ⟨822323673578078500368323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 548215782385385666912215 822323673578078500368323)
                ·
                  refine ⟨1233485510367117750552485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 822323673578078500368323 1233485510367117750552485)
                  ·
                    refine ⟨231278533193834578228591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1233485510367117750552485 231278533193834578228591)
                    ·
                      rfl

theorem cell22_675620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_675620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675620 prefixEnd_675620 := by exact prefixLift 675620
  have htrace : WordTrace (prefixWord ++ tailWord_675620) baseStart_675620 baseEnd_675620 := by
    simpa [prefixWord, tailWord_675620, baseEnd_675620] using wordTrace_append hprefix tailTrace_675620
  have hstable : (prefixWord ++ tailWord_675620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675620).length < 2 ^ (prefixWord ++ tailWord_675620).sum := by decide
  have hdescent : baseEnd_675620 < baseStart_675620 := by decide
  rcases family_descends (prefixWord ++ tailWord_675620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675633 : List Nat := [1, 2, 2, 3, 2, 2, 3, 2, 2, 3]
def baseStart_675633 : Nat := 118140960795 + 675633 * 2 ^ 59
def prefixEnd_675633 : Nat := 4983230072969 + 3 ^ 40 * 675633 * 2
def baseEnd_675633 : Nat := 231282983359506877653551

theorem tailTrace_675633 : CollatzResearch.WordTrace tailWord_675633 prefixEnd_675633 231282983359506877653551 := by
  unfold tailWord_675633
  simp only [CollatzResearch.WordTrace]
  refine ⟨24642359961304504774927553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16428239974203003183285035 24642359961304504774927553)
  ·
    refine ⟨18481769970978378581195665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24642359961304504774927553 18481769970978378581195665)
    ·
      refine ⟨13861327478233783935896749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18481769970978378581195665 13861327478233783935896749)
      ·
        refine ⟨5197997804337668975961281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13861327478233783935896749 5197997804337668975961281)
        ·
          refine ⟨3898498353253251731970961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5197997804337668975961281 3898498353253251731970961)
          ·
            refine ⟨2923873764939938798978221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3898498353253251731970961 2923873764939938798978221)
            ·
              refine ⟨1096452661852477049616833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2923873764939938798978221 1096452661852477049616833)
              ·
                refine ⟨822339496389357787212625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1096452661852477049616833 822339496389357787212625)
                ·
                  refine ⟨616754622292018340409469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 822339496389357787212625 616754622292018340409469)
                  ·
                    refine ⟨231282983359506877653551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 616754622292018340409469 231282983359506877653551)
                    ·
                      rfl

theorem cell22_675633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 2, 3].length) (baseStart_675633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675633 prefixEnd_675633 := by exact prefixLift 675633
  have htrace : WordTrace (prefixWord ++ tailWord_675633) baseStart_675633 baseEnd_675633 := by
    simpa [prefixWord, tailWord_675633, baseEnd_675633] using wordTrace_append hprefix tailTrace_675633
  have hstable : (prefixWord ++ tailWord_675633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675633).length < 2 ^ (prefixWord ++ tailWord_675633).sum := by decide
  have hdescent : baseEnd_675633 < baseStart_675633 := by decide
  rcases family_descends (prefixWord ++ tailWord_675633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675674 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 9]
def baseStart_675674 : Nat := 118140960795 + 675674 * 2 ^ 59
def prefixEnd_675674 : Nat := 4983230072969 + 3 ^ 40 * 675674 * 2
def baseEnd_675674 : Nat := 77099006165798812459475

theorem tailTrace_675674 : CollatzResearch.WordTrace tailWord_675674 prefixEnd_675674 77099006165798812459475 := by
  unfold tailWord_675674
  simp only [CollatzResearch.WordTrace]
  refine ⟨6160963838538992194292519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16429236902770645851446717 6160963838538992194292519)
  ·
    refine ⟨9241445757808488291438779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6160963838538992194292519 9241445757808488291438779)
    ·
      refine ⟨13862168636712732437158169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9241445757808488291438779 13862168636712732437158169)
      ·
        refine ⟨10396626477534549327868627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13862168636712732437158169 10396626477534549327868627)
        ·
          refine ⟨15594939716301823991802941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10396626477534549327868627 15594939716301823991802941)
          ·
            refine ⟨5848102393613183996926103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15594939716301823991802941 5848102393613183996926103)
            ·
              refine ⟨8772153590419775995389155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5848102393613183996926103 8772153590419775995389155)
              ·
                refine ⟨13158230385629663993083733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8772153590419775995389155 13158230385629663993083733)
                ·
                  refine ⟨77099006165798812459475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13158230385629663993083733 77099006165798812459475)
                  ·
                    rfl

theorem cell22_675674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 9].length) (baseStart_675674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675674 prefixEnd_675674 := by exact prefixLift 675674
  have htrace : WordTrace (prefixWord ++ tailWord_675674) baseStart_675674 baseEnd_675674 := by
    simpa [prefixWord, tailWord_675674, baseEnd_675674] using wordTrace_append hprefix tailTrace_675674
  have hstable : (prefixWord ++ tailWord_675674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675674).length < 2 ^ (prefixWord ++ tailWord_675674).sum := by decide
  have hdescent : baseEnd_675674 < baseStart_675674 := by decide
  rcases family_descends (prefixWord ++ tailWord_675674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675689 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 4, 5]
def baseStart_675689 : Nat := 118140960795 + 675689 * 2 ^ 59
def prefixEnd_675689 : Nat := 4983230072969 + 3 ^ 40 * 675689 * 2
def baseEnd_675689 : Nat := 231302153303941398253379

theorem tailTrace_675689 : CollatzResearch.WordTrace tailWord_675689 prefixEnd_675689 231302153303941398253379 := by
  unfold tailWord_675689
  simp only [CollatzResearch.WordTrace]
  refine ⟨24644402449101626338966121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16429601632734417559310747 24644402449101626338966121)
  ·
    refine ⟨18483301836826219754224591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24644402449101626338966121 18483301836826219754224591)
    ·
      refine ⟨27724952755239329631336887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18483301836826219754224591 27724952755239329631336887)
      ·
        refine ⟨41587429132858994447005331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27724952755239329631336887 41587429132858994447005331)
        ·
          refine ⟨62381143699288491670507997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41587429132858994447005331 62381143699288491670507997)
          ·
            refine ⟨23392928887233184376440499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62381143699288491670507997 23392928887233184376440499)
            ·
              refine ⟨35089393330849776564660749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23392928887233184376440499 35089393330849776564660749)
              ·
                refine ⟨13158522499068666211747781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35089393330849776564660749 13158522499068666211747781)
                ·
                  refine ⟨2467222968575374914702709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13158522499068666211747781 2467222968575374914702709)
                  ·
                    refine ⟨231302153303941398253379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2467222968575374914702709 231302153303941398253379)
                    ·
                      rfl

theorem cell22_675689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 5].length) (baseStart_675689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675689 prefixEnd_675689 := by exact prefixLift 675689
  have htrace : WordTrace (prefixWord ++ tailWord_675689) baseStart_675689 baseEnd_675689 := by
    simpa [prefixWord, tailWord_675689, baseEnd_675689] using wordTrace_append hprefix tailTrace_675689
  have hstable : (prefixWord ++ tailWord_675689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675689).length < 2 ^ (prefixWord ++ tailWord_675689).sum := by decide
  have hdescent : baseEnd_675689 < baseStart_675689 := by decide
  rcases family_descends (prefixWord ++ tailWord_675689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675721 : List Nat := [1, 2, 1, 1, 5, 1, 3, 1, 3, 4]
def baseStart_675721 : Nat := 118140960795 + 675721 * 2 ^ 59
def prefixEnd_675721 : Nat := 4983230072969 + 3 ^ 40 * 675721 * 2
def baseEnd_675721 : Nat := 231313107557903981453281

theorem tailTrace_675721 : CollatzResearch.WordTrace tailWord_675721 prefixEnd_675721 231313107557903981453281 := by
  unfold tailWord_675721
  simp only [CollatzResearch.WordTrace]
  refine ⟨24645569584985695804131017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16430379723323797202754011 24645569584985695804131017)
  ·
    refine ⟨18484177188739271853098263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24645569584985695804131017 18484177188739271853098263)
    ·
      refine ⟨27726265783108907779647395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18484177188739271853098263 27726265783108907779647395)
      ·
        refine ⟨41589398674663361669471093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27726265783108907779647395 41589398674663361669471093)
        ·
          refine ⟨3899006125749690156512915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41589398674663361669471093 3899006125749690156512915)
          ·
            refine ⟨5848509188624535234769373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3899006125749690156512915 5848509188624535234769373)
            ·
              refine ⟨2193190945734200713038515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5848509188624535234769373 2193190945734200713038515)
              ·
                refine ⟨3289786418601301069557773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2193190945734200713038515 3289786418601301069557773)
                ·
                  refine ⟨1233669906975487901084165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3289786418601301069557773 1233669906975487901084165)
                  ·
                    refine ⟨231313107557903981453281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1233669906975487901084165 231313107557903981453281)
                    ·
                      rfl

theorem cell22_675721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 4].length) (baseStart_675721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675721 prefixEnd_675721 := by exact prefixLift 675721
  have htrace : WordTrace (prefixWord ++ tailWord_675721) baseStart_675721 baseEnd_675721 := by
    simpa [prefixWord, tailWord_675721, baseEnd_675721] using wordTrace_append hprefix tailTrace_675721
  have hstable : (prefixWord ++ tailWord_675721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675721).length < 2 ^ (prefixWord ++ tailWord_675721).sum := by decide
  have hdescent : baseEnd_675721 < baseStart_675721 := by decide
  rcases family_descends (prefixWord ++ tailWord_675721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675742 : List Nat := [4, 3, 1, 3, 1, 1, 2, 2, 5]
def baseStart_675742 : Nat := 118140960795 + 675742 * 2 ^ 59
def prefixEnd_675742 : Nat := 4983230072969 + 3 ^ 40 * 675742 * 2
def baseEnd_675742 : Nat := 77106765429022308892739

theorem tailTrace_675742 : CollatzResearch.WordTrace tailWord_675742 prefixEnd_675742 77106765429022308892739 := by
  unfold tailWord_675742
  simp only [CollatzResearch.WordTrace]
  refine ⟨3080791939738702048830685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16430890345273077593763653 3080791939738702048830685)
  ·
    refine ⟨1155296977402013268311507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3080791939738702048830685 1155296977402013268311507)
    ·
      refine ⟨1732945466103019902467261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1155296977402013268311507 1732945466103019902467261)
      ·
        refine ⟨649854549788632463425223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1732945466103019902467261 649854549788632463425223)
        ·
          refine ⟨974781824682948695137835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 649854549788632463425223 974781824682948695137835)
          ·
            refine ⟨1462172737024423042706753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 974781824682948695137835 1462172737024423042706753)
            ·
              refine ⟨1096629552768317282030065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1462172737024423042706753 1096629552768317282030065)
              ·
                refine ⟨822472164576237961522549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1096629552768317282030065 822472164576237961522549)
                ·
                  refine ⟨77106765429022308892739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 822472164576237961522549 77106765429022308892739)
                  ·
                    rfl

theorem cell22_675742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_675742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675742 prefixEnd_675742 := by exact prefixLift 675742
  have htrace : WordTrace (prefixWord ++ tailWord_675742) baseStart_675742 baseEnd_675742 := by
    simpa [prefixWord, tailWord_675742, baseEnd_675742] using wordTrace_append hprefix tailTrace_675742
  have hstable : (prefixWord ++ tailWord_675742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675742).length < 2 ^ (prefixWord ++ tailWord_675742).sum := by decide
  have hdescent : baseEnd_675742 < baseStart_675742 := by decide
  rcases family_descends (prefixWord ++ tailWord_675742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675746 : List Nat := [3, 3, 1, 2, 4, 1, 2, 2, 1, 3]
def baseStart_675746 : Nat := 118140960795 + 675746 * 2 ^ 59
def prefixEnd_675746 : Nat := 4983230072969 + 3 ^ 40 * 675746 * 2
def baseEnd_675746 : Nat := 231321665568812249578205

theorem tailTrace_675746 : CollatzResearch.WordTrace tailWord_675746 prefixEnd_675746 231321665568812249578205 := by
  unfold tailWord_675746
  simp only [CollatzResearch.WordTrace]
  refine ⟨6161620352473781268447773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16430987606596750049194061 6161620352473781268447773)
  ·
    refine ⟨2310607632177667975667915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6161620352473781268447773 2310607632177667975667915)
    ·
      refine ⟨3465911448266501963501873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2310607632177667975667915 3465911448266501963501873)
      ·
        refine ⟨2599433586199876472626405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3465911448266501963501873 2599433586199876472626405)
        ·
          refine ⟨487393797412476838617451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2599433586199876472626405 487393797412476838617451)
          ·
            refine ⟨731090696118715257926177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487393797412476838617451 731090696118715257926177)
            ·
              refine ⟨548318022089036443444633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 731090696118715257926177 548318022089036443444633)
              ·
                refine ⟨411238516566777332583475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 548318022089036443444633 411238516566777332583475)
                ·
                  refine ⟨616857774850165998875213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 411238516566777332583475 616857774850165998875213)
                  ·
                    refine ⟨231321665568812249578205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 616857774850165998875213 231321665568812249578205)
                    ·
                      rfl

theorem cell22_675746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_675746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675746 prefixEnd_675746 := by exact prefixLift 675746
  have htrace : WordTrace (prefixWord ++ tailWord_675746) baseStart_675746 baseEnd_675746 := by
    simpa [prefixWord, tailWord_675746, baseEnd_675746] using wordTrace_append hprefix tailTrace_675746
  have hstable : (prefixWord ++ tailWord_675746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675746).length < 2 ^ (prefixWord ++ tailWord_675746).sum := by decide
  have hdescent : baseEnd_675746 < baseStart_675746 := by decide
  rcases family_descends (prefixWord ++ tailWord_675746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675768 : List Nat := [2, 1, 2, 1, 2, 3, 1, 5, 2, 3]
def baseStart_675768 : Nat := 118140960795 + 675768 * 2 ^ 59
def prefixEnd_675768 : Nat := 4983230072969 + 3 ^ 40 * 675768 * 2
def baseEnd_675768 : Nat := 231329196618411525528137

theorem tailTrace_675768 : CollatzResearch.WordTrace tailWord_675768 prefixEnd_675768 231329196618411525528137 := by
  unfold tailWord_675768
  simp only [CollatzResearch.WordTrace]
  refine ⟨12323641907907711415545979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16431522543876948554061305 12323641907907711415545979)
  ·
    refine ⟨18485462861861567123318969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12323641907907711415545979 18485462861861567123318969)
    ·
      refine ⟨13864097146396175342489227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18485462861861567123318969 13864097146396175342489227)
      ·
        refine ⟨20796145719594263013733841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13864097146396175342489227 20796145719594263013733841)
        ·
          refine ⟨15597109289695697260300381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20796145719594263013733841 15597109289695697260300381)
          ·
            refine ⟨5848915983635886472612643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15597109289695697260300381 5848915983635886472612643)
            ·
              refine ⟨8773373975453829708918965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5848915983635886472612643 8773373975453829708918965)
              ·
                refine ⟨822503810198796535211153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8773373975453829708918965 822503810198796535211153)
                ·
                  refine ⟨616877857649097401408365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 822503810198796535211153 616877857649097401408365)
                  ·
                    refine ⟨231329196618411525528137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 616877857649097401408365 231329196618411525528137)
                    ·
                      rfl

theorem cell22_675768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 2, 3].length) (baseStart_675768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675768 prefixEnd_675768 := by exact prefixLift 675768
  have htrace : WordTrace (prefixWord ++ tailWord_675768) baseStart_675768 baseEnd_675768 := by
    simpa [prefixWord, tailWord_675768, baseEnd_675768] using wordTrace_append hprefix tailTrace_675768
  have hstable : (prefixWord ++ tailWord_675768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675768).length < 2 ^ (prefixWord ++ tailWord_675768).sum := by decide
  have hdescent : baseEnd_675768 < baseStart_675768 := by decide
  rcases family_descends (prefixWord ++ tailWord_675768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675802 : List Nat := [3, 1, 1, 2, 5, 2, 1, 2, 2, 3]
def baseStart_675802 : Nat := 118140960795 + 675802 * 2 ^ 59
def prefixEnd_675802 : Nat := 4983230072969 + 3 ^ 40 * 675802 * 2
def baseEnd_675802 : Nat := 231340835513246770178033

theorem tailTrace_675802 : CollatzResearch.WordTrace tailWord_675802 prefixEnd_675802 231340835513246770178033 := by
  unfold tailWord_675802
  simp only [CollatzResearch.WordTrace]
  refine ⟨6162130974423061659457415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16432349265128164425219773 6162130974423061659457415)
  ·
    refine ⟨9243196461634592489186123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6162130974423061659457415 9243196461634592489186123)
    ·
      refine ⟨13864794692451888733779185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9243196461634592489186123 13864794692451888733779185)
      ·
        refine ⟨10398596019338916550334389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13864794692451888733779185 10398596019338916550334389)
        ·
          refine ⟨974868376813023426593849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10398596019338916550334389 974868376813023426593849)
          ·
            refine ⟨731151282609767569945387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 974868376813023426593849 731151282609767569945387)
            ·
              refine ⟨1096726923914651354918081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 731151282609767569945387 1096726923914651354918081)
              ·
                refine ⟨822545192935988516188561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1096726923914651354918081 822545192935988516188561)
                ·
                  refine ⟨616908894701991387141421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 822545192935988516188561 616908894701991387141421)
                  ·
                    refine ⟨231340835513246770178033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 616908894701991387141421 231340835513246770178033)
                    ·
                      rfl

theorem cell22_675802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 2, 3].length) (baseStart_675802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675802 prefixEnd_675802 := by exact prefixLift 675802
  have htrace : WordTrace (prefixWord ++ tailWord_675802) baseStart_675802 baseEnd_675802 := by
    simpa [prefixWord, tailWord_675802, baseEnd_675802] using wordTrace_append hprefix tailTrace_675802
  have hstable : (prefixWord ++ tailWord_675802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675802).length < 2 ^ (prefixWord ++ tailWord_675802).sum := by decide
  have hdescent : baseEnd_675802 < baseStart_675802 := by decide
  rcases family_descends (prefixWord ++ tailWord_675802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675847 : List Nat := [1, 1, 4, 3, 1, 2, 3, 3, 1, 3]
def baseStart_675847 : Nat := 118140960795 + 675847 * 2 ^ 59
def prefixEnd_675847 : Nat := 4983230072969 + 3 ^ 40 * 675847 * 2
def baseEnd_675847 : Nat := 231356239932881652802895

theorem tailTrace_675847 : CollatzResearch.WordTrace tailWord_675847 prefixEnd_675847 231356239932881652802895 := by
  unfold tailWord_675847
  simp only [CollatzResearch.WordTrace]
  refine ⟨24650165182529219323217795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16433443455019479548811863 24650165182529219323217795)
  ·
    refine ⟨36975247773793828984826693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24650165182529219323217795 36975247773793828984826693)
    ·
      refine ⟨6932858957586342934655005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36975247773793828984826693 6932858957586342934655005)
      ·
        refine ⟨2599822109094878600495627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6932858957586342934655005 2599822109094878600495627)
        ·
          refine ⟨3899733163642317900743441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2599822109094878600495627 3899733163642317900743441)
          ·
            refine ⟨2924799872731738425557581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3899733163642317900743441 2924799872731738425557581)
            ·
              refine ⟨1096799952274401909584093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2924799872731738425557581 1096799952274401909584093)
              ·
                refine ⟨411299982102900716094035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1096799952274401909584093 411299982102900716094035)
                ·
                  refine ⟨616949973154351074141053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 411299982102900716094035 616949973154351074141053)
                  ·
                    refine ⟨231356239932881652802895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 616949973154351074141053 231356239932881652802895)
                    ·
                      rfl

theorem cell22_675847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_675847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675847 prefixEnd_675847 := by exact prefixLift 675847
  have htrace : WordTrace (prefixWord ++ tailWord_675847) baseStart_675847 baseEnd_675847 := by
    simpa [prefixWord, tailWord_675847, baseEnd_675847] using wordTrace_append hprefix tailTrace_675847
  have hstable : (prefixWord ++ tailWord_675847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675847).length < 2 ^ (prefixWord ++ tailWord_675847).sum := by decide
  have hdescent : baseEnd_675847 < baseStart_675847 := by decide
  rcases family_descends (prefixWord ++ tailWord_675847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675890 : List Nat := [3, 2, 1, 1, 2, 3, 3, 2, 1, 4]
def baseStart_675890 : Nat := 118140960795 + 675890 * 2 ^ 59
def prefixEnd_675890 : Nat := 4983230072969 + 3 ^ 40 * 675890 * 2
def baseEnd_675890 : Nat := 231370959711643873977763

theorem tailTrace_675890 : CollatzResearch.WordTrace tailWord_675890 prefixEnd_675890 231370959711643873977763 := by
  unfold tailWord_675890
  simp only [CollatzResearch.WordTrace]
  refine ⟨6162933380343359416758281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16434489014248958444688749 6162933380343359416758281)
  ·
    refine ⟨4622200035257519562568711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6162933380343359416758281 4622200035257519562568711)
    ·
      refine ⟨6933300052886279343853067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4622200035257519562568711 6933300052886279343853067)
      ·
        refine ⟨10399950079329419015779601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6933300052886279343853067 10399950079329419015779601)
        ·
          refine ⟨7799962559497064261834701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10399950079329419015779601 7799962559497064261834701)
          ·
            refine ⟨2924985959811399098188013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7799962559497064261834701 2924985959811399098188013)
            ·
              refine ⟨1096869734929274661820505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2924985959811399098188013 1096869734929274661820505)
              ·
                refine ⟨822652301196955996365379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1096869734929274661820505 822652301196955996365379)
                ·
                  refine ⟨1233978451795433994548069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 822652301196955996365379 1233978451795433994548069)
                  ·
                    refine ⟨231370959711643873977763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1233978451795433994548069 231370959711643873977763)
                    ·
                      rfl

theorem cell22_675890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_675890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675890 prefixEnd_675890 := by exact prefixLift 675890
  have htrace : WordTrace (prefixWord ++ tailWord_675890) baseStart_675890 baseEnd_675890 := by
    simpa [prefixWord, tailWord_675890, baseEnd_675890] using wordTrace_append hprefix tailTrace_675890
  have hstable : (prefixWord ++ tailWord_675890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675890).length < 2 ^ (prefixWord ++ tailWord_675890).sum := by decide
  have hdescent : baseEnd_675890 < baseStart_675890 := by decide
  rcases family_descends (prefixWord ++ tailWord_675890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675903 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 6, 3]
def baseStart_675903 : Nat := 118140960795 + 675903 * 2 ^ 59
def prefixEnd_675903 : Nat := 4983230072969 + 3 ^ 40 * 675903 * 2
def baseEnd_675903 : Nat := 231375409877316173402723

theorem tailTrace_675903 : CollatzResearch.WordTrace tailWord_675903 prefixEnd_675903 231375409877316173402723 := by
  unfold tailWord_675903
  simp only [CollatzResearch.WordTrace]
  refine ⟨24652207670326340887256363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16434805113550893924837575 24652207670326340887256363)
  ·
    refine ⟨36978311505489511330884545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24652207670326340887256363 36978311505489511330884545)
    ·
      refine ⟨27733733629117133498163409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36978311505489511330884545 27733733629117133498163409)
      ·
        refine ⟨20800300221837850123622557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27733733629117133498163409 20800300221837850123622557)
        ·
          refine ⟨7800112583189193796358459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20800300221837850123622557 7800112583189193796358459)
          ·
            refine ⟨11700168874783790694537689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7800112583189193796358459 11700168874783790694537689)
            ·
              refine ⟨8775126656087843020903267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11700168874783790694537689 8775126656087843020903267)
              ·
                refine ⟨13162689984131764531354901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8775126656087843020903267 13162689984131764531354901)
                ·
                  refine ⟨617001093006176462407261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13162689984131764531354901 617001093006176462407261)
                  ·
                    refine ⟨231375409877316173402723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 617001093006176462407261 231375409877316173402723)
                    ·
                      rfl

theorem cell22_675903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 6, 3].length) (baseStart_675903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675903 prefixEnd_675903 := by exact prefixLift 675903
  have htrace : WordTrace (prefixWord ++ tailWord_675903) baseStart_675903 baseEnd_675903 := by
    simpa [prefixWord, tailWord_675903, baseEnd_675903] using wordTrace_append hprefix tailTrace_675903
  have hstable : (prefixWord ++ tailWord_675903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675903).length < 2 ^ (prefixWord ++ tailWord_675903).sum := by decide
  have hdescent : baseEnd_675903 < baseStart_675903 := by decide
  rcases family_descends (prefixWord ++ tailWord_675903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675922 : List Nat := [3, 2, 2, 1, 4, 1, 1, 4, 4]
def baseStart_675922 : Nat := 118140960795 + 675922 * 2 ^ 59
def prefixEnd_675922 : Nat := 4983230072969 + 3 ^ 40 * 675922 * 2
def baseEnd_675922 : Nat := 77127304655202152392555

theorem tailTrace_675922 : CollatzResearch.WordTrace tailWord_675922 prefixEnd_675922 77127304655202152392555 := by
  unfold tailWord_675922
  simp only [CollatzResearch.WordTrace]
  refine ⟨6163225164314376783049505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16435267104838338088132013 6163225164314376783049505)
  ·
    refine ⟨4622418873235782587287129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6163225164314376783049505 4622418873235782587287129)
    ·
      refine ⟨3466814154926836940465347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4622418873235782587287129 3466814154926836940465347)
      ·
        refine ⟨5200221232390255410698021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3466814154926836940465347 5200221232390255410698021)
        ·
          refine ⟨975041481073172889505879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5200221232390255410698021 975041481073172889505879)
          ·
            refine ⟨1462562221609759334258819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 975041481073172889505879 1462562221609759334258819)
            ·
              refine ⟨2193843332414639001388229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1462562221609759334258819 2193843332414639001388229)
              ·
                refine ⟨411345624827744812760293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2193843332414639001388229 411345624827744812760293)
                ·
                  refine ⟨77127304655202152392555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 411345624827744812760293 77127304655202152392555)
                  ·
                    rfl

theorem cell22_675922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_675922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675922 prefixEnd_675922 := by exact prefixLift 675922
  have htrace : WordTrace (prefixWord ++ tailWord_675922) baseStart_675922 baseEnd_675922 := by
    simpa [prefixWord, tailWord_675922, baseEnd_675922] using wordTrace_append hprefix tailTrace_675922
  have hstable : (prefixWord ++ tailWord_675922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675922).length < 2 ^ (prefixWord ++ tailWord_675922).sum := by decide
  have hdescent : baseEnd_675922 < baseStart_675922 := by decide
  rcases family_descends (prefixWord ++ tailWord_675922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675950 : List Nat := [4, 1, 2, 2, 1, 1, 5, 6]
def baseStart_675950 : Nat := 118140960795 + 675950 * 2 ^ 59
def prefixEnd_675950 : Nat := 4983230072969 + 3 ^ 40 * 675950 * 2
def baseEnd_675950 : Nat := 25710166548647079719731

theorem tailTrace_675950 : CollatzResearch.WordTrace tailWord_675950 prefixEnd_675950 25710166548647079719731 := by
  unfold tailWord_675950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3081740237644508489277163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16435947934104045276144869 3081740237644508489277163)
  ·
    refine ⟨4622610356466762733915745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3081740237644508489277163 4622610356466762733915745)
    ·
      refine ⟨3466957767350072050436809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4622610356466762733915745 3466957767350072050436809)
      ·
        refine ⟨2600218325512554037827607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3466957767350072050436809 2600218325512554037827607)
        ·
          refine ⟨3900327488268831056741411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2600218325512554037827607 3900327488268831056741411)
          ·
            refine ⟨5850491232403246585112117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3900327488268831056741411 5850491232403246585112117)
            ·
              refine ⟨548483553037804367354261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5850491232403246585112117 548483553037804367354261)
              ·
                refine ⟨25710166548647079719731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 548483553037804367354261 25710166548647079719731)
                ·
                  rfl

theorem cell22_675950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 6].length) (baseStart_675950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_675950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_675950 prefixEnd_675950 := by exact prefixLift 675950
  have htrace : WordTrace (prefixWord ++ tailWord_675950) baseStart_675950 baseEnd_675950 := by
    simpa [prefixWord, tailWord_675950, baseEnd_675950] using wordTrace_append hprefix tailTrace_675950
  have hstable : (prefixWord ++ tailWord_675950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675950).length < 2 ^ (prefixWord ++ tailWord_675950).sum := by decide
  have hdescent : baseEnd_675950 < baseStart_675950 := by decide
  rcases family_descends (prefixWord ++ tailWord_675950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676025 : List Nat := [1, 2, 1, 4, 1, 2, 1, 5, 1, 4]
def baseStart_676025 : Nat := 118140960795 + 676025 * 2 ^ 59
def prefixEnd_676025 : Nat := 4983230072969 + 3 ^ 40 * 676025 * 2
def baseEnd_676025 : Nat := 231417172970548521852349

theorem tailTrace_676025 : CollatzResearch.WordTrace tailWord_676025 prefixEnd_676025 231417172970548521852349 := by
  unfold tailWord_676025
  simp only [CollatzResearch.WordTrace]
  refine ⟨24656657375884355723197529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16437771583922903815465019 24656657375884355723197529)
  ·
    refine ⟨18492493031913266792398147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24656657375884355723197529 18492493031913266792398147)
    ·
      refine ⟨27738739547869900188597221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18492493031913266792398147 27738739547869900188597221)
      ·
        refine ⟨5201013665225606285361979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27738739547869900188597221 5201013665225606285361979)
        ·
          refine ⟨7801520497838409428042969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5201013665225606285361979 7801520497838409428042969)
          ·
            refine ⟨5851140373378807071032227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7801520497838409428042969 5851140373378807071032227)
            ·
              refine ⟨8776710560068210606548341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5851140373378807071032227 8776710560068210606548341)
              ·
                refine ⟨822816615006394744363907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8776710560068210606548341 822816615006394744363907)
                ·
                  refine ⟨1234224922509592116545861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 822816615006394744363907 1234224922509592116545861)
                  ·
                    refine ⟨231417172970548521852349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1234224922509592116545861 231417172970548521852349)
                    ·
                      rfl

theorem cell22_676025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 4].length) (baseStart_676025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_676025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_676025 prefixEnd_676025 := by exact prefixLift 676025
  have htrace : WordTrace (prefixWord ++ tailWord_676025) baseStart_676025 baseEnd_676025 := by
    simpa [prefixWord, tailWord_676025, baseEnd_676025] using wordTrace_append hprefix tailTrace_676025
  have hstable : (prefixWord ++ tailWord_676025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676025).length < 2 ^ (prefixWord ++ tailWord_676025).sum := by decide
  have hdescent : baseEnd_676025 < baseStart_676025 := by decide
  rcases family_descends (prefixWord ++ tailWord_676025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676033 : List Nat := [1, 2, 6, 1, 2, 1, 3, 2, 1, 3]
def baseStart_676033 : Nat := 118140960795 + 676033 * 2 ^ 59
def prefixEnd_676033 : Nat := 4983230072969 + 3 ^ 40 * 676033 * 2
def baseEnd_676033 : Nat := 231419911534039167652325

theorem tailTrace_676033 : CollatzResearch.WordTrace tailWord_676033 prefixEnd_676033 231419911534039167652325 := by
  unfold tailWord_676033
  simp only [CollatzResearch.WordTrace]
  refine ⟨24656949159855373089488753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16437966106570248726325835 24656949159855373089488753)
  ·
    refine ⟨18492711869891529817116565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24656949159855373089488753 18492711869891529817116565)
    ·
      refine ⟨866845868901165460177339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18492711869891529817116565 866845868901165460177339)
      ·
        refine ⟨1300268803351748190266009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 866845868901165460177339 1300268803351748190266009)
        ·
          refine ⟨975201602513811142699507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1300268803351748190266009 975201602513811142699507)
          ·
            refine ⟨1462802403770716714049261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 975201602513811142699507 1462802403770716714049261)
            ·
              refine ⟨548550901414018767768473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1462802403770716714049261 548550901414018767768473)
              ·
                refine ⟨411413176060514075826355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 548550901414018767768473 411413176060514075826355)
                ·
                  refine ⟨617119764090771113739533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 411413176060514075826355 617119764090771113739533)
                  ·
                    refine ⟨231419911534039167652325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 617119764090771113739533 231419911534039167652325)
                    ·
                      rfl

theorem cell22_676033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_676033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_676033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_676033 prefixEnd_676033 := by exact prefixLift 676033
  have htrace : WordTrace (prefixWord ++ tailWord_676033) baseStart_676033 baseEnd_676033 := by
    simpa [prefixWord, tailWord_676033, baseEnd_676033] using wordTrace_append hprefix tailTrace_676033
  have hstable : (prefixWord ++ tailWord_676033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676033).length < 2 ^ (prefixWord ++ tailWord_676033).sum := by decide
  have hdescent : baseEnd_676033 < baseStart_676033 := by decide
  rcases family_descends (prefixWord ++ tailWord_676033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676160 : List Nat := [2, 1, 1, 2, 2, 1, 2, 4, 3, 4]
def baseStart_676160 : Nat := 118140960795 + 676160 * 2 ^ 59
def prefixEnd_676160 : Nat := 4983230072969 + 3 ^ 40 * 676160 * 2
def baseEnd_676160 : Nat := 231463386229453169726935

theorem tailTrace_676160 : CollatzResearch.WordTrace tailWord_676160 prefixEnd_676160 231463386229453169726935 := by
  unfold tailWord_676160
  simp only [CollatzResearch.WordTrace]
  refine ⟨12330790615197636889680967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16441054153596849186241289 12330790615197636889680967)
  ·
    refine ⟨18496185922796455334521451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12330790615197636889680967 18496185922796455334521451)
    ·
      refine ⟨27744278884194683001782177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18496185922796455334521451 27744278884194683001782177)
      ·
        refine ⟨20808209163146012251336633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27744278884194683001782177 20808209163146012251336633)
        ·
          refine ⟨15606156872359509188502475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20808209163146012251336633 15606156872359509188502475)
          ·
            refine ⟨23409235308539263782753713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15606156872359509188502475 23409235308539263782753713)
            ·
              refine ⟨17556926481404447837065285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23409235308539263782753713 17556926481404447837065285)
              ·
                refine ⟨3291923715263333969449741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17556926481404447837065285 3291923715263333969449741)
                ·
                  refine ⟨1234471393223750238543653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3291923715263333969449741 1234471393223750238543653)
                  ·
                    refine ⟨231463386229453169726935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1234471393223750238543653 231463386229453169726935)
                    ·
                      rfl

theorem cell22_676160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 3, 4].length) (baseStart_676160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_676160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_676160 prefixEnd_676160 := by exact prefixLift 676160
  have htrace : WordTrace (prefixWord ++ tailWord_676160) baseStart_676160 baseEnd_676160 := by
    simpa [prefixWord, tailWord_676160, baseEnd_676160] using wordTrace_append hprefix tailTrace_676160
  have hstable : (prefixWord ++ tailWord_676160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676160).length < 2 ^ (prefixWord ++ tailWord_676160).sum := by decide
  have hdescent : baseEnd_676160 < baseStart_676160 := by decide
  rcases family_descends (prefixWord ++ tailWord_676160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676177 : List Nat := [1, 2, 2, 1, 4, 2, 1, 4, 1, 4]
def baseStart_676177 : Nat := 118140960795 + 676177 * 2 ^ 59
def prefixEnd_676177 : Nat := 4983230072969 + 3 ^ 40 * 676177 * 2
def baseEnd_676177 : Nat := 231469205676870792051883

theorem tailTrace_676177 : CollatzResearch.WordTrace tailWord_676177 prefixEnd_676177 231469205676870792051883 := by
  unfold tailWord_676177
  simp only [CollatzResearch.WordTrace]
  refine ⟨24662201271333685682730785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16441467514222457121820523 24662201271333685682730785)
  ·
    refine ⟨18496650953500264262048089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24662201271333685682730785 18496650953500264262048089)
    ·
      refine ⟨13872488215125198196536067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18496650953500264262048089 13872488215125198196536067)
      ·
        refine ⟨20808732322687797294804101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13872488215125198196536067 20808732322687797294804101)
        ·
          refine ⟨3901637310503961992775769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20808732322687797294804101 3901637310503961992775769)
          ·
            refine ⟨2926227982877971494581827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3901637310503961992775769 2926227982877971494581827)
            ·
              refine ⟨4389341974316957241872741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2926227982877971494581827 4389341974316957241872741)
              ·
                refine ⟨823001620184429482851139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4389341974316957241872741 823001620184429482851139)
                ·
                  refine ⟨1234502430276644224276709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 823001620184429482851139 1234502430276644224276709)
                  ·
                    refine ⟨231469205676870792051883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1234502430276644224276709 231469205676870792051883)
                    ·
                      rfl

theorem cell22_676177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_676177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_676177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_676177 prefixEnd_676177 := by exact prefixLift 676177
  have htrace : WordTrace (prefixWord ++ tailWord_676177) baseStart_676177 baseEnd_676177 := by
    simpa [prefixWord, tailWord_676177, baseEnd_676177] using wordTrace_append hprefix tailTrace_676177
  have hstable : (prefixWord ++ tailWord_676177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676177).length < 2 ^ (prefixWord ++ tailWord_676177).sum := by decide
  have hdescent : baseEnd_676177 < baseStart_676177 := by decide
  rcases family_descends (prefixWord ++ tailWord_676177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676194 : List Nat := [3, 3, 2, 1, 1, 2, 2, 3, 1, 4]
def baseStart_676194 : Nat := 118140960795 + 676194 * 2 ^ 59
def prefixEnd_676194 : Nat := 4983230072969 + 3 ^ 40 * 676194 * 2
def baseEnd_676194 : Nat := 231475025124288414376831

theorem tailTrace_676194 : CollatzResearch.WordTrace tailWord_676194 prefixEnd_676194 231475025124288414376831 := by
  unfold tailWord_676194
  simp only [CollatzResearch.WordTrace]
  refine ⟨6165705328068024396524909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16441880874848065057399757 6165705328068024396524909)
  ·
    refine ⟨2312139498025509148696841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6165705328068024396524909 2312139498025509148696841)
    ·
      refine ⟨1734104623519131861522631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2312139498025509148696841 1734104623519131861522631)
      ·
        refine ⟨2601156935278697792283947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1734104623519131861522631 2601156935278697792283947)
        ·
          refine ⟨3901735402918046688425921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2601156935278697792283947 3901735402918046688425921)
          ·
            refine ⟨2926301552188535016319441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3901735402918046688425921 2926301552188535016319441)
            ·
              refine ⟨2194726164141401262239581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2926301552188535016319441 2194726164141401262239581)
              ·
                refine ⟨823022311553025473339843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2194726164141401262239581 823022311553025473339843)
                ·
                  refine ⟨1234533467329538210009765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 823022311553025473339843 1234533467329538210009765)
                  ·
                    refine ⟨231475025124288414376831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1234533467329538210009765 231475025124288414376831)
                    ·
                      rfl

theorem cell22_676194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_676194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_676194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_676194 prefixEnd_676194 := by exact prefixLift 676194
  have htrace : WordTrace (prefixWord ++ tailWord_676194) baseStart_676194 baseEnd_676194 := by
    simpa [prefixWord, tailWord_676194, baseEnd_676194] using wordTrace_append hprefix tailTrace_676194
  have hstable : (prefixWord ++ tailWord_676194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676194).length < 2 ^ (prefixWord ++ tailWord_676194).sum := by decide
  have hdescent : baseEnd_676194 < baseStart_676194 := by decide
  rcases family_descends (prefixWord ++ tailWord_676194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676265 : List Nat := [1, 2, 1, 1, 1, 1, 3, 5, 7]
def baseStart_676265 : Nat := 118140960795 + 676265 * 2 ^ 59
def prefixEnd_676265 : Nat := 4983230072969 + 3 ^ 40 * 676265 * 2
def baseEnd_676265 : Nat := 77166443291755965283871

theorem tailTrace_676265 : CollatzResearch.WordTrace tailWord_676265 prefixEnd_676265 77166443291755965283871 := by
  unfold tailWord_676265
  simp only [CollatzResearch.WordTrace]
  refine ⟨24665410895014876711934249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16443607263343251141289499 24665410895014876711934249)
  ·
    refine ⟨18499058171261157533950687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24665410895014876711934249 18499058171261157533950687)
    ·
      refine ⟨27748587256891736300926031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18499058171261157533950687 27748587256891736300926031)
      ·
        refine ⟨41622880885337604451389047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27748587256891736300926031 41622880885337604451389047)
        ·
          refine ⟨62434321328006406677083571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41622880885337604451389047 62434321328006406677083571)
          ·
            refine ⟨93651481992009610015625357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62434321328006406677083571 93651481992009610015625357)
            ·
              refine ⟨35119305747003603755859509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93651481992009610015625357 35119305747003603755859509)
              ·
                refine ⟨3292434913781587852111829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35119305747003603755859509 3292434913781587852111829)
                ·
                  refine ⟨77166443291755965283871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3292434913781587852111829 77166443291755965283871)
                  ·
                    rfl

theorem cell22_676265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 7].length) (baseStart_676265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_676265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_676265 prefixEnd_676265 := by exact prefixLift 676265
  have htrace : WordTrace (prefixWord ++ tailWord_676265) baseStart_676265 baseEnd_676265 := by
    simpa [prefixWord, tailWord_676265, baseEnd_676265] using wordTrace_append hprefix tailTrace_676265
  have hstable : (prefixWord ++ tailWord_676265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676265).length < 2 ^ (prefixWord ++ tailWord_676265).sum := by decide
  have hdescent : baseEnd_676265 < baseStart_676265 := by decide
  rcases family_descends (prefixWord ++ tailWord_676265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676357 : List Nat := [1, 3, 1, 1, 2, 2, 4, 1, 1, 6]
def baseStart_676357 : Nat := 118140960795 + 676357 * 2 ^ 59
def prefixEnd_676357 : Nat := 4983230072969 + 3 ^ 40 * 676357 * 2
def baseEnd_676357 : Nat := 231530823355410322551331

theorem tailTrace_676357 : CollatzResearch.WordTrace tailWord_676357 prefixEnd_676357 231530823355410322551331 := by
  unfold tailWord_676357
  simp only [CollatzResearch.WordTrace]
  refine ⟨24668766410681576424283325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16445844273787717616188883 24668766410681576424283325)
  ·
    refine ⟨9250787404005591159106247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24668766410681576424283325 9250787404005591159106247)
    ·
      refine ⟨13876181106008386738659371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9250787404005591159106247 13876181106008386738659371)
      ·
        refine ⟨20814271659012580107989057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13876181106008386738659371 20814271659012580107989057)
        ·
          refine ⟨15610703744259435080991793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20814271659012580107989057 15610703744259435080991793)
          ·
            refine ⟨11708027808194576310743845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15610703744259435080991793 11708027808194576310743845)
            ·
              refine ⟨2195255214036483058264471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11708027808194576310743845 2195255214036483058264471)
              ·
                refine ⟨3292882821054724587396707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2195255214036483058264471 3292882821054724587396707)
                ·
                  refine ⟨4939324231582086881095061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3292882821054724587396707 4939324231582086881095061)
                  ·
                    refine ⟨231530823355410322551331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4939324231582086881095061 231530823355410322551331)
                    ·
                      rfl

theorem cell22_676357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_676357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_676357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_676357 prefixEnd_676357 := by exact prefixLift 676357
  have htrace : WordTrace (prefixWord ++ tailWord_676357) baseStart_676357 baseEnd_676357 := by
    simpa [prefixWord, tailWord_676357, baseEnd_676357] using wordTrace_append hprefix tailTrace_676357
  have hstable : (prefixWord ++ tailWord_676357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676357).length < 2 ^ (prefixWord ++ tailWord_676357).sum := by decide
  have hdescent : baseEnd_676357 < baseStart_676357 := by decide
  rcases family_descends (prefixWord ++ tailWord_676357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676397 : List Nat := [1, 5, 4, 1, 1, 2, 1, 2, 1, 4]
def baseStart_676397 : Nat := 118140960795 + 676397 * 2 ^ 59
def prefixEnd_676397 : Nat := 4983230072969 + 3 ^ 40 * 676397 * 2
def baseEnd_676397 : Nat := 231544516172863551551209

theorem tailTrace_676397 : CollatzResearch.WordTrace tailWord_676397 prefixEnd_676397 231544516172863551551209 := by
  unfold tailWord_676397
  simp only [CollatzResearch.WordTrace]
  refine ⟨24670225330536663255739445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16446816887024442170492963 24670225330536663255739445)
  ·
    refine ⟨2312833624737812180225573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24670225330536663255739445 2312833624737812180225573)
    ·
      refine ⟨433656304638339783792295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2312833624737812180225573 433656304638339783792295)
      ·
        refine ⟨650484456957509675688443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433656304638339783792295 650484456957509675688443)
        ·
          refine ⟨975726685436264513532665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 650484456957509675688443 975726685436264513532665)
          ·
            refine ⟨731795014077198385149499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 975726685436264513532665 731795014077198385149499)
            ·
              refine ⟨1097692521115797577724249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 731795014077198385149499 1097692521115797577724249)
              ·
                refine ⟨823269390836848183293187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1097692521115797577724249 823269390836848183293187)
                ·
                  refine ⟨1234904086255272274939781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 823269390836848183293187 1234904086255272274939781)
                  ·
                    refine ⟨231544516172863551551209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1234904086255272274939781 231544516172863551551209)
                    ·
                      rfl

theorem cell22_676397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_676397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_676397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_676397 prefixEnd_676397 := by exact prefixLift 676397
  have htrace : WordTrace (prefixWord ++ tailWord_676397) baseStart_676397 baseEnd_676397 := by
    simpa [prefixWord, tailWord_676397, baseEnd_676397] using wordTrace_append hprefix tailTrace_676397
  have hstable : (prefixWord ++ tailWord_676397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676397).length < 2 ^ (prefixWord ++ tailWord_676397).sum := by decide
  have hdescent : baseEnd_676397 < baseStart_676397 := by decide
  rcases family_descends (prefixWord ++ tailWord_676397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676449 : List Nat := [1, 2, 3, 1, 1, 5, 1, 1, 2, 5]
def baseStart_676449 : Nat := 118140960795 + 676449 * 2 ^ 59
def prefixEnd_676449 : Nat := 4983230072969 + 3 ^ 40 * 676449 * 2
def baseEnd_676449 : Nat := 231562316835552749251049

theorem tailTrace_676449 : CollatzResearch.WordTrace tailWord_676449 prefixEnd_676449 231562316835552749251049 := by
  unfold tailWord_676449
  simp only [CollatzResearch.WordTrace]
  refine ⟨24672121926348276136632401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16448081284232184091088267 24672121926348276136632401)
  ·
    refine ⟨18504091444761207102474301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24672121926348276136632401 18504091444761207102474301)
    ·
      refine ⟨6939034291785452663427863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18504091444761207102474301 6939034291785452663427863)
      ·
        refine ⟨10408551437678178995141795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6939034291785452663427863 10408551437678178995141795)
        ·
          refine ⟨15612827156517268492712693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10408551437678178995141795 15612827156517268492712693)
          ·
            refine ⟨1463702545923493921191815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15612827156517268492712693 1463702545923493921191815)
            ·
              refine ⟨2195553818885240881787723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1463702545923493921191815 2195553818885240881787723)
              ·
                refine ⟨3293330728327861322681585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2195553818885240881787723 3293330728327861322681585)
                ·
                  refine ⟨2469998046245895992011189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3293330728327861322681585 2469998046245895992011189)
                  ·
                    refine ⟨231562316835552749251049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2469998046245895992011189 231562316835552749251049)
                    ·
                      rfl

theorem cell22_676449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_676449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_676449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_676449 prefixEnd_676449 := by exact prefixLift 676449
  have htrace : WordTrace (prefixWord ++ tailWord_676449) baseStart_676449 baseEnd_676449 := by
    simpa [prefixWord, tailWord_676449, baseEnd_676449] using wordTrace_append hprefix tailTrace_676449
  have hstable : (prefixWord ++ tailWord_676449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676449).length < 2 ^ (prefixWord ++ tailWord_676449).sum := by decide
  have hdescent : baseEnd_676449 < baseStart_676449 := by decide
  rcases family_descends (prefixWord ++ tailWord_676449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676481 : List Nat := [1, 2, 4, 2, 1, 1, 3, 3, 1, 4]
def baseStart_676481 : Nat := 118140960795 + 676481 * 2 ^ 59
def prefixEnd_676481 : Nat := 4983230072969 + 3 ^ 40 * 676481 * 2
def baseEnd_676481 : Nat := 231573271089515332450951

theorem tailTrace_676481 : CollatzResearch.WordTrace tailWord_676481 prefixEnd_676481 231573271089515332450951 := by
  unfold tailWord_676481
  simp only [CollatzResearch.WordTrace]
  refine ⟨24673289062232345601797297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16448859374821563734531531 24673289062232345601797297)
  ·
    refine ⟨18504966796674259201347973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24673289062232345601797297 18504966796674259201347973)
    ·
      refine ⟨3469681274376423600252745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18504966796674259201347973 3469681274376423600252745)
      ·
        refine ⟨2602260955782317700189559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3469681274376423600252745 2602260955782317700189559)
        ·
          refine ⟨3903391433673476550284339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2602260955782317700189559 3903391433673476550284339)
          ·
            refine ⟨5855087150510214825426509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3903391433673476550284339 5855087150510214825426509)
            ·
              refine ⟨2195657681441330559534941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5855087150510214825426509 2195657681441330559534941)
              ·
                refine ⟨823371630540498959825603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2195657681441330559534941 823371630540498959825603)
                ·
                  refine ⟨1235057445810748439738405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 823371630540498959825603 1235057445810748439738405)
                  ·
                    refine ⟨231573271089515332450951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1235057445810748439738405 231573271089515332450951)
                    ·
                      rfl

theorem cell22_676481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_676481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_676481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_676481 prefixEnd_676481 := by exact prefixLift 676481
  have htrace : WordTrace (prefixWord ++ tailWord_676481) baseStart_676481 baseEnd_676481 := by
    simpa [prefixWord, tailWord_676481, baseEnd_676481] using wordTrace_append hprefix tailTrace_676481
  have hstable : (prefixWord ++ tailWord_676481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676481).length < 2 ^ (prefixWord ++ tailWord_676481).sum := by decide
  have hdescent : baseEnd_676481 < baseStart_676481 := by decide
  rcases family_descends (prefixWord ++ tailWord_676481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676509 : List Nat := [1, 4, 2, 1, 1, 1, 3, 2, 1, 6]
def baseStart_676509 : Nat := 118140960795 + 676509 * 2 ^ 59
def prefixEnd_676509 : Nat := 4983230072969 + 3 ^ 40 * 676509 * 2
def baseEnd_676509 : Nat := 231582856061732592750865

theorem tailTrace_676509 : CollatzResearch.WordTrace tailWord_676509 prefixEnd_676509 231582856061732592750865 := by
  unfold tailWord_676509
  simp only [CollatzResearch.WordTrace]
  refine ⟨24674310306130906383816581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16449540204087270922544387 24674310306130906383816581)
  ·
    refine ⟨4626433182399544946965609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24674310306130906383816581 4626433182399544946965609)
    ·
      refine ⟨3469824886799658710224207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4626433182399544946965609 3469824886799658710224207)
      ·
        refine ⟨5204737330199488065336311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3469824886799658710224207 5204737330199488065336311)
        ·
          refine ⟨7807105995299232098004467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5204737330199488065336311 7807105995299232098004467)
          ·
            refine ⟨11710658992948848147006701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7807105995299232098004467 11710658992948848147006701)
            ·
              refine ⟨4391497122355818055127513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11710658992948848147006701 4391497122355818055127513)
              ·
                refine ⟨3293622841766863541345635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4391497122355818055127513 3293622841766863541345635)
                ·
                  refine ⟨4940434262650295312018453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3293622841766863541345635 4940434262650295312018453)
                  ·
                    refine ⟨231582856061732592750865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4940434262650295312018453 231582856061732592750865)
                    ·
                      rfl

theorem cell22_676509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_676509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_676509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_676509 prefixEnd_676509 := by exact prefixLift 676509
  have htrace : WordTrace (prefixWord ++ tailWord_676509) baseStart_676509 baseEnd_676509 := by
    simpa [prefixWord, tailWord_676509, baseEnd_676509] using wordTrace_append hprefix tailTrace_676509
  have hstable : (prefixWord ++ tailWord_676509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676509).length < 2 ^ (prefixWord ++ tailWord_676509).sum := by decide
  have hdescent : baseEnd_676509 < baseStart_676509 := by decide
  rcases family_descends (prefixWord ++ tailWord_676509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676562 : List Nat := [3, 2, 2, 2, 3, 2, 2, 1, 2, 3]
def baseStart_676562 : Nat := 118140960795 + 676562 * 2 ^ 59
def prefixEnd_676562 : Nat := 4983230072969 + 3 ^ 40 * 676562 * 2
def baseEnd_676562 : Nat := 231600999044858121175703

theorem tailTrace_676562 : CollatzResearch.WordTrace tailWord_676562 prefixEnd_676562 231600999044858121175703 := by
  unfold tailWord_676562
  simp only [CollatzResearch.WordTrace]
  refine ⟨6169060843734724108873985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16450828916625930956997293 6169060843734724108873985)
  ·
    refine ⟨4626795632801043081655489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6169060843734724108873985 4626795632801043081655489)
    ·
      refine ⟨3470096724600782311241617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4626795632801043081655489 3470096724600782311241617)
      ·
        refine ⟨2602572543450586733431213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3470096724600782311241617 2602572543450586733431213)
        ·
          refine ⟨975964703793970025036705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2602572543450586733431213 975964703793970025036705)
          ·
            refine ⟨731973527845477518777529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 975964703793970025036705 731973527845477518777529)
            ·
              refine ⟨548980145884108139083147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 731973527845477518777529 548980145884108139083147)
              ·
                refine ⟨823470218826162208624721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 548980145884108139083147 823470218826162208624721)
                ·
                  refine ⟨617602664119621656468541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 823470218826162208624721 617602664119621656468541)
                  ·
                    refine ⟨231600999044858121175703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 617602664119621656468541 231600999044858121175703)
                    ·
                      rfl

theorem cell22_676562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_676562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_676562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_676562 prefixEnd_676562 := by exact prefixLift 676562
  have htrace : WordTrace (prefixWord ++ tailWord_676562) baseStart_676562 baseEnd_676562 := by
    simpa [prefixWord, tailWord_676562, baseEnd_676562] using wordTrace_append hprefix tailTrace_676562
  have hstable : (prefixWord ++ tailWord_676562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676562).length < 2 ^ (prefixWord ++ tailWord_676562).sum := by decide
  have hdescent : baseEnd_676562 < baseStart_676562 := by decide
  rcases family_descends (prefixWord ++ tailWord_676562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676616 : List Nat := [2, 1, 3, 2, 2, 2, 1, 2, 3, 4]
def baseStart_676616 : Nat := 118140960795 + 676616 * 2 ^ 59
def prefixEnd_676616 : Nat := 4983230072969 + 3 ^ 40 * 676616 * 2
def baseEnd_676616 : Nat := 231619484348419980325537

theorem tailTrace_676616 : CollatzResearch.WordTrace tailWord_676616 prefixEnd_676616 231619484348419980325537 := by
  unfold tailWord_676616
  simp only [CollatzResearch.WordTrace]
  refine ⟨12339106458371631828980851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16452141944495509105307801 12339106458371631828980851)
  ·
    refine ⟨18508659687557447743471277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12339106458371631828980851 18508659687557447743471277)
    ·
      refine ⟨6940747382834042903801729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18508659687557447743471277 6940747382834042903801729)
      ·
        refine ⟨5205560537125532177851297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6940747382834042903801729 5205560537125532177851297)
        ·
          refine ⟨3904170402844149133388473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5205560537125532177851297 3904170402844149133388473)
          ·
            refine ⟨2928127802133111850041355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3904170402844149133388473 2928127802133111850041355)
            ·
              refine ⟨4392191703199667775062033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2928127802133111850041355 4392191703199667775062033)
              ·
                refine ⟨3294143777399750831296525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4392191703199667775062033 3294143777399750831296525)
                ·
                  refine ⟨1235303916524906561736197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3294143777399750831296525 1235303916524906561736197)
                  ·
                    refine ⟨231619484348419980325537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1235303916524906561736197 231619484348419980325537)
                    ·
                      rfl

theorem cell22_676616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_676616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_676616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_676616 prefixEnd_676616 := by exact prefixLift 676616
  have htrace : WordTrace (prefixWord ++ tailWord_676616) baseStart_676616 baseEnd_676616 := by
    simpa [prefixWord, tailWord_676616, baseEnd_676616] using wordTrace_append hprefix tailTrace_676616
  have hstable : (prefixWord ++ tailWord_676616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676616).length < 2 ^ (prefixWord ++ tailWord_676616).sum := by decide
  have hdescent : baseEnd_676616 < baseStart_676616 := by decide
  rcases family_descends (prefixWord ++ tailWord_676616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676680 : List Nat := [2, 1, 3, 1, 1, 3, 5, 1, 2, 3]
def baseStart_676680 : Nat := 118140960795 + 676680 * 2 ^ 59
def prefixEnd_676680 : Nat := 4983230072969 + 3 ^ 40 * 676680 * 2
def baseEnd_676680 : Nat := 231641392856345146725341

theorem tailTrace_676680 : CollatzResearch.WordTrace tailWord_676680 prefixEnd_676680 231641392856345146725341 := by
  unfold tailWord_676680
  simp only [CollatzResearch.WordTrace]
  refine ⟨12340273594255701294145747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16453698125674268392194329 12340273594255701294145747)
  ·
    refine ⟨18510410391383551941218621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12340273594255701294145747 18510410391383551941218621)
    ·
      refine ⟨6941403896768831977956983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18510410391383551941218621 6941403896768831977956983)
      ·
        refine ⟨10412105845153247966935475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6941403896768831977956983 10412105845153247966935475)
        ·
          refine ⟨15618158767729871950403213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10412105845153247966935475 15618158767729871950403213)
          ·
            refine ⟨5856809537898701981401205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15618158767729871950403213 5856809537898701981401205)
            ·
              refine ⟨549075894178003310756363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5856809537898701981401205 549075894178003310756363)
              ·
                refine ⟨823613841267004966134545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 549075894178003310756363 823613841267004966134545)
                ·
                  refine ⟨617710380950253724600909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 823613841267004966134545 617710380950253724600909)
                  ·
                    refine ⟨231641392856345146725341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 617710380950253724600909 231641392856345146725341)
                    ·
                      rfl

theorem cell22_676680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_676680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_676680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_676680 prefixEnd_676680 := by exact prefixLift 676680
  have htrace : WordTrace (prefixWord ++ tailWord_676680) baseStart_676680 baseEnd_676680 := by
    simpa [prefixWord, tailWord_676680, baseEnd_676680] using wordTrace_append hprefix tailTrace_676680
  have hstable : (prefixWord ++ tailWord_676680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676680).length < 2 ^ (prefixWord ++ tailWord_676680).sum := by decide
  have hdescent : baseEnd_676680 < baseStart_676680 := by decide
  rcases family_descends (prefixWord ++ tailWord_676680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676721 : List Nat := [1, 2, 2, 2, 1, 4, 2, 1, 7]
def baseStart_676721 : Nat := 118140960795 + 676721 * 2 ^ 59
def prefixEnd_676721 : Nat := 4983230072969 + 3 ^ 40 * 676721 * 2
def baseEnd_676721 : Nat := 77218475998078235483405

theorem tailTrace_676721 : CollatzResearch.WordTrace tailWord_676721 prefixEnd_676721 77218475998078235483405 := by
  unfold tailWord_676721
  simp only [CollatzResearch.WordTrace]
  refine ⟨24682042581362866590534017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16454695054241911060356011 24682042581362866590534017)
  ·
    refine ⟨18511531936022149942900513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24682042581362866590534017 18511531936022149942900513)
    ·
      refine ⟨13883648952016612457175385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18511531936022149942900513 13883648952016612457175385)
      ·
        refine ⟨10412736714012459342881539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13883648952016612457175385 10412736714012459342881539)
        ·
          refine ⟨15619105071018689014322309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10412736714012459342881539 15619105071018689014322309)
          ·
            refine ⟨2928582200816004190185433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15619105071018689014322309 2928582200816004190185433)
            ·
              refine ⟨2196436650612003142639075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2928582200816004190185433 2196436650612003142639075)
              ·
                refine ⟨3294654975918004713958613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2196436650612003142639075 3294654975918004713958613)
                ·
                  refine ⟨77218475998078235483405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3294654975918004713958613 77218475998078235483405)
                  ·
                    rfl

theorem cell22_676721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 7].length) (baseStart_676721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_676721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_676721 prefixEnd_676721 := by exact prefixLift 676721
  have htrace : WordTrace (prefixWord ++ tailWord_676721) baseStart_676721 baseEnd_676721 := by
    simpa [prefixWord, tailWord_676721, baseEnd_676721] using wordTrace_append hprefix tailTrace_676721
  have hstable : (prefixWord ++ tailWord_676721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676721).length < 2 ^ (prefixWord ++ tailWord_676721).sum := by decide
  have hdescent : baseEnd_676721 < baseStart_676721 := by decide
  rcases family_descends (prefixWord ++ tailWord_676721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676725 : List Nat := [1, 3, 4, 1, 1, 2, 3, 1, 3, 3]
def baseStart_676725 : Nat := 118140960795 + 676725 * 2 ^ 59
def prefixEnd_676725 : Nat := 4983230072969 + 3 ^ 40 * 676725 * 2
def baseEnd_676725 : Nat := 231656797275980029350203

theorem tailTrace_676725 : CollatzResearch.WordTrace tailWord_676725 prefixEnd_676725 231656797275980029350203 := by
  unfold tailWord_676725
  simp only [CollatzResearch.WordTrace]
  refine ⟨24682188473348375273679629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16454792315565583515786419 24682188473348375273679629)
  ·
    refine ⟨9255820677505640727629861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24682188473348375273679629 9255820677505640727629861)
    ·
      refine ⟨1735466377032307636430599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9255820677505640727629861 1735466377032307636430599)
      ·
        refine ⟨2603199565548461454645899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1735466377032307636430599 2603199565548461454645899)
        ·
          refine ⟨3904799348322692181968849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2603199565548461454645899 3904799348322692181968849)
          ·
            refine ⟨2928599511242019136476637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3904799348322692181968849 2928599511242019136476637)
            ·
              refine ⟨1098224816715757176178739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2928599511242019136476637 1098224816715757176178739)
              ·
                refine ⟨1647337225073635764268109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1098224816715757176178739 1647337225073635764268109)
                ·
                  refine ⟨617751459402613411600541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1647337225073635764268109 617751459402613411600541)
                  ·
                    refine ⟨231656797275980029350203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 617751459402613411600541 231656797275980029350203)
                    ·
                      rfl

theorem cell22_676725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_676725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_676725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_676725 prefixEnd_676725 := by exact prefixLift 676725
  have htrace : WordTrace (prefixWord ++ tailWord_676725) baseStart_676725 baseEnd_676725 := by
    simpa [prefixWord, tailWord_676725, baseEnd_676725] using wordTrace_append hprefix tailTrace_676725
  have hstable : (prefixWord ++ tailWord_676725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676725).length < 2 ^ (prefixWord ++ tailWord_676725).sum := by decide
  have hdescent : baseEnd_676725 < baseStart_676725 := by decide
  rcases family_descends (prefixWord ++ tailWord_676725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676768 : List Nat := [2, 1, 1, 4, 1, 1, 2, 5, 1, 4]
def baseStart_676768 : Nat := 118140960795 + 676768 * 2 ^ 59
def prefixEnd_676768 : Nat := 4983230072969 + 3 ^ 40 * 676768 * 2
def baseEnd_676768 : Nat := 231671517054742250525071

theorem tailTrace_676768 : CollatzResearch.WordTrace tailWord_676768 prefixEnd_676768 231671517054742250525071 := by
  unfold tailWord_676768
  simp only [CollatzResearch.WordTrace]
  refine ⟨12341878406096296808747479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16455837874795062411663305 12341878406096296808747479)
  ·
    refine ⟨18512817609144445213121219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12341878406096296808747479 18512817609144445213121219)
    ·
      refine ⟨27769226413716667819681829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18512817609144445213121219 27769226413716667819681829)
      ·
        refine ⟨5206729952571875216190343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27769226413716667819681829 5206729952571875216190343)
        ·
          refine ⟨7810094928857812824285515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5206729952571875216190343 7810094928857812824285515)
          ·
            refine ⟨11715142393286719236428273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7810094928857812824285515 11715142393286719236428273)
            ·
              refine ⟨8786356794965039427321205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11715142393286719236428273 8786356794965039427321205)
              ·
                refine ⟨823720949527972446311363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8786356794965039427321205 823720949527972446311363)
                ·
                  refine ⟨1235581424291958669467045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 823720949527972446311363 1235581424291958669467045)
                  ·
                    refine ⟨231671517054742250525071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1235581424291958669467045 231671517054742250525071)
                    ·
                      rfl

theorem cell22_676768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 1, 4].length) (baseStart_676768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_676768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_676768 prefixEnd_676768 := by exact prefixLift 676768
  have htrace : WordTrace (prefixWord ++ tailWord_676768) baseStart_676768 baseEnd_676768 := by
    simpa [prefixWord, tailWord_676768, baseEnd_676768] using wordTrace_append hprefix tailTrace_676768
  have hstable : (prefixWord ++ tailWord_676768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676768).length < 2 ^ (prefixWord ++ tailWord_676768).sum := by decide
  have hdescent : baseEnd_676768 < baseStart_676768 := by decide
  rcases family_descends (prefixWord ++ tailWord_676768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676860 : List Nat := [2, 2, 2, 1, 2, 3, 2, 2, 3, 3]
def baseStart_676860 : Nat := 118140960795 + 676860 * 2 ^ 59
def prefixEnd_676860 : Nat := 4983230072969 + 3 ^ 40 * 676860 * 2
def baseEnd_676860 : Nat := 231703010534884677224789

theorem tailTrace_676860 : CollatzResearch.WordTrace tailWord_676860 prefixEnd_676860 231703010534884677224789 := by
  unfold tailWord_676860
  simp only [CollatzResearch.WordTrace]
  refine ⟨12343556163929646664922017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16458074885239528886562689 12343556163929646664922017)
  ·
    refine ⟨9257667122947234998691513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12343556163929646664922017 9257667122947234998691513)
    ·
      refine ⟨6943250342210426249018635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9257667122947234998691513 6943250342210426249018635)
      ·
        refine ⟨10414875513315639373527953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6943250342210426249018635 10414875513315639373527953)
        ·
          refine ⟨7811156634986729530145965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10414875513315639373527953 7811156634986729530145965)
          ·
            refine ⟨2929183738120023573804737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7811156634986729530145965 2929183738120023573804737)
            ·
              refine ⟨2196887803590017680353553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2929183738120023573804737 2196887803590017680353553)
              ·
                refine ⟨1647665852692513260265165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2196887803590017680353553 1647665852692513260265165)
                ·
                  refine ⟨617874694759692472599437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1647665852692513260265165 617874694759692472599437)
                  ·
                    refine ⟨231703010534884677224789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 617874694759692472599437 231703010534884677224789)
                    ·
                      rfl

theorem cell22_676860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_676860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_676860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_676860 prefixEnd_676860 := by exact prefixLift 676860
  have htrace : WordTrace (prefixWord ++ tailWord_676860) baseStart_676860 baseEnd_676860 := by
    simpa [prefixWord, tailWord_676860, baseEnd_676860] using wordTrace_append hprefix tailTrace_676860
  have hstable : (prefixWord ++ tailWord_676860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676860).length < 2 ^ (prefixWord ++ tailWord_676860).sum := by decide
  have hdescent : baseEnd_676860 < baseStart_676860 := by decide
  rcases family_descends (prefixWord ++ tailWord_676860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676920 : List Nat := [2, 1, 2, 1, 5, 2, 1, 1, 3, 4]
def baseStart_676920 : Nat := 118140960795 + 676920 * 2 ^ 59
def prefixEnd_676920 : Nat := 4983230072969 + 3 ^ 40 * 676920 * 2
def baseEnd_676920 : Nat := 231723549761064520724605

theorem tailTrace_676920 : CollatzResearch.WordTrace tailWord_676920 prefixEnd_676920 231723549761064520724605 := by
  unfold tailWord_676920
  simp only [CollatzResearch.WordTrace]
  refine ⟨12344650353820961788514107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16459533805094615718018809 12344650353820961788514107)
  ·
    refine ⟨18516975530731442682771161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12344650353820961788514107 18516975530731442682771161)
    ·
      refine ⟨13887731648048582012078371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18516975530731442682771161 13887731648048582012078371)
      ·
        refine ⟨20831597472072873018117557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13887731648048582012078371 20831597472072873018117557)
        ·
          refine ⟨1952962263006831845448521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20831597472072873018117557 1952962263006831845448521)
          ·
            refine ⟨1464721697255123884086391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1952962263006831845448521 1464721697255123884086391)
            ·
              refine ⟨2197082545882685826129587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1464721697255123884086391 2197082545882685826129587)
              ·
                refine ⟨3295623818824028739194381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2197082545882685826129587 3295623818824028739194381)
                ·
                  refine ⟨1235858932059010777197893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3295623818824028739194381 1235858932059010777197893)
                  ·
                    refine ⟨231723549761064520724605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1235858932059010777197893 231723549761064520724605)
                    ·
                      rfl

theorem cell22_676920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_676920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_676920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_676920 prefixEnd_676920 := by exact prefixLift 676920
  have htrace : WordTrace (prefixWord ++ tailWord_676920) baseStart_676920 baseEnd_676920 := by
    simpa [prefixWord, tailWord_676920, baseEnd_676920] using wordTrace_append hprefix tailTrace_676920
  have hstable : (prefixWord ++ tailWord_676920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676920).length < 2 ^ (prefixWord ++ tailWord_676920).sum := by decide
  have hdescent : baseEnd_676920 < baseStart_676920 := by decide
  rcases family_descends (prefixWord ++ tailWord_676920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676933 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 3, 5]
def baseStart_676933 : Nat := 118140960795 + 676933 * 2 ^ 59
def prefixEnd_676933 : Nat := 4983230072969 + 3 ^ 40 * 676933 * 2
def baseEnd_676933 : Nat := 231727999926736820149565

theorem tailTrace_676933 : CollatzResearch.WordTrace tailWord_676933 prefixEnd_676933 231727999926736820149565 := by
  unfold tailWord_676933
  simp only [CollatzResearch.WordTrace]
  refine ⟨24689774856594826797251453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16459849904396551198167635 24689774856594826797251453)
  ·
    refine ⟨9258665571223060048969295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24689774856594826797251453 9258665571223060048969295)
    ·
      refine ⟨13887998356834590073453943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9258665571223060048969295 13887998356834590073453943)
      ·
        refine ⟨20831997535251885110180915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13887998356834590073453943 20831997535251885110180915)
        ·
          refine ⟨31247996302877827665271373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20831997535251885110180915 31247996302877827665271373)
          ·
            refine ⟨11717998613579185374476765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31247996302877827665271373 11717998613579185374476765)
            ·
              refine ⟨4394249480092194515428787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11717998613579185374476765 4394249480092194515428787)
              ·
                refine ⟨6591374220138291773143181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4394249480092194515428787 6591374220138291773143181)
                ·
                  refine ⟨2471765332551859414928693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6591374220138291773143181 2471765332551859414928693)
                  ·
                    refine ⟨231727999926736820149565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2471765332551859414928693 231727999926736820149565)
                    ·
                      rfl

theorem cell22_676933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_676933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_676933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_676933 prefixEnd_676933 := by exact prefixLift 676933
  have htrace : WordTrace (prefixWord ++ tailWord_676933) baseStart_676933 baseEnd_676933 := by
    simpa [prefixWord, tailWord_676933, baseEnd_676933] using wordTrace_append hprefix tailTrace_676933
  have hstable : (prefixWord ++ tailWord_676933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676933).length < 2 ^ (prefixWord ++ tailWord_676933).sum := by decide
  have hdescent : baseEnd_676933 < baseStart_676933 := by decide
  rcases family_descends (prefixWord ++ tailWord_676933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676967 : List Nat := [1, 1, 5, 1, 1, 3, 2, 3, 2, 3]
def baseStart_676967 : Nat := 118140960795 + 676967 * 2 ^ 59
def prefixEnd_676967 : Nat := 4983230072969 + 3 ^ 40 * 676967 * 2
def baseEnd_676967 : Nat := 231739638821572064799461

theorem tailTrace_676967 : CollatzResearch.WordTrace tailWord_676967 prefixEnd_676967 231739638821572064799461 := by
  unfold tailWord_676967
  simp only [CollatzResearch.WordTrace]
  refine ⟨24691014938471650603989155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16460676625647767069326103 24691014938471650603989155)
  ·
    refine ⟨37036522407707475905983733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24691014938471650603989155 37036522407707475905983733)
    ·
      refine ⟨3472173975722575866185975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37036522407707475905983733 3472173975722575866185975)
      ·
        refine ⟨5208260963583863799278963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3472173975722575866185975 5208260963583863799278963)
        ·
          refine ⟨7812391445375795698918445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5208260963583863799278963 7812391445375795698918445)
          ·
            refine ⟨2929646792015923387094417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7812391445375795698918445 2929646792015923387094417)
            ·
              refine ⟨2197235094011942540320813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2929646792015923387094417 2197235094011942540320813)
              ·
                refine ⟨823963160254478452620305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2197235094011942540320813 823963160254478452620305)
                ·
                  refine ⟨617972370190858839465229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 823963160254478452620305 617972370190858839465229)
                  ·
                    refine ⟨231739638821572064799461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 617972370190858839465229 231739638821572064799461)
                    ·
                      rfl

theorem cell22_676967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_676967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_676967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_676967 prefixEnd_676967 := by exact prefixLift 676967
  have htrace : WordTrace (prefixWord ++ tailWord_676967) baseStart_676967 baseEnd_676967 := by
    simpa [prefixWord, tailWord_676967, baseEnd_676967] using wordTrace_append hprefix tailTrace_676967
  have hstable : (prefixWord ++ tailWord_676967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676967).length < 2 ^ (prefixWord ++ tailWord_676967).sum := by decide
  have hdescent : baseEnd_676967 < baseStart_676967 := by decide
  rcases family_descends (prefixWord ++ tailWord_676967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676995 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 5, 3]
def baseStart_676995 : Nat := 118140960795 + 676995 * 2 ^ 59
def prefixEnd_676995 : Nat := 4983230072969 + 3 ^ 40 * 676995 * 2
def baseEnd_676995 : Nat := 231749223793789325099375

theorem tailTrace_676995 : CollatzResearch.WordTrace tailWord_676995 prefixEnd_676995 231749223793789325099375 := by
  unfold tailWord_676995
  simp only [CollatzResearch.WordTrace]
  refine ⟨24692036182370211386008439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16461357454913474257338959 24692036182370211386008439)
  ·
    refine ⟨37038054273555317079012659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24692036182370211386008439 37038054273555317079012659)
    ·
      refine ⟨55557081410332975618518989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37038054273555317079012659 55557081410332975618518989)
      ·
        refine ⟨20833905528874865856944621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55557081410332975618518989 20833905528874865856944621)
        ·
          refine ⟨7812714573328074696354233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20833905528874865856944621 7812714573328074696354233)
          ·
            refine ⟨5859535929996056022265675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7812714573328074696354233 5859535929996056022265675)
            ·
              refine ⟨8789303894994084033398513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5859535929996056022265675 8789303894994084033398513)
              ·
                refine ⟨6591977921245563025048885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8789303894994084033398513 6591977921245563025048885)
                ·
                  refine ⟨617997930116771533598333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6591977921245563025048885 617997930116771533598333)
                  ·
                    refine ⟨231749223793789325099375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 617997930116771533598333 231749223793789325099375)
                    ·
                      rfl

theorem cell22_676995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 5, 3].length) (baseStart_676995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_676995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_676995 prefixEnd_676995 := by exact prefixLift 676995
  have htrace : WordTrace (prefixWord ++ tailWord_676995) baseStart_676995 baseEnd_676995 := by
    simpa [prefixWord, tailWord_676995, baseEnd_676995] using wordTrace_append hprefix tailTrace_676995
  have hstable : (prefixWord ++ tailWord_676995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676995).length < 2 ^ (prefixWord ++ tailWord_676995).sum := by decide
  have hdescent : baseEnd_676995 < baseStart_676995 := by decide
  rcases family_descends (prefixWord ++ tailWord_676995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677089 : List Nat := [1, 2, 3, 1, 3, 4, 1, 2, 1, 4]
def baseStart_677089 : Nat := 118140960795 + 677089 * 2 ^ 59
def prefixEnd_677089 : Nat := 4983230072969 + 3 ^ 40 * 677089 * 2
def baseEnd_677089 : Nat := 231781401914804413249087

theorem tailTrace_677089 : CollatzResearch.WordTrace tailWord_677089 prefixEnd_677089 231781401914804413249087 := by
  unfold tailWord_677089
  simp only [CollatzResearch.WordTrace]
  refine ⟨24695464644029665439930321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16463643096019776959953547 24695464644029665439930321)
  ·
    refine ⟨18521598483022249079947741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24695464644029665439930321 18521598483022249079947741)
    ·
      refine ⟨6945599431133343404980403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18521598483022249079947741 6945599431133343404980403)
      ·
        refine ⟨10418399146700015107470605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6945599431133343404980403 10418399146700015107470605)
        ·
          refine ⟨3906899680012505665301477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10418399146700015107470605 3906899680012505665301477)
          ·
            refine ⟨732543690002344812244027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3906899680012505665301477 732543690002344812244027)
            ·
              refine ⟨1098815535003517218366041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 732543690002344812244027 1098815535003517218366041)
              ·
                refine ⟨824111651252637913774531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1098815535003517218366041 824111651252637913774531)
                ·
                  refine ⟨1236167476878956870661797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 824111651252637913774531 1236167476878956870661797)
                  ·
                    refine ⟨231781401914804413249087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1236167476878956870661797 231781401914804413249087)
                    ·
                      rfl

theorem cell22_677089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_677089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_677089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_677089 prefixEnd_677089 := by exact prefixLift 677089
  have htrace : WordTrace (prefixWord ++ tailWord_677089) baseStart_677089 baseEnd_677089 := by
    simpa [prefixWord, tailWord_677089, baseEnd_677089] using wordTrace_append hprefix tailTrace_677089
  have hstable : (prefixWord ++ tailWord_677089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677089).length < 2 ^ (prefixWord ++ tailWord_677089).sum := by decide
  have hdescent : baseEnd_677089 < baseStart_677089 := by decide
  rcases family_descends (prefixWord ++ tailWord_677089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677102 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 6, 3]
def baseStart_677102 : Nat := 118140960795 + 677102 * 2 ^ 59
def prefixEnd_677102 : Nat := 4983230072969 + 3 ^ 40 * 677102 * 2
def baseEnd_677102 : Nat := 231785852080476712674047

theorem tailTrace_677102 : CollatzResearch.WordTrace tailWord_677102 prefixEnd_677102 231785852080476712674047 := by
  unfold tailWord_677102
  simp only [CollatzResearch.WordTrace]
  refine ⟨3086992349122821082519195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16463959195321712440102373 3086992349122821082519195)
  ·
    refine ⟨4630488523684231623778793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3086992349122821082519195 4630488523684231623778793)
    ·
      refine ⟨3472866392763173717834095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4630488523684231623778793 3472866392763173717834095)
      ·
        refine ⟨5209299589144760576751143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3472866392763173717834095 5209299589144760576751143)
        ·
          refine ⟨7813949383717140865126715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5209299589144760576751143 7813949383717140865126715)
          ·
            refine ⟨11720924075575711297690073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7813949383717140865126715 11720924075575711297690073)
            ·
              refine ⟨8790693056681783473267555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11720924075575711297690073 8790693056681783473267555)
              ·
                refine ⟨13186039585022675209901333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8790693056681783473267555 13186039585022675209901333)
                ·
                  refine ⟨618095605547937900464125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13186039585022675209901333 618095605547937900464125)
                  ·
                    refine ⟨231785852080476712674047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 618095605547937900464125 231785852080476712674047)
                    ·
                      rfl

theorem cell22_677102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_677102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_677102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_677102 prefixEnd_677102 := by exact prefixLift 677102
  have htrace : WordTrace (prefixWord ++ tailWord_677102) baseStart_677102 baseEnd_677102 := by
    simpa [prefixWord, tailWord_677102, baseEnd_677102] using wordTrace_append hprefix tailTrace_677102
  have hstable : (prefixWord ++ tailWord_677102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677102).length < 2 ^ (prefixWord ++ tailWord_677102).sum := by decide
  have hdescent : baseEnd_677102 < baseStart_677102 := by decide
  rcases family_descends (prefixWord ++ tailWord_677102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677106 : List Nat := [3, 2, 1, 3, 3, 1, 3, 1, 1, 4]
def baseStart_677106 : Nat := 118140960795 + 677106 * 2 ^ 59
def prefixEnd_677106 : Nat := 4983230072969 + 3 ^ 40 * 677106 * 2
def baseEnd_677106 : Nat := 231787221362222035574035

theorem tailTrace_677106 : CollatzResearch.WordTrace tailWord_677106 prefixEnd_677106 231787221362222035574035 := by
  unfold tailWord_677106
  simp only [CollatzResearch.WordTrace]
  refine ⟨6174021171242019335824793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16464056456645384895532781 6174021171242019335824793)
  ·
    refine ⟨4630515878431514501868595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6174021171242019335824793 4630515878431514501868595)
    ·
      refine ⟨6945773817647271752802893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4630515878431514501868595 6945773817647271752802893)
      ·
        refine ⟨2604665181617726907301085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6945773817647271752802893 2604665181617726907301085)
        ·
          refine ⟨976749443106647590237907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2604665181617726907301085 976749443106647590237907)
          ·
            refine ⟨1465124164659971385356861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 976749443106647590237907 1465124164659971385356861)
            ·
              refine ⟨549421561747489269508823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1465124164659971385356861 549421561747489269508823)
              ·
                refine ⟨824132342621233904263235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 549421561747489269508823 824132342621233904263235)
                ·
                  refine ⟨1236198513931850856394853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 824132342621233904263235 1236198513931850856394853)
                  ·
                    refine ⟨231787221362222035574035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1236198513931850856394853 231787221362222035574035)
                    ·
                      rfl

theorem cell22_677106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_677106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_677106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_677106 prefixEnd_677106 := by exact prefixLift 677106
  have htrace : WordTrace (prefixWord ++ tailWord_677106) baseStart_677106 baseEnd_677106 := by
    simpa [prefixWord, tailWord_677106, baseEnd_677106] using wordTrace_append hprefix tailTrace_677106
  have hstable : (prefixWord ++ tailWord_677106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677106).length < 2 ^ (prefixWord ++ tailWord_677106).sum := by decide
  have hdescent : baseEnd_677106 < baseStart_677106 := by decide
  rcases family_descends (prefixWord ++ tailWord_677106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677119 : List Nat := [1, 1, 2, 2, 1, 6, 2, 2, 2, 3]
def baseStart_677119 : Nat := 118140960795 + 677119 * 2 ^ 59
def prefixEnd_677119 : Nat := 4983230072969 + 3 ^ 40 * 677119 * 2
def baseEnd_677119 : Nat := 231791671527894334998995

theorem tailTrace_677119 : CollatzResearch.WordTrace tailWord_677119 prefixEnd_677119 231791671527894334998995 := by
  unfold tailWord_677119
  simp only [CollatzResearch.WordTrace]
  refine ⟨24696558833920980563522411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16464372555947320375681607 24696558833920980563522411)
  ·
    refine ⟨37044838250881470845283617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24696558833920980563522411 37044838250881470845283617)
    ·
      refine ⟨27783628688161103133962713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37044838250881470845283617 27783628688161103133962713)
      ·
        refine ⟨20837721516120827350472035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27783628688161103133962713 20837721516120827350472035)
        ·
          refine ⟨31256582274181241025708053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20837721516120827350472035 31256582274181241025708053)
          ·
            refine ⟨1465152294102245673080065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31256582274181241025708053 1465152294102245673080065)
            ·
              refine ⟨1098864220576684254810049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1465152294102245673080065 1098864220576684254810049)
              ·
                refine ⟨824148165432513191107537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1098864220576684254810049 824148165432513191107537)
                ·
                  refine ⟨618111124074384893330653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 824148165432513191107537 618111124074384893330653)
                  ·
                    refine ⟨231791671527894334998995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 618111124074384893330653 231791671527894334998995)
                    ·
                      rfl

theorem cell22_677119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 2, 3].length) (baseStart_677119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_677119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_677119 prefixEnd_677119 := by exact prefixLift 677119
  have htrace : WordTrace (prefixWord ++ tailWord_677119) baseStart_677119 baseEnd_677119 := by
    simpa [prefixWord, tailWord_677119, baseEnd_677119] using wordTrace_append hprefix tailTrace_677119
  have hstable : (prefixWord ++ tailWord_677119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677119).length < 2 ^ (prefixWord ++ tailWord_677119).sum := by decide
  have hdescent : baseEnd_677119 < baseStart_677119 := by decide
  rcases family_descends (prefixWord ++ tailWord_677119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677121 : List Nat := [1, 2, 4, 1, 1, 5, 2, 2, 4]
def baseStart_677121 : Nat := 118140960795 + 677121 * 2 ^ 59
def prefixEnd_677121 : Nat := 4983230072969 + 3 ^ 40 * 677121 * 2
def baseEnd_677121 : Nat := 77264118722922332149663

theorem tailTrace_677121 : CollatzResearch.WordTrace tailWord_677121 prefixEnd_677121 77264118722922332149663 := by
  unfold tailWord_677121
  simp only [CollatzResearch.WordTrace]
  refine ⟨24696631779913734905095217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16464421186609156603396811 24696631779913734905095217)
  ·
    refine ⟨18522473834935301178821413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24696631779913734905095217 18522473834935301178821413)
    ·
      refine ⟨3472963844050368971029015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18522473834935301178821413 3472963844050368971029015)
      ·
        refine ⟨5209445766075553456543523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3472963844050368971029015 5209445766075553456543523)
        ·
          refine ⟨7814168649113330184815285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5209445766075553456543523 7814168649113330184815285)
          ·
            refine ⟨732578310854374704826433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7814168649113330184815285 732578310854374704826433)
            ·
              refine ⟨549433733140781028619825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 732578310854374704826433 549433733140781028619825)
              ·
                refine ⟨412075299855585771464869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 549433733140781028619825 412075299855585771464869)
                ·
                  refine ⟨77264118722922332149663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 412075299855585771464869 77264118722922332149663)
                  ·
                    rfl

theorem cell22_677121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 2, 4].length) (baseStart_677121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_677121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_677121 prefixEnd_677121 := by exact prefixLift 677121
  have htrace : WordTrace (prefixWord ++ tailWord_677121) baseStart_677121 baseEnd_677121 := by
    simpa [prefixWord, tailWord_677121, baseEnd_677121] using wordTrace_append hprefix tailTrace_677121
  have hstable : (prefixWord ++ tailWord_677121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677121).length < 2 ^ (prefixWord ++ tailWord_677121).sum := by decide
  have hdescent : baseEnd_677121 < baseStart_677121 := by decide
  rcases family_descends (prefixWord ++ tailWord_677121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677130 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 2, 7]
def baseStart_677130 : Nat := 118140960795 + 677130 * 2 ^ 59
def prefixEnd_677130 : Nat := 4983230072969 + 3 ^ 40 * 677130 * 2
def baseEnd_677130 : Nat := 231795437052693972973961

theorem tailTrace_677130 : CollatzResearch.WordTrace tailWord_677130 prefixEnd_677130 231795437052693972973961 := by
  unfold tailWord_677130
  simp only [CollatzResearch.WordTrace]
  refine ⟨6174240009220282360543211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16464640024587419628115229 6174240009220282360543211)
  ·
    refine ⟨9261360013830423540814817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6174240009220282360543211 9261360013830423540814817)
    ·
      refine ⟨6946020010372817655611113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9261360013830423540814817 6946020010372817655611113)
      ·
        refine ⟨5209515007779613241708335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6946020010372817655611113 5209515007779613241708335)
        ·
          refine ⟨7814272511669419862562503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5209515007779613241708335 7814272511669419862562503)
          ·
            refine ⟨11721408767504129793843755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7814272511669419862562503 11721408767504129793843755)
            ·
              refine ⟨17582113151256194690765633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11721408767504129793843755 17582113151256194690765633)
              ·
                refine ⟨13186584863442146018074225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17582113151256194690765633 13186584863442146018074225)
                ·
                  refine ⟨9889938647581609513555669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13186584863442146018074225 9889938647581609513555669)
                  ·
                    refine ⟨231795437052693972973961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9889938647581609513555669 231795437052693972973961)
                    ·
                      rfl

theorem cell22_677130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_677130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_677130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_677130 prefixEnd_677130 := by exact prefixLift 677130
  have htrace : WordTrace (prefixWord ++ tailWord_677130) baseStart_677130 baseEnd_677130 := by
    simpa [prefixWord, tailWord_677130, baseEnd_677130] using wordTrace_append hprefix tailTrace_677130
  have hstable : (prefixWord ++ tailWord_677130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677130).length < 2 ^ (prefixWord ++ tailWord_677130).sum := by decide
  have hdescent : baseEnd_677130 < baseStart_677130 := by decide
  rcases family_descends (prefixWord ++ tailWord_677130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677132 : List Nat := [2, 2, 1, 2, 2, 5, 1, 7]
def baseStart_677132 : Nat := 118140960795 + 677132 * 2 ^ 59
def prefixEnd_677132 : Nat := 4983230072969 + 3 ^ 40 * 677132 * 2
def baseEnd_677132 : Nat := 25755124632618514935995

theorem tailTrace_677132 : CollatzResearch.WordTrace tailWord_677132 prefixEnd_677132 25755124632618514935995 := by
  unfold tailWord_677132
  simp only [CollatzResearch.WordTrace]
  refine ⟨12348516491436941891872825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16464688655249255855830433 12348516491436941891872825)
  ·
    refine ⟨9261387368577706418904619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12348516491436941891872825 9261387368577706418904619)
    ·
      refine ⟨13892081052866559628356929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9261387368577706418904619 13892081052866559628356929)
      ·
        refine ⟨10419060789649919721267697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13892081052866559628356929 10419060789649919721267697)
        ·
          refine ⟨7814295592237439790950773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10419060789649919721267697 7814295592237439790950773)
          ·
            refine ⟨732590211772259980401635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7814295592237439790950773 732590211772259980401635)
            ·
              refine ⟨1098885317658389970602453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 732590211772259980401635 1098885317658389970602453)
              ·
                refine ⟨25755124632618514935995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1098885317658389970602453 25755124632618514935995)
                ·
                  rfl

theorem cell22_677132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 7].length) (baseStart_677132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_677132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_677132 prefixEnd_677132 := by exact prefixLift 677132
  have htrace : WordTrace (prefixWord ++ tailWord_677132) baseStart_677132 baseEnd_677132 := by
    simpa [prefixWord, tailWord_677132, baseEnd_677132] using wordTrace_append hprefix tailTrace_677132
  have hstable : (prefixWord ++ tailWord_677132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677132).length < 2 ^ (prefixWord ++ tailWord_677132).sum := by decide
  have hdescent : baseEnd_677132 < baseStart_677132 := by decide
  rcases family_descends (prefixWord ++ tailWord_677132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677149 : List Nat := [1, 4, 2, 3, 1, 2, 3, 6]
def baseStart_677149 : Nat := 118140960795 + 677149 * 2 ^ 59
def prefixEnd_677149 : Nat := 4983230072969 + 3 ^ 40 * 677149 * 2
def baseEnd_677149 : Nat := 25755771237887139638767

theorem tailTrace_677149 : CollatzResearch.WordTrace tailWord_677149 prefixEnd_677149 25755771237887139638767 := by
  unfold tailWord_677149
  simp only [CollatzResearch.WordTrace]
  refine ⟨24697653023812295687114501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16465102015874863791409667 24697653023812295687114501)
  ·
    refine ⟨4630809941964805441333969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24697653023812295687114501 4630809941964805441333969)
    ·
      refine ⟨3473107456473604081000477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4630809941964805441333969 3473107456473604081000477)
      ·
        refine ⟨1302415296177601530375179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3473107456473604081000477 1302415296177601530375179)
        ·
          refine ⟨1953622944266402295562769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1302415296177601530375179 1953622944266402295562769)
          ·
            refine ⟨1465217208199801721672077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1953622944266402295562769 1465217208199801721672077)
            ·
              refine ⟨549456453074925645627029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1465217208199801721672077 549456453074925645627029)
              ·
                refine ⟨25755771237887139638767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 549456453074925645627029 25755771237887139638767)
                ·
                  rfl

theorem cell22_677149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 6].length) (baseStart_677149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_677149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_677149 prefixEnd_677149 := by exact prefixLift 677149
  have htrace : WordTrace (prefixWord ++ tailWord_677149) baseStart_677149 baseEnd_677149 := by
    simpa [prefixWord, tailWord_677149, baseEnd_677149] using wordTrace_append hprefix tailTrace_677149
  have hstable : (prefixWord ++ tailWord_677149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677149).length < 2 ^ (prefixWord ++ tailWord_677149).sum := by decide
  have hdescent : baseEnd_677149 < baseStart_677149 := by decide
  rcases family_descends (prefixWord ++ tailWord_677149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677151 : List Nat := [1, 1, 2, 4, 5, 1, 1, 1, 2, 4]
def baseStart_677151 : Nat := 118140960795 + 677151 * 2 ^ 59
def prefixEnd_677151 : Nat := 4983230072969 + 3 ^ 40 * 677151 * 2
def baseEnd_677151 : Nat := 231802625781856918198897

theorem tailTrace_677151 : CollatzResearch.WordTrace tailWord_677151 prefixEnd_677151 231802625781856918198897 := by
  unfold tailWord_677151
  simp only [CollatzResearch.WordTrace]
  refine ⟨24697725969805050028687307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16465150646536700019124871 24697725969805050028687307)
  ·
    refine ⟨37046588954707575043030961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24697725969805050028687307 37046588954707575043030961)
    ·
      refine ⟨27784941716030681282273221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37046588954707575043030961 27784941716030681282273221)
      ·
        refine ⟨5209676571755752740426229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27784941716030681282273221 5209676571755752740426229)
        ·
          refine ⟨488407178602101819414959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5209676571755752740426229 488407178602101819414959)
          ·
            refine ⟨732610767903152729122439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488407178602101819414959 732610767903152729122439)
            ·
              refine ⟨1098916151854729093683659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 732610767903152729122439 1098916151854729093683659)
              ·
                refine ⟨1648374227782093640525489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1098916151854729093683659 1648374227782093640525489)
                ·
                  refine ⟨1236280670836570230394117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1648374227782093640525489 1236280670836570230394117)
                  ·
                    refine ⟨231802625781856918198897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1236280670836570230394117 231802625781856918198897)
                    ·
                      rfl

theorem cell22_677151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 2, 4].length) (baseStart_677151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_677151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_677151 prefixEnd_677151 := by exact prefixLift 677151
  have htrace : WordTrace (prefixWord ++ tailWord_677151) baseStart_677151 baseEnd_677151 := by
    simpa [prefixWord, tailWord_677151, baseEnd_677151] using wordTrace_append hprefix tailTrace_677151
  have hstable : (prefixWord ++ tailWord_677151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677151).length < 2 ^ (prefixWord ++ tailWord_677151).sum := by decide
  have hdescent : baseEnd_677151 < baseStart_677151 := by decide
  rcases family_descends (prefixWord ++ tailWord_677151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677297 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 1, 8]
def baseStart_677297 : Nat := 118140960795 + 677297 * 2 ^ 59
def prefixEnd_677297 : Nat := 4983230072969 + 3 ^ 40 * 677297 * 2
def baseEnd_677297 : Nat := 231852604565561204048449

theorem tailTrace_677297 : CollatzResearch.WordTrace tailWord_677297 prefixEnd_677297 231852604565561204048449 := by
  unfold tailWord_677297
  simp only [CollatzResearch.WordTrace]
  refine ⟨24703051027276116963502145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16468700684850744642334763 24703051027276116963502145)
  ·
    refine ⟨18527288270457087722626609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24703051027276116963502145 18527288270457087722626609)
    ·
      refine ⟨13895466202842815791969957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18527288270457087722626609 13895466202842815791969957)
      ·
        refine ⟨2605399913033027960994367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13895466202842815791969957 2605399913033027960994367)
        ·
          refine ⟨3908099869549541941491551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2605399913033027960994367 3908099869549541941491551)
          ·
            refine ⟨5862149804324312912237327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3908099869549541941491551 5862149804324312912237327)
            ·
              refine ⟨8793224706486469368355991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5862149804324312912237327 8793224706486469368355991)
              ·
                refine ⟨13189837059729704052533987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8793224706486469368355991 13189837059729704052533987)
                ·
                  refine ⟨19784755589594556078800981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13189837059729704052533987 19784755589594556078800981)
                  ·
                    refine ⟨231852604565561204048449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 19784755589594556078800981 231852604565561204048449)
                    ·
                      rfl

theorem cell22_677297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_677297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_677297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_677297 prefixEnd_677297 := by exact prefixLift 677297
  have htrace : WordTrace (prefixWord ++ tailWord_677297) baseStart_677297 baseEnd_677297 := by
    simpa [prefixWord, tailWord_677297, baseEnd_677297] using wordTrace_append hprefix tailTrace_677297
  have hstable : (prefixWord ++ tailWord_677297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677297).length < 2 ^ (prefixWord ++ tailWord_677297).sum := by decide
  have hdescent : baseEnd_677297 < baseStart_677297 := by decide
  rcases family_descends (prefixWord ++ tailWord_677297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677316 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 5, 3]
def baseStart_677316 : Nat := 118140960795 + 677316 * 2 ^ 59
def prefixEnd_677316 : Nat := 4983230072969 + 3 ^ 40 * 677316 * 2
def baseEnd_677316 : Nat := 231859108653851487823391

theorem tailTrace_677316 : CollatzResearch.WordTrace tailWord_677316 prefixEnd_677316 231859108653851487823391 := by
  unfold tailWord_677316
  simp only [CollatzResearch.WordTrace]
  refine ⟨12351872007103641604221901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16469162676138188805629201 12351872007103641604221901)
  ·
    refine ⟨4631952002663865601583213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12351872007103641604221901 4631952002663865601583213)
    ·
      refine ⟨1736982000998949600593705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4631952002663865601583213 1736982000998949600593705)
      ·
        refine ⟨1302736500749212200445279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1736982000998949600593705 1302736500749212200445279)
        ·
          refine ⟨1954104751123818300667919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1302736500749212200445279 1954104751123818300667919)
          ·
            refine ⟨2931157126685727451001879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1954104751123818300667919 2931157126685727451001879)
            ·
              refine ⟨4396735690028591176502819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2931157126685727451001879 4396735690028591176502819)
              ·
                refine ⟨6595103535042886764754229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4396735690028591176502819 6595103535042886764754229)
                ·
                  refine ⟨618290956410270634195709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6595103535042886764754229 618290956410270634195709)
                  ·
                    refine ⟨231859108653851487823391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 618290956410270634195709 231859108653851487823391)
                    ·
                      rfl

theorem cell22_677316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_677316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_677316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_677316 prefixEnd_677316 := by exact prefixLift 677316
  have htrace : WordTrace (prefixWord ++ tailWord_677316) baseStart_677316 baseEnd_677316 := by
    simpa [prefixWord, tailWord_677316, baseEnd_677316] using wordTrace_append hprefix tailTrace_677316
  have hstable : (prefixWord ++ tailWord_677316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677316).length < 2 ^ (prefixWord ++ tailWord_677316).sum := by decide
  have hdescent : baseEnd_677316 < baseStart_677316 := by decide
  rcases family_descends (prefixWord ++ tailWord_677316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677333 : List Nat := [1, 3, 2, 3, 1, 1, 4, 3, 1, 3]
def baseStart_677333 : Nat := 118140960795 + 677333 * 2 ^ 59
def prefixEnd_677333 : Nat := 4983230072969 + 3 ^ 40 * 677333 * 2
def baseEnd_677333 : Nat := 231864928101269110148339

theorem tailTrace_677333 : CollatzResearch.WordTrace tailWord_677333 prefixEnd_677333 231864928101269110148339 := by
  unfold tailWord_677333
  simp only [CollatzResearch.WordTrace]
  refine ⟨24704364055145695111812653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16469576036763796741208435 24704364055145695111812653)
  ·
    refine ⟨9264136520679635666929745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24704364055145695111812653 9264136520679635666929745)
    ·
      refine ⟨6948102390509726750197309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9264136520679635666929745 6948102390509726750197309)
      ·
        refine ⟨2605538396441147531323991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6948102390509726750197309 2605538396441147531323991)
        ·
          refine ⟨3908307594661721296985987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2605538396441147531323991 3908307594661721296985987)
          ·
            refine ⟨5862461391992581945478981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3908307594661721296985987 5862461391992581945478981)
            ·
              refine ⟨1099211510998609114777309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5862461391992581945478981 1099211510998609114777309)
              ·
                refine ⟨412204316624478418041491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1099211510998609114777309 412204316624478418041491)
                ·
                  refine ⟨618306474936717627062237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 412204316624478418041491 618306474936717627062237)
                  ·
                    refine ⟨231864928101269110148339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 618306474936717627062237 231864928101269110148339)
                    ·
                      rfl

theorem cell22_677333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_677333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_677333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_677333 prefixEnd_677333 := by exact prefixLift 677333
  have htrace : WordTrace (prefixWord ++ tailWord_677333) baseStart_677333 baseEnd_677333 := by
    simpa [prefixWord, tailWord_677333, baseEnd_677333] using wordTrace_append hprefix tailTrace_677333
  have hstable : (prefixWord ++ tailWord_677333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677333).length < 2 ^ (prefixWord ++ tailWord_677333).sum := by decide
  have hdescent : baseEnd_677333 < baseStart_677333 := by decide
  rcases family_descends (prefixWord ++ tailWord_677333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677479 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 1, 7]
def baseStart_677479 : Nat := 118140960795 + 677479 * 2 ^ 59
def prefixEnd_677479 : Nat := 4983230072969 + 3 ^ 40 * 677479 * 2
def baseEnd_677479 : Nat := 231914906884973395997891

theorem tailTrace_677479 : CollatzResearch.WordTrace tailWord_677479 prefixEnd_677479 231914906884973395997891 := by
  unfold tailWord_677479
  simp only [CollatzResearch.WordTrace]
  refine ⟨24709689112616762046627491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16473126075077841364418327 24709689112616762046627491)
  ·
    refine ⟨37064533668925143069941237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24709689112616762046627491 37064533668925143069941237)
    ·
      refine ⟨3474800031461732162806991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37064533668925143069941237 3474800031461732162806991)
      ·
        refine ⟨5212200047192598244210487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3474800031461732162806991 5212200047192598244210487)
        ·
          refine ⟨7818300070788897366315731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5212200047192598244210487 7818300070788897366315731)
          ·
            refine ⟨11727450106183346049473597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7818300070788897366315731 11727450106183346049473597)
            ·
              refine ⟨4397793789818754768552599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11727450106183346049473597 4397793789818754768552599)
              ·
                refine ⟨6596690684728132152828899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4397793789818754768552599 6596690684728132152828899)
                ·
                  refine ⟨9895036027092198229243349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6596690684728132152828899 9895036027092198229243349)
                  ·
                    refine ⟨231914906884973395997891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9895036027092198229243349 231914906884973395997891)
                    ·
                      rfl

theorem cell22_677479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_677479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_677479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_677479 prefixEnd_677479 := by exact prefixLift 677479
  have htrace : WordTrace (prefixWord ++ tailWord_677479) baseStart_677479 baseEnd_677479 := by
    simpa [prefixWord, tailWord_677479, baseEnd_677479] using wordTrace_append hprefix tailTrace_677479
  have hstable : (prefixWord ++ tailWord_677479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677479).length < 2 ^ (prefixWord ++ tailWord_677479).sum := by decide
  have hdescent : baseEnd_677479 < baseStart_677479 := by decide
  rcases family_descends (prefixWord ++ tailWord_677479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677509 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 8]
def baseStart_677509 : Nat := 118140960795 + 677509 * 2 ^ 59
def prefixEnd_677509 : Nat := 4983230072969 + 3 ^ 40 * 677509 * 2
def baseEnd_677509 : Nat := 77308392166021105915933

theorem tailTrace_677509 : CollatzResearch.WordTrace tailWord_677509 prefixEnd_677509 77308392166021105915933 := by
  unfold tailWord_677509
  simp only [CollatzResearch.WordTrace]
  refine ⟨24710783302508077170219581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16473855535005384780146387 24710783302508077170219581)
  ·
    refine ⟨9266543738440528938832343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24710783302508077170219581 9266543738440528938832343)
    ·
      refine ⟨13899815607660793408248515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9266543738440528938832343 13899815607660793408248515)
      ·
        refine ⟨20849723411491190112372773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13899815607660793408248515 20849723411491190112372773)
        ·
          refine ⟨3909323139654598146069895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20849723411491190112372773 3909323139654598146069895)
          ·
            refine ⟨5863984709481897219104843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3909323139654598146069895 5863984709481897219104843)
            ·
              refine ⟨8795977064222845828657265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5863984709481897219104843 8795977064222845828657265)
              ·
                refine ⟨6596982798167134371492949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8795977064222845828657265 6596982798167134371492949)
                ·
                  refine ⟨77308392166021105915933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6596982798167134371492949 77308392166021105915933)
                  ·
                    rfl

theorem cell22_677509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 8].length) (baseStart_677509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_677509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_677509 prefixEnd_677509 := by exact prefixLift 677509
  have htrace : WordTrace (prefixWord ++ tailWord_677509) baseStart_677509 baseEnd_677509 := by
    simpa [prefixWord, tailWord_677509, baseEnd_677509] using wordTrace_append hprefix tailTrace_677509
  have hstable : (prefixWord ++ tailWord_677509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677509).length < 2 ^ (prefixWord ++ tailWord_677509).sum := by decide
  have hdescent : baseEnd_677509 < baseStart_677509 := by decide
  rcases family_descends (prefixWord ++ tailWord_677509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677539 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 3, 6]
def baseStart_677539 : Nat := 118140960795 + 677539 * 2 ^ 59
def prefixEnd_677539 : Nat := 4983230072969 + 3 ^ 40 * 677539 * 2
def baseEnd_677539 : Nat := 231935446111153239497707

theorem tailTrace_677539 : CollatzResearch.WordTrace tailWord_677539 prefixEnd_677539 231935446111153239497707 := by
  unfold tailWord_677539
  simp only [CollatzResearch.WordTrace]
  refine ⟨24711877492399392293811671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16474584994932928195874447 24711877492399392293811671)
  ·
    refine ⟨37067816238599088440717507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24711877492399392293811671 37067816238599088440717507)
    ·
      refine ⟨55601724357898632661076261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37067816238599088440717507 55601724357898632661076261)
      ·
        refine ⟨10425323317105993623951799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55601724357898632661076261 10425323317105993623951799)
        ·
          refine ⟨15637984975658990435927699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10425323317105993623951799 15637984975658990435927699)
          ·
            refine ⟨23456977463488485653891549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15637984975658990435927699 23456977463488485653891549)
            ·
              refine ⟨8796366548808182120209331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23456977463488485653891549 8796366548808182120209331)
              ·
                refine ⟨13194549823212273180313997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8796366548808182120209331 13194549823212273180313997)
                ·
                  refine ⟨4947956183704602442617749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13194549823212273180313997 4947956183704602442617749)
                  ·
                    refine ⟨231935446111153239497707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4947956183704602442617749 231935446111153239497707)
                    ·
                      rfl

theorem cell22_677539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 6].length) (baseStart_677539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_677539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_677539 prefixEnd_677539 := by exact prefixLift 677539
  have htrace : WordTrace (prefixWord ++ tailWord_677539) baseStart_677539 baseEnd_677539 := by
    simpa [prefixWord, tailWord_677539, baseEnd_677539] using wordTrace_append hprefix tailTrace_677539
  have hstable : (prefixWord ++ tailWord_677539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677539).length < 2 ^ (prefixWord ++ tailWord_677539).sum := by decide
  have hdescent : baseEnd_677539 < baseStart_677539 := by decide
  rcases family_descends (prefixWord ++ tailWord_677539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677541 : List Nat := [1, 3, 1, 2, 1, 2, 5, 1, 1, 5]
def baseStart_677541 : Nat := 118140960795 + 677541 * 2 ^ 59
def prefixEnd_677541 : Nat := 4983230072969 + 3 ^ 40 * 677541 * 2
def baseEnd_677541 : Nat := 231936130752025900947701

theorem tailTrace_677541 : CollatzResearch.WordTrace tailWord_677541 prefixEnd_677541 231936130752025900947701 := by
  unfold tailWord_677541
  simp only [CollatzResearch.WordTrace]
  refine ⟨24711950438392146635384477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16474633625594764423589651 24711950438392146635384477)
  ·
    refine ⟨9266981414397054988269179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24711950438392146635384477 9266981414397054988269179)
    ·
      refine ⟨13900472121595582482403769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9266981414397054988269179 13900472121595582482403769)
      ·
        refine ⟨10425354091196686861802827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13900472121595582482403769 10425354091196686861802827)
        ·
          refine ⟨15638031136795030292704241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10425354091196686861802827 15638031136795030292704241)
          ·
            refine ⟨11728523352596272719528181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15638031136795030292704241 11728523352596272719528181)
            ·
              refine ⟨1099549064305900567455767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11728523352596272719528181 1099549064305900567455767)
              ·
                refine ⟨1649323596458850851183651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1099549064305900567455767 1649323596458850851183651)
                ·
                  refine ⟨2473985394688276276775477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1649323596458850851183651 2473985394688276276775477)
                  ·
                    refine ⟨231936130752025900947701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2473985394688276276775477 231936130752025900947701)
                    ·
                      rfl

theorem cell22_677541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_677541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_677541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_677541 prefixEnd_677541 := by exact prefixLift 677541
  have htrace : WordTrace (prefixWord ++ tailWord_677541) baseStart_677541 baseEnd_677541 := by
    simpa [prefixWord, tailWord_677541, baseEnd_677541] using wordTrace_append hprefix tailTrace_677541
  have hstable : (prefixWord ++ tailWord_677541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677541).length < 2 ^ (prefixWord ++ tailWord_677541).sum := by decide
  have hdescent : baseEnd_677541 < baseStart_677541 := by decide
  rcases family_descends (prefixWord ++ tailWord_677541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677588 : List Nat := [2, 4, 1, 3, 1, 2, 2, 7]
def baseStart_677588 : Nat := 118140960795 + 677588 * 2 ^ 59
def prefixEnd_677588 : Nat := 4983230072969 + 3 ^ 40 * 677588 * 2
def baseEnd_677588 : Nat := 25772468868059271669173

theorem tailTrace_677588 : CollatzResearch.WordTrace tailWord_677588 prefixEnd_677588 25772468868059271669173 := by
  unfold tailWord_677588
  simp only [CollatzResearch.WordTrace]
  refine ⟨12356832334610936831172709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16475776446147915774896945 12356832334610936831172709)
  ·
    refine ⟨2316906062739550655844883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12356832334610936831172709 2316906062739550655844883)
    ·
      refine ⟨3475359094109325983767325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2316906062739550655844883 3475359094109325983767325)
      ·
        refine ⟨1303259660290997243912747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3475359094109325983767325 1303259660290997243912747)
        ·
          refine ⟨1954889490436495865869121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1303259660290997243912747 1954889490436495865869121)
          ·
            refine ⟨1466167117827371899401841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1954889490436495865869121 1466167117827371899401841)
            ·
              refine ⟨1099625338370528924551381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1466167117827371899401841 1099625338370528924551381)
              ·
                refine ⟨25772468868059271669173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1099625338370528924551381 25772468868059271669173)
                ·
                  rfl

theorem cell22_677588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 7].length) (baseStart_677588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_677588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_677588 prefixEnd_677588 := by exact prefixLift 677588
  have htrace : WordTrace (prefixWord ++ tailWord_677588) baseStart_677588 baseEnd_677588 := by
    simpa [prefixWord, tailWord_677588, baseEnd_677588] using wordTrace_append hprefix tailTrace_677588
  have hstable : (prefixWord ++ tailWord_677588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677588).length < 2 ^ (prefixWord ++ tailWord_677588).sum := by decide
  have hdescent : baseEnd_677588 < baseStart_677588 := by decide
  rcases family_descends (prefixWord ++ tailWord_677588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677650 : List Nat := [3, 2, 4, 1, 1, 1, 2, 3, 5]
def baseStart_677650 : Nat := 118140960795 + 677650 * 2 ^ 59
def prefixEnd_677650 : Nat := 4983230072969 + 3 ^ 40 * 677650 * 2
def baseEnd_677650 : Nat := 77324481226528649990789

theorem tailTrace_677650 : CollatzResearch.WordTrace tailWord_677650 prefixEnd_677650 77324481226528649990789 := by
  unfold tailWord_677650
  simp only [CollatzResearch.WordTrace]
  refine ⟨6178981498749314562775601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16477283996664838834068269 6178981498749314562775601)
  ·
    refine ⟨4634236124061985922081701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6178981498749314562775601 4634236124061985922081701)
    ·
      refine ⟨868919273261622360390319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4634236124061985922081701 868919273261622360390319)
      ·
        refine ⟨1303378909892433540585479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 868919273261622360390319 1303378909892433540585479)
        ·
          refine ⟨1955068364838650310878219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1303378909892433540585479 1955068364838650310878219)
          ·
            refine ⟨2932602547257975466317329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1955068364838650310878219 2932602547257975466317329)
            ·
              refine ⟨2199451910443481599737997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2932602547257975466317329 2199451910443481599737997)
              ·
                refine ⟨824794466416305599901749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2199451910443481599737997 824794466416305599901749)
                ·
                  refine ⟨77324481226528649990789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 824794466416305599901749 77324481226528649990789)
                  ·
                    rfl

theorem cell22_677650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_677650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_677650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_677650 prefixEnd_677650 := by exact prefixLift 677650
  have htrace : WordTrace (prefixWord ++ tailWord_677650) baseStart_677650 baseEnd_677650 := by
    simpa [prefixWord, tailWord_677650, baseEnd_677650] using wordTrace_append hprefix tailTrace_677650
  have hstable : (prefixWord ++ tailWord_677650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677650).length < 2 ^ (prefixWord ++ tailWord_677650).sum := by decide
  have hdescent : baseEnd_677650 < baseStart_677650 := by decide
  rcases family_descends (prefixWord ++ tailWord_677650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677663 : List Nat := [1, 1, 2, 4, 2, 1, 2, 4, 1, 4]
def baseStart_677663 : Nat := 118140960795 + 677663 * 2 ^ 59
def prefixEnd_677663 : Nat := 4983230072969 + 3 ^ 40 * 677663 * 2
def baseEnd_677663 : Nat := 231977893845258249397327

theorem tailTrace_677663 : CollatzResearch.WordTrace tailWord_677663 prefixEnd_677663 231977893845258249397327 := by
  unfold tailWord_677663
  simp only [CollatzResearch.WordTrace]
  refine ⟨24716400143950161471325643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16477600095966774314217095 24716400143950161471325643)
  ·
    refine ⟨37074600215925242206988465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24716400143950161471325643 37074600215925242206988465)
    ·
      refine ⟨27805950161943931655241349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37074600215925242206988465 27805950161943931655241349)
      ·
        refine ⟨5213615655364487185357753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27805950161943931655241349 5213615655364487185357753)
        ·
          refine ⟨3910211741523365389018315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5213615655364487185357753 3910211741523365389018315)
          ·
            refine ⟨5865317612285048083527473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3910211741523365389018315 5865317612285048083527473)
            ·
              refine ⟨4398988209213786062645605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5865317612285048083527473 4398988209213786062645605)
              ·
                refine ⟨824810289227584886746051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4398988209213786062645605 824810289227584886746051)
                ·
                  refine ⟨1237215433841377330119077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 824810289227584886746051 1237215433841377330119077)
                  ·
                    refine ⟨231977893845258249397327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1237215433841377330119077 231977893845258249397327)
                    ·
                      rfl

theorem cell22_677663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 4].length) (baseStart_677663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_677663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_677663 prefixEnd_677663 := by exact prefixLift 677663
  have htrace : WordTrace (prefixWord ++ tailWord_677663) baseStart_677663 baseEnd_677663 := by
    simpa [prefixWord, tailWord_677663, baseEnd_677663] using wordTrace_append hprefix tailTrace_677663
  have hstable : (prefixWord ++ tailWord_677663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677663).length < 2 ^ (prefixWord ++ tailWord_677663).sum := by decide
  have hdescent : baseEnd_677663 < baseStart_677663 := by decide
  rcases family_descends (prefixWord ++ tailWord_677663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677706 : List Nat := [3, 1, 2, 1, 1, 1, 4, 9]
def baseStart_677706 : Nat := 118140960795 + 677706 * 2 ^ 59
def prefixEnd_677706 : Nat := 4983230072969 + 3 ^ 40 * 677706 * 2
def baseEnd_677706 : Nat := 25776957069335607841355

theorem tailTrace_677706 : CollatzResearch.WordTrace tailWord_677706 prefixEnd_677706 25776957069335607841355 := by
  unfold tailWord_677706
  simp only [CollatzResearch.WordTrace]
  refine ⟨6179492120698594953785243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16478645655196253210093981 6179492120698594953785243)
  ·
    refine ⟨9269238181047892430677865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6179492120698594953785243 9269238181047892430677865)
    ·
      refine ⟨6951928635785919323008399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9269238181047892430677865 6951928635785919323008399)
      ·
        refine ⟨10427892953678878984512599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6951928635785919323008399 10427892953678878984512599)
        ·
          refine ⟨15641839430518318476768899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10427892953678878984512599 15641839430518318476768899)
          ·
            refine ⟨23462759145777477715153349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15641839430518318476768899 23462759145777477715153349)
            ·
              refine ⟨4399267339833277071591253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23462759145777477715153349 4399267339833277071591253)
              ·
                refine ⟨25776957069335607841355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4399267339833277071591253 25776957069335607841355)
                ·
                  rfl

theorem cell22_677706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 9].length) (baseStart_677706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_677706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_677706 prefixEnd_677706 := by exact prefixLift 677706
  have htrace : WordTrace (prefixWord ++ tailWord_677706) baseStart_677706 baseEnd_677706 := by
    simpa [prefixWord, tailWord_677706, baseEnd_677706] using wordTrace_append hprefix tailTrace_677706
  have hstable : (prefixWord ++ tailWord_677706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677706).length < 2 ^ (prefixWord ++ tailWord_677706).sum := by decide
  have hdescent : baseEnd_677706 < baseStart_677706 := by decide
  rcases family_descends (prefixWord ++ tailWord_677706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677721 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 2, 7]
def baseStart_677721 : Nat := 118140960795 + 677721 * 2 ^ 59
def prefixEnd_677721 : Nat := 4983230072969 + 3 ^ 40 * 677721 * 2
def baseEnd_677721 : Nat := 231997748430565431447149

theorem tailTrace_677721 : CollatzResearch.WordTrace tailWord_677721 prefixEnd_677721 231997748430565431447149 := by
  unfold tailWord_677721
  simp only [CollatzResearch.WordTrace]
  refine ⟨24718515577740037376937017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16479010385160024917958011 24718515577740037376937017)
  ·
    refine ⟨18538886683305028032702763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24718515577740037376937017 18538886683305028032702763)
    ·
      refine ⟨27808330024957542049054145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18538886683305028032702763 27808330024957542049054145)
      ·
        refine ⟨20856247518718156536790609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27808330024957542049054145 20856247518718156536790609)
        ·
          refine ⟨15642185639038617402592957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20856247518718156536790609 15642185639038617402592957)
          ·
            refine ⟨5865819614639481525972359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15642185639038617402592957 5865819614639481525972359)
            ·
              refine ⟨8798729421959222288958539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5865819614639481525972359 8798729421959222288958539)
              ·
                refine ⟨13198094132938833433437809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8798729421959222288958539 13198094132938833433437809)
                ·
                  refine ⟨9898570599704125075078357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13198094132938833433437809 9898570599704125075078357)
                  ·
                    refine ⟨231997748430565431447149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9898570599704125075078357 231997748430565431447149)
                    ·
                      rfl

theorem cell22_677721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 7].length) (baseStart_677721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_677721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_677721 prefixEnd_677721 := by exact prefixLift 677721
  have htrace : WordTrace (prefixWord ++ tailWord_677721) baseStart_677721 baseEnd_677721 := by
    simpa [prefixWord, tailWord_677721, baseEnd_677721] using wordTrace_append hprefix tailTrace_677721
  have hstable : (prefixWord ++ tailWord_677721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677721).length < 2 ^ (prefixWord ++ tailWord_677721).sum := by decide
  have hdescent : baseEnd_677721 < baseStart_677721 := by decide
  rcases family_descends (prefixWord ++ tailWord_677721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677761 : List Nat := [1, 2, 4, 4, 1, 2, 2, 1, 2, 3]
def baseStart_677761 : Nat := 118140960795 + 677761 * 2 ^ 59
def prefixEnd_677761 : Nat := 4983230072969 + 3 ^ 40 * 677761 * 2
def baseEnd_677761 : Nat := 232011441248018660447027

theorem tailTrace_677761 : CollatzResearch.WordTrace tailWord_677761 prefixEnd_677761 232011441248018660447027 := by
  unfold tailWord_677761
  simp only [CollatzResearch.WordTrace]
  refine ⟨24719974497595124208393137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16479982998396749472262091 24719974497595124208393137)
  ·
    refine ⟨18539980873196343156294853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24719974497595124208393137 18539980873196343156294853)
    ·
      refine ⟨3476246413724314341805285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18539980873196343156294853 3476246413724314341805285)
      ·
        refine ⟨651796202573308939088491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3476246413724314341805285 651796202573308939088491)
        ·
          refine ⟨977694303859963408632737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 651796202573308939088491 977694303859963408632737)
          ·
            refine ⟨733270727894972556474553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 977694303859963408632737 733270727894972556474553)
            ·
              refine ⟨549953045921229417355915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 733270727894972556474553 549953045921229417355915)
              ·
                refine ⟨824929568881844126033873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 549953045921229417355915 824929568881844126033873)
                ·
                  refine ⟨618697176661383094525405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 824929568881844126033873 618697176661383094525405)
                  ·
                    refine ⟨232011441248018660447027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 618697176661383094525405 232011441248018660447027)
                    ·
                      rfl

theorem cell22_677761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_677761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_677761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_677761 prefixEnd_677761 := by exact prefixLift 677761
  have htrace : WordTrace (prefixWord ++ tailWord_677761) baseStart_677761 baseEnd_677761 := by
    simpa [prefixWord, tailWord_677761, baseEnd_677761] using wordTrace_append hprefix tailTrace_677761
  have hstable : (prefixWord ++ tailWord_677761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677761).length < 2 ^ (prefixWord ++ tailWord_677761).sum := by decide
  have hdescent : baseEnd_677761 < baseStart_677761 := by decide
  rcases family_descends (prefixWord ++ tailWord_677761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677845 : List Nat := [1, 3, 2, 3, 2, 1, 2, 2, 1, 5]
def baseStart_677845 : Nat := 118140960795 + 677845 * 2 ^ 59
def prefixEnd_677845 : Nat := 4983230072969 + 3 ^ 40 * 677845 * 2
def baseEnd_677845 : Nat := 232040196164670441346769

theorem tailTrace_677845 : CollatzResearch.WordTrace tailWord_677845 prefixEnd_677845 232040196164670441346769 := by
  unfold tailWord_677845
  simp only [CollatzResearch.WordTrace]
  refine ⟨24723038229290806554450989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16482025486193871036300659 24723038229290806554450989)
  ·
    refine ⟨9271139335984052457919121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24723038229290806554450989 9271139335984052457919121)
    ·
      refine ⟨6953354501988039343439341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9271139335984052457919121 6953354501988039343439341)
      ·
        refine ⟨2607507938245514753789753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6953354501988039343439341 2607507938245514753789753)
        ·
          refine ⟨1955630953684136065342315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2607507938245514753789753 1955630953684136065342315)
          ·
            refine ⟨2933446430526204098013473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1955630953684136065342315 2933446430526204098013473)
            ·
              refine ⟨2200084822894653073510105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2933446430526204098013473 2200084822894653073510105)
              ·
                refine ⟨1650063617170989805132579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2200084822894653073510105 1650063617170989805132579)
                ·
                  refine ⟨2475095425756484707698869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1650063617170989805132579 2475095425756484707698869)
                  ·
                    refine ⟨232040196164670441346769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2475095425756484707698869 232040196164670441346769)
                    ·
                      rfl

theorem cell22_677845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_677845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_677845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_677845 prefixEnd_677845 := by exact prefixLift 677845
  have htrace : WordTrace (prefixWord ++ tailWord_677845) baseStart_677845 baseEnd_677845 := by
    simpa [prefixWord, tailWord_677845, baseEnd_677845] using wordTrace_append hprefix tailTrace_677845
  have hstable : (prefixWord ++ tailWord_677845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677845).length < 2 ^ (prefixWord ++ tailWord_677845).sum := by decide
  have hdescent : baseEnd_677845 < baseStart_677845 := by decide
  rcases family_descends (prefixWord ++ tailWord_677845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677849 : List Nat := [1, 2, 1, 2, 6, 2, 2, 1, 1, 4]
def baseStart_677849 : Nat := 118140960795 + 677849 * 2 ^ 59
def prefixEnd_677849 : Nat := 4983230072969 + 3 ^ 40 * 677849 * 2
def baseEnd_677849 : Nat := 232041565446415764246757

theorem tailTrace_677849 : CollatzResearch.WordTrace tailWord_677849 prefixEnd_677849 232041565446415764246757 := by
  unfold tailWord_677849
  simp only [CollatzResearch.WordTrace]
  refine ⟨24723184121276315237596601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16482122747517543491731067 24723184121276315237596601)
  ·
    refine ⟨18542388090957236428197451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24723184121276315237596601 18542388090957236428197451)
    ·
      refine ⟨27813582136435854642296177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18542388090957236428197451 27813582136435854642296177)
      ·
        refine ⟨20860186602326890981722133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27813582136435854642296177 20860186602326890981722133)
        ·
          refine ⟨977821246984073014768225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20860186602326890981722133 977821246984073014768225)
          ·
            refine ⟨733365935238054761076169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 977821246984073014768225 733365935238054761076169)
            ·
              refine ⟨550024451428541070807127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 733365935238054761076169 550024451428541070807127)
              ·
                refine ⟨825036677142811606210691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 550024451428541070807127 825036677142811606210691)
                ·
                  refine ⟨1237555015714217409316037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 825036677142811606210691 1237555015714217409316037)
                  ·
                    refine ⟨232041565446415764246757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1237555015714217409316037 232041565446415764246757)
                    ·
                      rfl

theorem cell22_677849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 1, 4].length) (baseStart_677849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_677849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_677849 prefixEnd_677849 := by exact prefixLift 677849
  have htrace : WordTrace (prefixWord ++ tailWord_677849) baseStart_677849 baseEnd_677849 := by
    simpa [prefixWord, tailWord_677849, baseEnd_677849] using wordTrace_append hprefix tailTrace_677849
  have hstable : (prefixWord ++ tailWord_677849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677849).length < 2 ^ (prefixWord ++ tailWord_677849).sum := by decide
  have hdescent : baseEnd_677849 < baseStart_677849 := by decide
  rcases family_descends (prefixWord ++ tailWord_677849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677892 : List Nat := [2, 3, 2, 4, 1, 1, 1, 8]
def baseStart_677892 : Nat := 118140960795 + 677892 * 2 ^ 59
def prefixEnd_677892 : Nat := 4983230072969 + 3 ^ 40 * 677892 * 2
def baseEnd_677892 : Nat := 25784031691686442824625

theorem tailTrace_677892 : CollatzResearch.WordTrace tailWord_677892 prefixEnd_677892 25784031691686442824625 := by
  unfold tailWord_677892
  simp only [CollatzResearch.WordTrace]
  refine ⟨12362376230060266790705965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16483168306747022387607953 12362376230060266790705965)
  ·
    refine ⟨4635891086272600046514737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12362376230060266790705965 4635891086272600046514737)
    ·
      refine ⟨3476918314704450034886053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4635891086272600046514737 3476918314704450034886053)
      ·
        refine ⟨651922184007084381541135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3476918314704450034886053 651922184007084381541135)
        ·
          refine ⟨977883276010626572311703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 651922184007084381541135 977883276010626572311703)
          ·
            refine ⟨1466824914015939858467555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 977883276010626572311703 1466824914015939858467555)
            ·
              refine ⟨2200237371023909787701333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1466824914015939858467555 2200237371023909787701333)
              ·
                refine ⟨25784031691686442824625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2200237371023909787701333 25784031691686442824625)
                ·
                  rfl

theorem cell22_677892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 8].length) (baseStart_677892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_677892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_677892 prefixEnd_677892 := by exact prefixLift 677892
  have htrace : WordTrace (prefixWord ++ tailWord_677892) baseStart_677892 baseEnd_677892 := by
    simpa [prefixWord, tailWord_677892, baseEnd_677892] using wordTrace_append hprefix tailTrace_677892
  have hstable : (prefixWord ++ tailWord_677892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677892).length < 2 ^ (prefixWord ++ tailWord_677892).sum := by decide
  have hdescent : baseEnd_677892 < baseStart_677892 := by decide
  rcases family_descends (prefixWord ++ tailWord_677892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677937 : List Nat := [1, 2, 2, 3, 1, 3, 4, 1, 5]
def baseStart_677937 : Nat := 118140960795 + 677937 * 2 ^ 59
def prefixEnd_677937 : Nat := 4983230072969 + 3 ^ 40 * 677937 * 2
def baseEnd_677937 : Nat := 77357229881604289348829

theorem tailTrace_677937 : CollatzResearch.WordTrace tailWord_677937 prefixEnd_677937 77357229881604289348829 := by
  unfold tailWord_677937
  simp only [CollatzResearch.WordTrace]
  refine ⟨24726393744957506266800065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16484262496638337511200043 24726393744957506266800065)
  ·
    refine ⟨18544795308718129700100049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24726393744957506266800065 18544795308718129700100049)
    ·
      refine ⟨13908596481538597275075037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18544795308718129700100049 13908596481538597275075037)
      ·
        refine ⟨5215723680576973978153139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13908596481538597275075037 5215723680576973978153139)
        ·
          refine ⟨7823585520865460967229709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5215723680576973978153139 7823585520865460967229709)
          ·
            refine ⟨2933844570324547862711141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7823585520865460967229709 2933844570324547862711141)
            ·
              refine ⟨550095856935852724258339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2933844570324547862711141 550095856935852724258339)
              ·
                refine ⟨825143785403779086387509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 550095856935852724258339 825143785403779086387509)
                ·
                  refine ⟨77357229881604289348829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 825143785403779086387509 77357229881604289348829)
                  ·
                    rfl

theorem cell22_677937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 5].length) (baseStart_677937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_677937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_677937 prefixEnd_677937 := by exact prefixLift 677937
  have htrace : WordTrace (prefixWord ++ tailWord_677937) baseStart_677937 baseEnd_677937 := by
    simpa [prefixWord, tailWord_677937, baseEnd_677937] using wordTrace_append hprefix tailTrace_677937
  have hstable : (prefixWord ++ tailWord_677937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677937).length < 2 ^ (prefixWord ++ tailWord_677937).sum := by decide
  have hdescent : baseEnd_677937 < baseStart_677937 := by decide
  rcases family_descends (prefixWord ++ tailWord_677937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677997 : List Nat := [1, 5, 1, 1, 2, 1, 4, 1, 1, 5]
def baseStart_677997 : Nat := 118140960795 + 677997 * 2 ^ 59
def prefixEnd_677997 : Nat := 4983230072969 + 3 ^ 40 * 677997 * 2
def baseEnd_677997 : Nat := 232092228870992711546303

theorem tailTrace_677997 : CollatzResearch.WordTrace tailWord_677997 prefixEnd_677997 232092228870992711546303 := by
  unfold tailWord_677997
  simp only [CollatzResearch.WordTrace]
  refine ⟨24728582124740136513984245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16485721416493424342656163 24728582124740136513984245)
  ·
    refine ⟨2318304574194387798186023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24728582124740136513984245 2318304574194387798186023)
    ·
      refine ⟨3477456861291581697279035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2318304574194387798186023 3477456861291581697279035)
      ·
        refine ⟨5216185291937372545918553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3477456861291581697279035 5216185291937372545918553)
        ·
          refine ⟨3912138968953029409438915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5216185291937372545918553 3912138968953029409438915)
          ·
            refine ⟨5868208453429544114158373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3912138968953029409438915 5868208453429544114158373)
            ·
              refine ⟨1100289085018039521404695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5868208453429544114158373 1100289085018039521404695)
              ·
                refine ⟨1650433627527059282107043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1100289085018039521404695 1650433627527059282107043)
                ·
                  refine ⟨2475650441290588923160565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1650433627527059282107043 2475650441290588923160565)
                  ·
                    refine ⟨232092228870992711546303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2475650441290588923160565 232092228870992711546303)
                    ·
                      rfl

theorem cell22_677997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_677997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_677997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_677997 prefixEnd_677997 := by exact prefixLift 677997
  have htrace : WordTrace (prefixWord ++ tailWord_677997) baseStart_677997 baseEnd_677997 := by
    simpa [prefixWord, tailWord_677997, baseEnd_677997] using wordTrace_append hprefix tailTrace_677997
  have hstable : (prefixWord ++ tailWord_677997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677997).length < 2 ^ (prefixWord ++ tailWord_677997).sum := by decide
  have hdescent : baseEnd_677997 < baseStart_677997 := by decide
  rcases family_descends (prefixWord ++ tailWord_677997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678012 : List Nat := [2, 2, 2, 1, 1, 4, 3, 1, 2, 4]
def baseStart_678012 : Nat := 118140960795 + 678012 * 2 ^ 59
def prefixEnd_678012 : Nat := 4983230072969 + 3 ^ 40 * 678012 * 2
def baseEnd_678012 : Nat := 232097363677537672421257

theorem tailTrace_678012 : CollatzResearch.WordTrace tailWord_678012 prefixEnd_678012 232097363677537672421257 := by
  unfold tailWord_678012
  simp only [CollatzResearch.WordTrace]
  refine ⟨12364564609842897037890145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16486086146457196050520193 12364564609842897037890145)
  ·
    refine ⟨9273423457382172778417609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12364564609842897037890145 9273423457382172778417609)
    ·
      refine ⟨6955067593036629583813207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9273423457382172778417609 6955067593036629583813207)
      ·
        refine ⟨10432601389554944375719811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6955067593036629583813207 10432601389554944375719811)
        ·
          refine ⟨15648902084332416563579717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10432601389554944375719811 15648902084332416563579717)
          ·
            refine ⟨2934169140812328105671197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15648902084332416563579717 2934169140812328105671197)
            ·
              refine ⟨1100313427804623039626699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2934169140812328105671197 1100313427804623039626699)
              ·
                refine ⟨1650470141706934559440049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1100313427804623039626699 1650470141706934559440049)
                ·
                  refine ⟨1237852606280200919580037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1650470141706934559440049 1237852606280200919580037)
                  ·
                    refine ⟨232097363677537672421257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1237852606280200919580037 232097363677537672421257)
                    ·
                      rfl

theorem cell22_678012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_678012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678012 prefixEnd_678012 := by exact prefixLift 678012
  have htrace : WordTrace (prefixWord ++ tailWord_678012) baseStart_678012 baseEnd_678012 := by
    simpa [prefixWord, tailWord_678012, baseEnd_678012] using wordTrace_append hprefix tailTrace_678012
  have hstable : (prefixWord ++ tailWord_678012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678012).length < 2 ^ (prefixWord ++ tailWord_678012).sum := by decide
  have hdescent : baseEnd_678012 < baseStart_678012 := by decide
  rcases family_descends (prefixWord ++ tailWord_678012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678119 : List Nat := [1, 1, 5, 3, 1, 2, 1, 1, 3, 4]
def baseStart_678119 : Nat := 118140960795 + 678119 * 2 ^ 59
def prefixEnd_678119 : Nat := 4983230072969 + 3 ^ 40 * 678119 * 2
def baseEnd_678119 : Nat := 232133991964225059995929

theorem tailTrace_678119 : CollatzResearch.WordTrace tailWord_678119 prefixEnd_678119 232133991964225059995929 := by
  unfold tailWord_678119
  simp only [CollatzResearch.WordTrace]
  refine ⟨24733031830298151349925411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16488687886865434233283607 24733031830298151349925411)
  ·
    refine ⟨37099547745447227024888117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24733031830298151349925411 37099547745447227024888117)
    ·
      refine ⟨3478082601135677533583261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37099547745447227024888117 3478082601135677533583261)
      ·
        refine ⟨1304280975425879075093723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3478082601135677533583261 1304280975425879075093723)
        ·
          refine ⟨1956421463138818612640585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1304280975425879075093723 1956421463138818612640585)
          ·
            refine ⟨1467316097354113959480439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1956421463138818612640585 1467316097354113959480439)
            ·
              refine ⟨2200974146031170939220659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1467316097354113959480439 2200974146031170939220659)
              ·
                refine ⟨3301461219046756408830989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2200974146031170939220659 3301461219046756408830989)
                ·
                  refine ⟨1238047957142533653311621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3301461219046756408830989 1238047957142533653311621)
                  ·
                    refine ⟨232133991964225059995929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1238047957142533653311621 232133991964225059995929)
                    ·
                      rfl

theorem cell22_678119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_678119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678119 prefixEnd_678119 := by exact prefixLift 678119
  have htrace : WordTrace (prefixWord ++ tailWord_678119) baseStart_678119 baseEnd_678119 := by
    simpa [prefixWord, tailWord_678119, baseEnd_678119] using wordTrace_append hprefix tailTrace_678119
  have hstable : (prefixWord ++ tailWord_678119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678119).length < 2 ^ (prefixWord ++ tailWord_678119).sum := by decide
  have hdescent : baseEnd_678119 < baseStart_678119 := by decide
  rcases family_descends (prefixWord ++ tailWord_678119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678147 : List Nat := [1, 1, 1, 3, 2, 3, 1, 4, 2, 4]
def baseStart_678147 : Nat := 118140960795 + 678147 * 2 ^ 59
def prefixEnd_678147 : Nat := 4983230072969 + 3 ^ 40 * 678147 * 2
def baseEnd_678147 : Nat := 232143576936442320295843

theorem tailTrace_678147 : CollatzResearch.WordTrace tailWord_678147 prefixEnd_678147 232143576936442320295843 := by
  unfold tailWord_678147
  simp only [CollatzResearch.WordTrace]
  refine ⟨24734053074196712131944695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16489368716131141421296463 24734053074196712131944695)
  ·
    refine ⟨37101079611295068197917043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24734053074196712131944695 37101079611295068197917043)
    ·
      refine ⟨55651619416942602296875565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37101079611295068197917043 55651619416942602296875565)
      ·
        refine ⟨20869357281353475861328337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55651619416942602296875565 20869357281353475861328337)
        ·
          refine ⟨15652017961015106895996253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20869357281353475861328337 15652017961015106895996253)
          ·
            refine ⟨5869506735380665085998595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15652017961015106895996253 5869506735380665085998595)
            ·
              refine ⟨8804260103070997628997893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5869506735380665085998595 8804260103070997628997893)
              ·
                refine ⟨1650798769325812055437105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8804260103070997628997893 1650798769325812055437105)
                ·
                  refine ⟨1238099076994359041577829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1650798769325812055437105 1238099076994359041577829)
                  ·
                    refine ⟨232143576936442320295843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1238099076994359041577829 232143576936442320295843)
                    ·
                      rfl

theorem cell22_678147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 4].length) (baseStart_678147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678147 prefixEnd_678147 := by exact prefixLift 678147
  have htrace : WordTrace (prefixWord ++ tailWord_678147) baseStart_678147 baseEnd_678147 := by
    simpa [prefixWord, tailWord_678147, baseEnd_678147] using wordTrace_append hprefix tailTrace_678147
  have hstable : (prefixWord ++ tailWord_678147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678147).length < 2 ^ (prefixWord ++ tailWord_678147).sum := by decide
  have hdescent : baseEnd_678147 < baseStart_678147 := by decide
  rcases family_descends (prefixWord ++ tailWord_678147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678181 : List Nat := [1, 3, 1, 2, 5, 2, 1, 1, 2, 4]
def baseStart_678181 : Nat := 118140960795 + 678181 * 2 ^ 59
def prefixEnd_678181 : Nat := 4983230072969 + 3 ^ 40 * 678181 * 2
def baseEnd_678181 : Nat := 232155215831277564945739

theorem tailTrace_678181 : CollatzResearch.WordTrace tailWord_678181 prefixEnd_678181 232155215831277564945739 := by
  unfold tailWord_678181
  simp only [CollatzResearch.WordTrace]
  refine ⟨24735293156073535938682397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16490195437382357292454931 24735293156073535938682397)
  ·
    refine ⟨9275734933527575977005899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24735293156073535938682397 9275734933527575977005899)
    ·
      refine ⟨13913602400291363965508849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9275734933527575977005899 13913602400291363965508849)
      ·
        refine ⟨10435201800218522974131637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13913602400291363965508849 10435201800218522974131637)
        ·
          refine ⟨978300168770486528824841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10435201800218522974131637 978300168770486528824841)
          ·
            refine ⟨733725126577864896618631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 978300168770486528824841 733725126577864896618631)
            ·
              refine ⟨1100587689866797344927947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733725126577864896618631 1100587689866797344927947)
              ·
                refine ⟨1650881534800196017391921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1100587689866797344927947 1650881534800196017391921)
                ·
                  refine ⟨1238161151100147013043941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1650881534800196017391921 1238161151100147013043941)
                  ·
                    refine ⟨232155215831277564945739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1238161151100147013043941 232155215831277564945739)
                    ·
                      rfl

theorem cell22_678181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 4].length) (baseStart_678181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678181 prefixEnd_678181 := by exact prefixLift 678181
  have htrace : WordTrace (prefixWord ++ tailWord_678181) baseStart_678181 baseEnd_678181 := by
    simpa [prefixWord, tailWord_678181, baseEnd_678181] using wordTrace_append hprefix tailTrace_678181
  have hstable : (prefixWord ++ tailWord_678181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678181).length < 2 ^ (prefixWord ++ tailWord_678181).sum := by decide
  have hdescent : baseEnd_678181 < baseStart_678181 := by decide
  rcases family_descends (prefixWord ++ tailWord_678181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678207 : List Nat := [1, 1, 2, 2, 4, 1, 3, 1, 7]
def baseStart_678207 : Nat := 118140960795 + 678207 * 2 ^ 59
def prefixEnd_678207 : Nat := 4983230072969 + 3 ^ 40 * 678207 * 2
def baseEnd_678207 : Nat := 77388038720874054598553

theorem tailTrace_678207 : CollatzResearch.WordTrace tailWord_678207 prefixEnd_678207 77388038720874054598553 := by
  unfold tailWord_678207
  simp only [CollatzResearch.WordTrace]
  refine ⟨24736241453979342379128875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16490827635986228252752583 24736241453979342379128875)
  ·
    refine ⟨37104362180969013568693313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24736241453979342379128875 37104362180969013568693313)
    ·
      refine ⟨27828271635726760176519985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37104362180969013568693313 27828271635726760176519985)
      ·
        refine ⟨20871203726795070132389989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27828271635726760176519985 20871203726795070132389989)
        ·
          refine ⟨3913350698774075649823123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20871203726795070132389989 3913350698774075649823123)
          ·
            refine ⟨5870026048161113474734685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3913350698774075649823123 5870026048161113474734685)
            ·
              refine ⟨2201259768060417553025507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5870026048161113474734685 2201259768060417553025507)
              ·
                refine ⟨3301889652090626329538261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2201259768060417553025507 3301889652090626329538261)
                ·
                  refine ⟨77388038720874054598553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3301889652090626329538261 77388038720874054598553)
                  ·
                    rfl

theorem cell22_678207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 7].length) (baseStart_678207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678207 prefixEnd_678207 := by exact prefixLift 678207
  have htrace : WordTrace (prefixWord ++ tailWord_678207) baseStart_678207 baseEnd_678207 := by
    simpa [prefixWord, tailWord_678207, baseEnd_678207] using wordTrace_append hprefix tailTrace_678207
  have hstable : (prefixWord ++ tailWord_678207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678207).length < 2 ^ (prefixWord ++ tailWord_678207).sum := by decide
  have hdescent : baseEnd_678207 < baseStart_678207 := by decide
  rcases family_descends (prefixWord ++ tailWord_678207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678211 : List Nat := [1, 1, 1, 3, 1, 3, 4, 4, 1, 3]
def baseStart_678211 : Nat := 118140960795 + 678211 * 2 ^ 59
def prefixEnd_678211 : Nat := 4983230072969 + 3 ^ 40 * 678211 * 2
def baseEnd_678211 : Nat := 232165485444367486695647

theorem tailTrace_678211 : CollatzResearch.WordTrace tailWord_678211 prefixEnd_678211 232165485444367486695647 := by
  unfold tailWord_678211
  simp only [CollatzResearch.WordTrace]
  refine ⟨24736387345964851062274487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16490924897309900708182991 24736387345964851062274487)
  ·
    refine ⟨37104581018947276593411731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24736387345964851062274487 37104581018947276593411731)
    ·
      refine ⟨55656871528420914890117597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37104581018947276593411731 55656871528420914890117597)
      ·
        refine ⟨20871326823157843083794099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55656871528420914890117597 20871326823157843083794099)
        ·
          refine ⟨31306990234736764625691149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20871326823157843083794099 31306990234736764625691149)
          ·
            refine ⟨11740121338026286734634181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31306990234736764625691149 11740121338026286734634181)
            ·
              refine ⟨2201272750879928762743909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11740121338026286734634181 2201272750879928762743909)
              ·
                refine ⟨412738640789986643014483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2201272750879928762743909 412738640789986643014483)
                ·
                  refine ⟨619107961184979964521725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 412738640789986643014483 619107961184979964521725)
                  ·
                    refine ⟨232165485444367486695647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 619107961184979964521725 232165485444367486695647)
                    ·
                      rfl

theorem cell22_678211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4, 1, 3].length) (baseStart_678211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678211 prefixEnd_678211 := by exact prefixLift 678211
  have htrace : WordTrace (prefixWord ++ tailWord_678211) baseStart_678211 baseEnd_678211 := by
    simpa [prefixWord, tailWord_678211, baseEnd_678211] using wordTrace_append hprefix tailTrace_678211
  have hstable : (prefixWord ++ tailWord_678211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678211).length < 2 ^ (prefixWord ++ tailWord_678211).sum := by decide
  have hdescent : baseEnd_678211 < baseStart_678211 := by decide
  rcases family_descends (prefixWord ++ tailWord_678211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678222 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 1, 7]
def baseStart_678222 : Nat := 118140960795 + 678222 * 2 ^ 59
def prefixEnd_678222 : Nat := 4983230072969 + 3 ^ 40 * 678222 * 2
def baseEnd_678222 : Nat := 232169250969167124670613

theorem tailTrace_678222 : CollatzResearch.WordTrace tailWord_678222 prefixEnd_678222 232169250969167124670613 := by
  unfold tailWord_678222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3092098568615624992615615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16491192365949999960616613 3092098568615624992615615)
  ·
    refine ⟨4638147852923437488923423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3092098568615624992615615 4638147852923437488923423)
    ·
      refine ⟨6957221779385156233385135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4638147852923437488923423 6957221779385156233385135)
      ·
        refine ⟨10435832669077734350077703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6957221779385156233385135 10435832669077734350077703)
        ·
          refine ⟨15653749003616601525116555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10435832669077734350077703 15653749003616601525116555)
          ·
            refine ⟨23480623505424902287674833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15653749003616601525116555 23480623505424902287674833)
            ·
              refine ⟨17610467629068676715756125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23480623505424902287674833 17610467629068676715756125)
              ·
                refine ⟨6603925360900753768408547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17610467629068676715756125 6603925360900753768408547)
                ·
                  refine ⟨9905888041351130652612821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6603925360900753768408547 9905888041351130652612821)
                  ·
                    refine ⟨232169250969167124670613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9905888041351130652612821 232169250969167124670613)
                    ·
                      rfl

theorem cell22_678222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_678222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678222 prefixEnd_678222 := by exact prefixLift 678222
  have htrace : WordTrace (prefixWord ++ tailWord_678222) baseStart_678222 baseEnd_678222 := by
    simpa [prefixWord, tailWord_678222, baseEnd_678222] using wordTrace_append hprefix tailTrace_678222
  have hstable : (prefixWord ++ tailWord_678222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678222).length < 2 ^ (prefixWord ++ tailWord_678222).sum := by decide
  have hdescent : baseEnd_678222 < baseStart_678222 := by decide
  rcases family_descends (prefixWord ++ tailWord_678222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678262 : List Nat := [5, 1, 1, 4, 2, 1, 1, 1, 3, 3]
def baseStart_678262 : Nat := 118140960795 + 678262 * 2 ^ 59
def prefixEnd_678262 : Nat := 4983230072969 + 3 ^ 40 * 678262 * 2
def baseEnd_678262 : Nat := 232182943786620353670491

theorem tailTrace_678262 : CollatzResearch.WordTrace tailWord_678262 prefixEnd_678262 232182943786620353670491 := by
  unfold tailWord_678262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1546140466798755423273815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16492164979186724514920693 1546140466798755423273815)
  ·
    refine ⟨2319210700198133134910723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1546140466798755423273815 2319210700198133134910723)
    ·
      refine ⟨3478816050297199702366085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2319210700198133134910723 3478816050297199702366085)
      ·
        refine ⟨652278009430724944193641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3478816050297199702366085 652278009430724944193641)
        ·
          refine ⟨489208507073043708145231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 652278009430724944193641 489208507073043708145231)
          ·
            refine ⟨733812760609565562217847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489208507073043708145231 733812760609565562217847)
            ·
              refine ⟨1100719140914348343326771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733812760609565562217847 1100719140914348343326771)
              ·
                refine ⟨1651078711371522514990157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1100719140914348343326771 1651078711371522514990157)
                ·
                  refine ⟨619154516764320943121309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1651078711371522514990157 619154516764320943121309)
                  ·
                    refine ⟨232182943786620353670491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 619154516764320943121309 232182943786620353670491)
                    ·
                      rfl

theorem cell22_678262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_678262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678262 prefixEnd_678262 := by exact prefixLift 678262
  have htrace : WordTrace (prefixWord ++ tailWord_678262) baseStart_678262 baseEnd_678262 := by
    simpa [prefixWord, tailWord_678262, baseEnd_678262] using wordTrace_append hprefix tailTrace_678262
  have hstable : (prefixWord ++ tailWord_678262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678262).length < 2 ^ (prefixWord ++ tailWord_678262).sum := by decide
  have hdescent : baseEnd_678262 < baseStart_678262 := by decide
  rcases family_descends (prefixWord ++ tailWord_678262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678269 : List Nat := [1, 4, 1, 1, 2, 3, 3, 1, 6]
def baseStart_678269 : Nat := 118140960795 + 678269 * 2 ^ 59
def prefixEnd_678269 : Nat := 4983230072969 + 3 ^ 40 * 678269 * 2
def baseEnd_678269 : Nat := 77395113343224889581823

theorem tailTrace_678269 : CollatzResearch.WordTrace tailWord_678269 prefixEnd_678269 77395113343224889581823 := by
  unfold tailWord_678269
  simp only [CollatzResearch.WordTrace]
  refine ⟨24738502779754726967885861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16492335186503151311923907 24738502779754726967885861)
  ·
    refine ⟨4638469271204011306478599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24738502779754726967885861 4638469271204011306478599)
    ·
      refine ⟨6957703906806016959717899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4638469271204011306478599 6957703906806016959717899)
      ·
        refine ⟨10436555860209025439576849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6957703906806016959717899 10436555860209025439576849)
        ·
          refine ⟨7827416895156769079682637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10436555860209025439576849 7827416895156769079682637)
          ·
            refine ⟨2935281335683788404880989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7827416895156769079682637 2935281335683788404880989)
            ·
              refine ⟨1100730500881420651830371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2935281335683788404880989 1100730500881420651830371)
              ·
                refine ⟨1651095751322130977745557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1100730500881420651830371 1651095751322130977745557)
                ·
                  refine ⟨77395113343224889581823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1651095751322130977745557 77395113343224889581823)
                  ·
                    rfl

theorem cell22_678269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_678269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678269 prefixEnd_678269 := by exact prefixLift 678269
  have htrace : WordTrace (prefixWord ++ tailWord_678269) baseStart_678269 baseEnd_678269 := by
    simpa [prefixWord, tailWord_678269, baseEnd_678269] using wordTrace_append hprefix tailTrace_678269
  have hstable : (prefixWord ++ tailWord_678269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678269).length < 2 ^ (prefixWord ++ tailWord_678269).sum := by decide
  have hdescent : baseEnd_678269 < baseStart_678269 := by decide
  rcases family_descends (prefixWord ++ tailWord_678269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678297 : List Nat := [1, 2, 1, 2, 1, 4, 1, 10]
def baseStart_678297 : Nat := 118140960795 + 678297 * 2 ^ 59
def prefixEnd_678297 : Nat := 4983230072969 + 3 ^ 40 * 678297 * 2
def baseEnd_678297 : Nat := 25799436111321325449487

theorem tailTrace_678297 : CollatzResearch.WordTrace tailWord_678297 prefixEnd_678297 25799436111321325449487 := by
  unfold tailWord_678297
  simp only [CollatzResearch.WordTrace]
  refine ⟨24739524023653287749905145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16493016015768858499936763 24739524023653287749905145)
  ·
    refine ⟨18554643017739965812428859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24739524023653287749905145 18554643017739965812428859)
    ·
      refine ⟨27831964526609948718643289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18554643017739965812428859 27831964526609948718643289)
      ·
        refine ⟨20873973394957461538982467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27831964526609948718643289 20873973394957461538982467)
        ·
          refine ⟨31310960092436192308473701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20873973394957461538982467 31310960092436192308473701)
          ·
            refine ⟨5870805017331786057838819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31310960092436192308473701 5870805017331786057838819)
            ·
              refine ⟨8806207525997679086758229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5870805017331786057838819 8806207525997679086758229)
              ·
                refine ⟨25799436111321325449487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 8806207525997679086758229 25799436111321325449487)
                ·
                  rfl

theorem cell22_678297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 10].length) (baseStart_678297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678297 prefixEnd_678297 := by exact prefixLift 678297
  have htrace : WordTrace (prefixWord ++ tailWord_678297) baseStart_678297 baseEnd_678297 := by
    simpa [prefixWord, tailWord_678297, baseEnd_678297] using wordTrace_append hprefix tailTrace_678297
  have hstable : (prefixWord ++ tailWord_678297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678297).length < 2 ^ (prefixWord ++ tailWord_678297).sum := by decide
  have hdescent : baseEnd_678297 < baseStart_678297 := by decide
  rcases family_descends (prefixWord ++ tailWord_678297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678301 : List Nat := [1, 4, 2, 1, 4, 1, 1, 2, 1, 5]
def baseStart_678301 : Nat := 118140960795 + 678301 * 2 ^ 59
def prefixEnd_678301 : Nat := 4983230072969 + 3 ^ 40 * 678301 * 2
def baseEnd_678301 : Nat := 232196294283637251945371

theorem tailTrace_678301 : CollatzResearch.WordTrace tailWord_678301 prefixEnd_678301 232196294283637251945371 := by
  unfold tailWord_678301
  simp only [CollatzResearch.WordTrace]
  refine ⟨24739669915638796433050757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16493113277092530955367171 24739669915638796433050757)
  ·
    refine ⟨4638688109182274331197017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24739669915638796433050757 4638688109182274331197017)
    ·
      refine ⟨3479016081886705748397763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4638688109182274331197017 3479016081886705748397763)
      ·
        refine ⟨5218524122830058622596645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3479016081886705748397763 5218524122830058622596645)
        ·
          refine ⟨978473273030635991736871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5218524122830058622596645 978473273030635991736871)
          ·
            refine ⟨1467709909545953987605307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 978473273030635991736871 1467709909545953987605307)
            ·
              refine ⟨2201564864318930981407961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1467709909545953987605307 2201564864318930981407961)
              ·
                refine ⟨1651173648239198236055971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2201564864318930981407961 1651173648239198236055971)
                ·
                  refine ⟨2476760472358797354083957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1651173648239198236055971 2476760472358797354083957)
                  ·
                    refine ⟨232196294283637251945371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2476760472358797354083957 232196294283637251945371)
                    ·
                      rfl

theorem cell22_678301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_678301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678301 prefixEnd_678301 := by exact prefixLift 678301
  have htrace : WordTrace (prefixWord ++ tailWord_678301) baseStart_678301 baseEnd_678301 := by
    simpa [prefixWord, tailWord_678301, baseEnd_678301] using wordTrace_append hprefix tailTrace_678301
  have hstable : (prefixWord ++ tailWord_678301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678301).length < 2 ^ (prefixWord ++ tailWord_678301).sum := by decide
  have hdescent : baseEnd_678301 < baseStart_678301 := by decide
  rcases family_descends (prefixWord ++ tailWord_678301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678305 : List Nat := [1, 2, 3, 5, 1, 1, 3, 1, 1, 4]
def baseStart_678305 : Nat := 118140960795 + 678305 * 2 ^ 59
def prefixEnd_678305 : Nat := 4983230072969 + 3 ^ 40 * 678305 * 2
def baseEnd_678305 : Nat := 232197663565382574845359

theorem tailTrace_678305 : CollatzResearch.WordTrace tailWord_678305 prefixEnd_678305 232197663565382574845359 := by
  unfold tailWord_678305
  simp only [CollatzResearch.WordTrace]
  refine ⟨24739815807624305116196369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16493210538416203410797579 24739815807624305116196369)
  ·
    refine ⟨18554861855718228837147277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24739815807624305116196369 18554861855718228837147277)
    ·
      refine ⟨6958073195894335813930229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18554861855718228837147277 6958073195894335813930229)
      ·
        refine ⟨652319362115093982555959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6958073195894335813930229 652319362115093982555959)
        ·
          refine ⟨978479043172640973833939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652319362115093982555959 978479043172640973833939)
          ·
            refine ⟨1467718564758961460750909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 978479043172640973833939 1467718564758961460750909)
            ·
              refine ⟨550394461784610547781591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1467718564758961460750909 550394461784610547781591)
              ·
                refine ⟨825591692676915821672387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 550394461784610547781591 825591692676915821672387)
                ·
                  refine ⟨1238387539015373732508581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 825591692676915821672387 1238387539015373732508581)
                  ·
                    refine ⟨232197663565382574845359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1238387539015373732508581 232197663565382574845359)
                    ·
                      rfl

theorem cell22_678305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_678305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678305 prefixEnd_678305 := by exact prefixLift 678305
  have htrace : WordTrace (prefixWord ++ tailWord_678305) baseStart_678305 baseEnd_678305 := by
    simpa [prefixWord, tailWord_678305, baseEnd_678305] using wordTrace_append hprefix tailTrace_678305
  have hstable : (prefixWord ++ tailWord_678305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678305).length < 2 ^ (prefixWord ++ tailWord_678305).sum := by decide
  have hdescent : baseEnd_678305 < baseStart_678305 := by decide
  rcases family_descends (prefixWord ++ tailWord_678305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678346 : List Nat := [3, 1, 2, 1, 2, 2, 3, 2, 3, 3]
def baseStart_678346 : Nat := 118140960795 + 678346 * 2 ^ 59
def prefixEnd_678346 : Nat := 4983230072969 + 3 ^ 40 * 678346 * 2
def baseEnd_678346 : Nat := 232211698703272134570233

theorem tailTrace_678346 : CollatzResearch.WordTrace tailWord_678346 prefixEnd_678346 232211698703272134570233 := by
  unfold tailWord_678346
  simp only [CollatzResearch.WordTrace]
  refine ⟨6185327800118942279609723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16494207466983846078959261 6185327800118942279609723)
  ·
    refine ⟨9277991700178413419414585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6185327800118942279609723 9277991700178413419414585)
    ·
      refine ⟨6958493775133810064560939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9277991700178413419414585 6958493775133810064560939)
      ·
        refine ⟨10437740662700715096841409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6958493775133810064560939 10437740662700715096841409)
        ·
          refine ⟨7828305497025536322631057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10437740662700715096841409 7828305497025536322631057)
          ·
            refine ⟨5871229122769152241973293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7828305497025536322631057 5871229122769152241973293)
            ·
              refine ⟨2201710921038432090739985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5871229122769152241973293 2201710921038432090739985)
              ·
                refine ⟨1651283190778824068054989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2201710921038432090739985 1651283190778824068054989)
                ·
                  refine ⟨619231196542059025520621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1651283190778824068054989 619231196542059025520621)
                  ·
                    refine ⟨232211698703272134570233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 619231196542059025520621 232211698703272134570233)
                    ·
                      rfl

theorem cell22_678346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_678346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678346 prefixEnd_678346 := by exact prefixLift 678346
  have htrace : WordTrace (prefixWord ++ tailWord_678346) baseStart_678346 baseEnd_678346 := by
    simpa [prefixWord, tailWord_678346, baseEnd_678346] using wordTrace_append hprefix tailTrace_678346
  have hstable : (prefixWord ++ tailWord_678346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678346).length < 2 ^ (prefixWord ++ tailWord_678346).sum := by decide
  have hdescent : baseEnd_678346 < baseStart_678346 := by decide
  rcases family_descends (prefixWord ++ tailWord_678346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678376 : List Nat := [2, 1, 4, 1, 1, 3, 3, 2, 5]
def baseStart_678376 : Nat := 118140960795 + 678376 * 2 ^ 59
def prefixEnd_678376 : Nat := 4983230072969 + 3 ^ 40 * 678376 * 2
def baseEnd_678376 : Nat := 77407322772120685440047

theorem tailTrace_678376 : CollatzResearch.WordTrace tailWord_678376 prefixEnd_678376 77407322772120685440047 := by
  unfold tailWord_678376
  simp only [CollatzResearch.WordTrace]
  refine ⟨12371202695183542121015491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16494936926911389494687321 12371202695183542121015491)
  ·
    refine ⟨18556804042775313181523237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12371202695183542121015491 18556804042775313181523237)
    ·
      refine ⟨3479400758020371221535607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18556804042775313181523237 3479400758020371221535607)
      ·
        refine ⟨5219101137030556832303411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3479400758020371221535607 5219101137030556832303411)
        ·
          refine ⟨7828651705545835248455117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5219101137030556832303411 7828651705545835248455117)
          ·
            refine ⟨2935744389579688218170669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7828651705545835248455117 2935744389579688218170669)
            ·
              refine ⟨1100904146092383081814001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2935744389579688218170669 1100904146092383081814001)
              ·
                refine ⟨825678109569287311360501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1100904146092383081814001 825678109569287311360501)
                ·
                  refine ⟨77407322772120685440047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 825678109569287311360501 77407322772120685440047)
                  ·
                    rfl

theorem cell22_678376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 5].length) (baseStart_678376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678376 prefixEnd_678376 := by exact prefixLift 678376
  have htrace : WordTrace (prefixWord ++ tailWord_678376) baseStart_678376 baseEnd_678376 := by
    simpa [prefixWord, tailWord_678376, baseEnd_678376] using wordTrace_append hprefix tailTrace_678376
  have hstable : (prefixWord ++ tailWord_678376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678376).length < 2 ^ (prefixWord ++ tailWord_678376).sum := by decide
  have hdescent : baseEnd_678376 < baseStart_678376 := by decide
  rcases family_descends (prefixWord ++ tailWord_678376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678419 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 3, 5]
def baseStart_678419 : Nat := 118140960795 + 678419 * 2 ^ 59
def prefixEnd_678419 : Nat := 4983230072969 + 3 ^ 40 * 678419 * 2
def baseEnd_678419 : Nat := 232236688095124277495009

theorem tailTrace_678419 : CollatzResearch.WordTrace tailWord_678419 prefixEnd_678419 232236688095124277495009 := by
  unfold tailWord_678419
  simp only [CollatzResearch.WordTrace]
  refine ⟨24743973729211302585846311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16495982486140868390564207 24743973729211302585846311)
  ·
    refine ⟨37115960593816953878769467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24743973729211302585846311 37115960593816953878769467)
    ·
      refine ⟨55673940890725430818154201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37115960593816953878769467 55673940890725430818154201)
      ·
        refine ⟨41755455668044073113615651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55673940890725430818154201 41755455668044073113615651)
        ·
          refine ⟨62633183502066109670423477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41755455668044073113615651 62633183502066109670423477)
          ·
            refine ⟨5871860953318697781602201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62633183502066109670423477 5871860953318697781602201)
            ·
              refine ⟨4403895714989023336201651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5871860953318697781602201 4403895714989023336201651)
              ·
                refine ⟨6605843572483535004302477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4403895714989023336201651 6605843572483535004302477)
                ·
                  refine ⟨2477191339681325626613429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6605843572483535004302477 2477191339681325626613429)
                  ·
                    refine ⟨232236688095124277495009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2477191339681325626613429 232236688095124277495009)
                    ·
                      rfl

theorem cell22_678419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 5].length) (baseStart_678419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678419 prefixEnd_678419 := by exact prefixLift 678419
  have htrace : WordTrace (prefixWord ++ tailWord_678419) baseStart_678419 baseEnd_678419 := by
    simpa [prefixWord, tailWord_678419, baseEnd_678419] using wordTrace_append hprefix tailTrace_678419
  have hstable : (prefixWord ++ tailWord_678419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678419).length < 2 ^ (prefixWord ++ tailWord_678419).sum := by decide
  have hdescent : baseEnd_678419 < baseStart_678419 := by decide
  rcases family_descends (prefixWord ++ tailWord_678419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678449 : List Nat := [1, 2, 2, 3, 1, 1, 3, 9]
def baseStart_678449 : Nat := 118140960795 + 678449 * 2 ^ 59
def prefixEnd_678449 : Nat := 4983230072969 + 3 ^ 40 * 678449 * 2
def baseEnd_678449 : Nat := 25805217523134911027213

theorem tailTrace_678449 : CollatzResearch.WordTrace tailWord_678449 prefixEnd_678449 25805217523134911027213 := by
  unfold tailWord_678449
  simp only [CollatzResearch.WordTrace]
  refine ⟨24745067919102617709438401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16496711946068411806292267 24745067919102617709438401)
  ·
    refine ⟨18558800939326963282078801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24745067919102617709438401 18558800939326963282078801)
    ·
      refine ⟨13919100704495222461559101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18558800939326963282078801 13919100704495222461559101)
      ·
        refine ⟨5219662764185708423084663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13919100704495222461559101 5219662764185708423084663)
        ·
          refine ⟨7829494146278562634626995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5219662764185708423084663 7829494146278562634626995)
          ·
            refine ⟨11744241219417843951940493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7829494146278562634626995 11744241219417843951940493)
            ·
              refine ⟨4404090457281691481977685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11744241219417843951940493 4404090457281691481977685)
              ·
                refine ⟨25805217523134911027213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4404090457281691481977685 25805217523134911027213)
                ·
                  rfl

theorem cell22_678449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 9].length) (baseStart_678449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678449 prefixEnd_678449 := by exact prefixLift 678449
  have htrace : WordTrace (prefixWord ++ tailWord_678449) baseStart_678449 baseEnd_678449 := by
    simpa [prefixWord, tailWord_678449, baseEnd_678449] using wordTrace_append hprefix tailTrace_678449
  have hstable : (prefixWord ++ tailWord_678449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678449).length < 2 ^ (prefixWord ++ tailWord_678449).sum := by decide
  have hdescent : baseEnd_678449 < baseStart_678449 := by decide
  rcases family_descends (prefixWord ++ tailWord_678449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678453 : List Nat := [1, 3, 3, 1, 1, 2, 3, 3, 2, 3]
def baseStart_678453 : Nat := 118140960795 + 678453 * 2 ^ 59
def prefixEnd_678453 : Nat := 4983230072969 + 3 ^ 40 * 678453 * 2
def baseEnd_678453 : Nat := 232248326989959522144905

theorem tailTrace_678453 : CollatzResearch.WordTrace tailWord_678453 prefixEnd_678453 232248326989959522144905 := by
  unfold tailWord_678453
  simp only [CollatzResearch.WordTrace]
  refine ⟨24745213811088126392584013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16496809207392084261722675 24745213811088126392584013)
  ·
    refine ⟨9279455179158047397219005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24745213811088126392584013 9279455179158047397219005)
    ·
      refine ⟨3479795692184267773957127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9279455179158047397219005 3479795692184267773957127)
      ·
        refine ⟨5219693538276401660935691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3479795692184267773957127 5219693538276401660935691)
        ·
          refine ⟨7829540307414602491403537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5219693538276401660935691 7829540307414602491403537)
          ·
            refine ⟨5872155230560951868552653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7829540307414602491403537 5872155230560951868552653)
            ·
              refine ⟨2202058211460356950707245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5872155230560951868552653 2202058211460356950707245)
              ·
                refine ⟨825771829297633856515217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2202058211460356950707245 825771829297633856515217)
                ·
                  refine ⟨619328871973225392386413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 825771829297633856515217 619328871973225392386413)
                  ·
                    refine ⟨232248326989959522144905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 619328871973225392386413 232248326989959522144905)
                    ·
                      rfl

theorem cell22_678453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_678453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678453 prefixEnd_678453 := by exact prefixLift 678453
  have htrace : WordTrace (prefixWord ++ tailWord_678453) baseStart_678453 baseEnd_678453 := by
    simpa [prefixWord, tailWord_678453, baseEnd_678453] using wordTrace_append hprefix tailTrace_678453
  have hstable : (prefixWord ++ tailWord_678453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678453).length < 2 ^ (prefixWord ++ tailWord_678453).sum := by decide
  have hdescent : baseEnd_678453 < baseStart_678453 := by decide
  rcases family_descends (prefixWord ++ tailWord_678453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678464 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 2, 7]
def baseStart_678464 : Nat := 118140960795 + 678464 * 2 ^ 59
def prefixEnd_678464 : Nat := 4983230072969 + 3 ^ 40 * 678464 * 2
def baseEnd_678464 : Nat := 232252092514759160119871

theorem tailTrace_678464 : CollatzResearch.WordTrace tailWord_678464 prefixEnd_678464 232252092514759160119871 := by
  unfold tailWord_678464
  simp only [CollatzResearch.WordTrace]
  refine ⟨12372807507024137635617223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16497076676032183514156297 12372807507024137635617223)
  ·
    refine ⟨18559211260536206453425835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12372807507024137635617223 18559211260536206453425835)
    ·
      refine ⟨27838816890804309680138753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18559211260536206453425835 27838816890804309680138753)
      ·
        refine ⟨20879112668103232260104065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27838816890804309680138753 20879112668103232260104065)
        ·
          refine ⟨15659334501077424195078049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20879112668103232260104065 15659334501077424195078049)
          ·
            refine ⟨11744500875808068146308537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15659334501077424195078049 11744500875808068146308537)
            ·
              refine ⟨8808375656856051109731403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11744500875808068146308537 8808375656856051109731403)
              ·
                refine ⟨13212563485284076664597105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8808375656856051109731403 13212563485284076664597105)
                ·
                  refine ⟨9909422613963057498447829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13212563485284076664597105 9909422613963057498447829)
                  ·
                    refine ⟨232252092514759160119871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9909422613963057498447829 232252092514759160119871)
                    ·
                      rfl

theorem cell22_678464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 7].length) (baseStart_678464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678464 prefixEnd_678464 := by exact prefixLift 678464
  have htrace : WordTrace (prefixWord ++ tailWord_678464) baseStart_678464 baseEnd_678464 := by
    simpa [prefixWord, tailWord_678464, baseEnd_678464] using wordTrace_append hprefix tailTrace_678464
  have hstable : (prefixWord ++ tailWord_678464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678464).length < 2 ^ (prefixWord ++ tailWord_678464).sum := by decide
  have hdescent : baseEnd_678464 < baseStart_678464 := by decide
  rcases family_descends (prefixWord ++ tailWord_678464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678470 : List Nat := [6, 1, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_678470 : Nat := 118140960795 + 678470 * 2 ^ 59
def prefixEnd_678470 : Nat := 4983230072969 + 3 ^ 40 * 678470 * 2
def baseEnd_678470 : Nat := 232254146437377144469853

theorem tailTrace_678470 : CollatzResearch.WordTrace tailWord_678470 prefixEnd_678470 232254146437377144469853 := by
  unfold tailWord_678470
  simp only [CollatzResearch.WordTrace]
  refine ⟨773307307875829321748527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16497222568017692197301909 773307307875829321748527)
  ·
    refine ⟨1159960961813743982622791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 773307307875829321748527 1159960961813743982622791)
    ·
      refine ⟨1739941442720615973934187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1159960961813743982622791 1739941442720615973934187)
      ·
        refine ⟨2609912164080923960901281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1739941442720615973934187 2609912164080923960901281)
        ·
          refine ⟨1957434123060692970675961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2609912164080923960901281 1957434123060692970675961)
          ·
            refine ⟨1468075592295519728006971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1957434123060692970675961 1468075592295519728006971)
            ·
              refine ⟨2202113388443279592010457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1468075592295519728006971 2202113388443279592010457)
              ·
                refine ⟨1651585041332459694007843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2202113388443279592010457 1651585041332459694007843)
                ·
                  refine ⟨2477377561998689541011765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1651585041332459694007843 2477377561998689541011765)
                  ·
                    refine ⟨232254146437377144469853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2477377561998689541011765 232254146437377144469853)
                    ·
                      rfl

theorem cell22_678470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_678470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678470 prefixEnd_678470 := by exact prefixLift 678470
  have htrace : WordTrace (prefixWord ++ tailWord_678470) baseStart_678470 baseEnd_678470 := by
    simpa [prefixWord, tailWord_678470, baseEnd_678470] using wordTrace_append hprefix tailTrace_678470
  have hstable : (prefixWord ++ tailWord_678470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678470).length < 2 ^ (prefixWord ++ tailWord_678470).sum := by decide
  have hdescent : baseEnd_678470 < baseStart_678470 := by decide
  rcases family_descends (prefixWord ++ tailWord_678470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678511 : List Nat := [1, 1, 2, 1, 3, 2, 4, 3, 5]
def baseStart_678511 : Nat := 118140960795 + 678511 * 2 ^ 59
def prefixEnd_678511 : Nat := 4983230072969 + 3 ^ 40 * 678511 * 2
def baseEnd_678511 : Nat := 77422727191755568064909

theorem tailTrace_678511 : CollatzResearch.WordTrace tailWord_678511 prefixEnd_678511 77422727191755568064909 := by
  unfold tailWord_678511
  simp only [CollatzResearch.WordTrace]
  refine ⟨24747329244878002298195387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16498219496585334865463591 24747329244878002298195387)
  ·
    refine ⟨37120993867317003447293081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24747329244878002298195387 37120993867317003447293081)
    ·
      refine ⟨27840745400487752585469811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37120993867317003447293081 27840745400487752585469811)
      ·
        refine ⟨41761118100731628878204717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27840745400487752585469811 41761118100731628878204717)
        ·
          refine ⟨15660419287774360829326769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41761118100731628878204717 15660419287774360829326769)
          ·
            refine ⟨11745314465830770621995077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15660419287774360829326769 11745314465830770621995077)
            ·
              refine ⟨2202246462343269491624077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11745314465830770621995077 2202246462343269491624077)
              ·
                refine ⟨825842423378726059359029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2202246462343269491624077 825842423378726059359029)
                ·
                  refine ⟨77422727191755568064909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 825842423378726059359029 77422727191755568064909)
                  ·
                    rfl

theorem cell22_678511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 5].length) (baseStart_678511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678511 prefixEnd_678511 := by exact prefixLift 678511
  have htrace : WordTrace (prefixWord ++ tailWord_678511) baseStart_678511 baseEnd_678511 := by
    simpa [prefixWord, tailWord_678511, baseEnd_678511] using wordTrace_append hprefix tailTrace_678511
  have hstable : (prefixWord ++ tailWord_678511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678511).length < 2 ^ (prefixWord ++ tailWord_678511).sum := by decide
  have hdescent : baseEnd_678511 < baseStart_678511 := by decide
  rcases family_descends (prefixWord ++ tailWord_678511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678532 : List Nat := [2, 3, 2, 1, 3, 2, 2, 3, 1, 3]
def baseStart_678532 : Nat := 118140960795 + 678532 * 2 ^ 59
def prefixEnd_678532 : Nat := 4983230072969 + 3 ^ 40 * 678532 * 2
def baseEnd_678532 : Nat := 232275370304429649419663

theorem tailTrace_678532 : CollatzResearch.WordTrace tailWord_678532 prefixEnd_678532 232275370304429649419663 := by
  unfold tailWord_678532
  simp only [CollatzResearch.WordTrace]
  refine ⟨12374047588900961442354925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16498730118534615256473233 12374047588900961442354925)
  ·
    refine ⟨4640267845837860540883097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12374047588900961442354925 4640267845837860540883097)
    ·
      refine ⟨3480200884378395405662323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4640267845837860540883097 3480200884378395405662323)
      ·
        refine ⟨5220301326567593108493485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3480200884378395405662323 5220301326567593108493485)
        ·
          refine ⟨1957612997462847415685057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5220301326567593108493485 1957612997462847415685057)
          ·
            refine ⟨1468209748097135561763793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1957612997462847415685057 1468209748097135561763793)
            ·
              refine ⟨1101157311072851671322845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1468209748097135561763793 1101157311072851671322845)
              ·
                refine ⟨412933991652319376746067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1101157311072851671322845 412933991652319376746067)
                ·
                  refine ⟨619400987478479065119101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 412933991652319376746067 619400987478479065119101)
                  ·
                    refine ⟨232275370304429649419663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 619400987478479065119101 232275370304429649419663)
                    ·
                      rfl

theorem cell22_678532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_678532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678532 prefixEnd_678532 := by exact prefixLift 678532
  have htrace : WordTrace (prefixWord ++ tailWord_678532) baseStart_678532 baseEnd_678532 := by
    simpa [prefixWord, tailWord_678532, baseEnd_678532] using wordTrace_append hprefix tailTrace_678532
  have hstable : (prefixWord ++ tailWord_678532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678532).length < 2 ^ (prefixWord ++ tailWord_678532).sum := by decide
  have hdescent : baseEnd_678532 < baseStart_678532 := by decide
  rcases family_descends (prefixWord ++ tailWord_678532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678573 : List Nat := [1, 5, 2, 1, 1, 2, 2, 2, 6]
def baseStart_678573 : Nat := 118140960795 + 678573 * 2 ^ 59
def prefixEnd_678573 : Nat := 4983230072969 + 3 ^ 40 * 678573 * 2
def baseEnd_678573 : Nat := 77429801814106403048179

theorem tailTrace_678573 : CollatzResearch.WordTrace tailWord_678573 prefixEnd_678573 77429801814106403048179 := by
  unfold tailWord_678573
  simp only [CollatzResearch.WordTrace]
  refine ⟨24749590570653386886952373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16499727047102257924634915 24749590570653386886952373)
  ·
    refine ⟨2320274115998755020651785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24749590570653386886952373 2320274115998755020651785)
    ·
      refine ⟨1740205586999066265488839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2320274115998755020651785 1740205586999066265488839)
      ·
        refine ⟨2610308380498599398233259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1740205586999066265488839 2610308380498599398233259)
        ·
          refine ⟨3915462570747899097349889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2610308380498599398233259 3915462570747899097349889)
          ·
            refine ⟨2936596928060924323012417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3915462570747899097349889 2936596928060924323012417)
            ·
              refine ⟨2202447696045693242259313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2936596928060924323012417 2202447696045693242259313)
              ·
                refine ⟨1651835772034269931694485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2202447696045693242259313 1651835772034269931694485)
                ·
                  refine ⟨77429801814106403048179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1651835772034269931694485 77429801814106403048179)
                  ·
                    rfl

theorem cell22_678573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_678573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678573 prefixEnd_678573 := by exact prefixLift 678573
  have htrace : WordTrace (prefixWord ++ tailWord_678573) baseStart_678573 baseEnd_678573 := by
    simpa [prefixWord, tailWord_678573, baseEnd_678573] using wordTrace_append hprefix tailTrace_678573
  have hstable : (prefixWord ++ tailWord_678573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678573).length < 2 ^ (prefixWord ++ tailWord_678573).sum := by decide
  have hdescent : baseEnd_678573 < baseStart_678573 := by decide
  rcases family_descends (prefixWord ++ tailWord_678573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678586 : List Nat := [3, 1, 1, 1, 2, 3, 1, 3, 1, 6]
def baseStart_678586 : Nat := 118140960795 + 678586 * 2 ^ 59
def prefixEnd_678586 : Nat := 4983230072969 + 3 ^ 40 * 678586 * 2
def baseEnd_678586 : Nat := 232293855607991508569497

theorem tailTrace_678586 : CollatzResearch.WordTrace tailWord_678586 prefixEnd_678586 232293855607991508569497 := by
  unfold tailWord_678586
  simp only [CollatzResearch.WordTrace]
  refine ⟨6187516179901572526793903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16500043146404193404783741 6187516179901572526793903)
  ·
    refine ⟨9281274269852358790190855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6187516179901572526793903 9281274269852358790190855)
    ·
      refine ⟨13921911404778538185286283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9281274269852358790190855 13921911404778538185286283)
      ·
        refine ⟨20882867107167807277929425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13921911404778538185286283 20882867107167807277929425)
        ·
          refine ⟨15662150330375855458447069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20882867107167807277929425 15662150330375855458447069)
          ·
            refine ⟨5873306373890945796917651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15662150330375855458447069 5873306373890945796917651)
            ·
              refine ⟨8809959560836418695376477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5873306373890945796917651 8809959560836418695376477)
              ·
                refine ⟨3303734835313657010766179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8809959560836418695376477 3303734835313657010766179)
                ·
                  refine ⟨4955602252970485516149269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3303734835313657010766179 4955602252970485516149269)
                  ·
                    refine ⟨232293855607991508569497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4955602252970485516149269 232293855607991508569497)
                    ·
                      rfl

theorem cell22_678586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_678586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678586 prefixEnd_678586 := by exact prefixLift 678586
  have htrace : WordTrace (prefixWord ++ tailWord_678586) baseStart_678586 baseEnd_678586 := by
    simpa [prefixWord, tailWord_678586, baseEnd_678586] using wordTrace_append hprefix tailTrace_678586
  have hstable : (prefixWord ++ tailWord_678586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678586).length < 2 ^ (prefixWord ++ tailWord_678586).sum := by decide
  have hdescent : baseEnd_678586 < baseStart_678586 := by decide
  rcases family_descends (prefixWord ++ tailWord_678586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678588 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 6, 3]
def baseStart_678588 : Nat := 118140960795 + 678588 * 2 ^ 59
def prefixEnd_678588 : Nat := 4983230072969 + 3 ^ 40 * 678588 * 2
def baseEnd_678588 : Nat := 232294540248864170019491

theorem tailTrace_678588 : CollatzResearch.WordTrace tailWord_678588 prefixEnd_678588 232294540248864170019491 := by
  unfold tailWord_678588
  simp only [CollatzResearch.WordTrace]
  refine ⟨12375068832799522224374209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16500091777066029632498945 12375068832799522224374209)
  ·
    refine ⟨9281301624599641668280657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12375068832799522224374209 9281301624599641668280657)
    ·
      refine ⟨6960976218449731251210493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9281301624599641668280657 6960976218449731251210493)
      ·
        refine ⟨2610366081918649219203935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6960976218449731251210493 2610366081918649219203935)
        ·
          refine ⟨3915549122877973828805903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2610366081918649219203935 3915549122877973828805903)
          ·
            refine ⟨5873323684316960743208855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3915549122877973828805903 5873323684316960743208855)
            ·
              refine ⟨8809985526475441114813283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5873323684316960743208855 8809985526475441114813283)
              ·
                refine ⟨13214978289713161672219925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8809985526475441114813283 13214978289713161672219925)
                ·
                  refine ⟨619452107330304453385309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13214978289713161672219925 619452107330304453385309)
                  ·
                    refine ⟨232294540248864170019491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 619452107330304453385309 232294540248864170019491)
                    ·
                      rfl

theorem cell22_678588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_678588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678588 prefixEnd_678588 := by exact prefixLift 678588
  have htrace : WordTrace (prefixWord ++ tailWord_678588) baseStart_678588 baseEnd_678588 := by
    simpa [prefixWord, tailWord_678588, baseEnd_678588] using wordTrace_append hprefix tailTrace_678588
  have hstable : (prefixWord ++ tailWord_678588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678588).length < 2 ^ (prefixWord ++ tailWord_678588).sum := by decide
  have hdescent : baseEnd_678588 < baseStart_678588 := by decide
  rcases family_descends (prefixWord ++ tailWord_678588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678633 : List Nat := [1, 2, 1, 1, 1, 2, 4, 4, 3, 3]
def baseStart_678633 : Nat := 118140960795 + 678633 * 2 ^ 59
def prefixEnd_678633 : Nat := 4983230072969 + 3 ^ 40 * 678633 * 2
def baseEnd_678633 : Nat := 232309944668499052644353

theorem tailTrace_678633 : CollatzResearch.WordTrace tailWord_678633 prefixEnd_678633 232309944668499052644353 := by
  unfold tailWord_678633
  simp only [CollatzResearch.WordTrace]
  refine ⟨24751778950436017134136553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16501185966957344756091035 24751778950436017134136553)
  ·
    refine ⟨18563834212827012850602415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24751778950436017134136553 18563834212827012850602415)
    ·
      refine ⟨27845751319240519275903623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18563834212827012850602415 27845751319240519275903623)
      ·
        refine ⟨41768626978860778913855435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27845751319240519275903623 41768626978860778913855435)
        ·
          refine ⟨62652940468291168370783153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41768626978860778913855435 62652940468291168370783153)
          ·
            refine ⟨46989705351218376278087365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62652940468291168370783153 46989705351218376278087365)
            ·
              refine ⟨8810569753353445552141381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46989705351218376278087365 8810569753353445552141381)
              ·
                refine ⟨1651981828753771041026509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8810569753353445552141381 1651981828753771041026509)
                ·
                  refine ⟨619493185782664140384941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1651981828753771041026509 619493185782664140384941)
                  ·
                    refine ⟨232309944668499052644353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 619493185782664140384941 232309944668499052644353)
                    ·
                      rfl

theorem cell22_678633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 3, 3].length) (baseStart_678633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678633 prefixEnd_678633 := by exact prefixLift 678633
  have htrace : WordTrace (prefixWord ++ tailWord_678633) baseStart_678633 baseEnd_678633 := by
    simpa [prefixWord, tailWord_678633, baseEnd_678633] using wordTrace_append hprefix tailTrace_678633
  have hstable : (prefixWord ++ tailWord_678633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678633).length < 2 ^ (prefixWord ++ tailWord_678633).sum := by decide
  have hdescent : baseEnd_678633 < baseStart_678633 := by decide
  rcases family_descends (prefixWord ++ tailWord_678633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678661 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 3, 7]
def baseStart_678661 : Nat := 118140960795 + 678661 * 2 ^ 59
def prefixEnd_678661 : Nat := 4983230072969 + 3 ^ 40 * 678661 * 2
def baseEnd_678661 : Nat := 232319529640716312944267

theorem tailTrace_678661 : CollatzResearch.WordTrace tailWord_678661 prefixEnd_678661 232319529640716312944267 := by
  unfold tailWord_678661
  simp only [CollatzResearch.WordTrace]
  refine ⟨24752800194334577916155837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16501866796223051944103891 24752800194334577916155837)
  ·
    refine ⟨9282300072875466718558439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24752800194334577916155837 9282300072875466718558439)
    ·
      refine ⟨13923450109313200077837659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9282300072875466718558439 13923450109313200077837659)
      ·
        refine ⟨20885175163969800116756489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13923450109313200077837659 20885175163969800116756489)
        ·
          refine ⟨15663881372977350087567367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20885175163969800116756489 15663881372977350087567367)
          ·
            refine ⟨23495822059466025131351051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15663881372977350087567367 23495822059466025131351051)
            ·
              refine ⟨35243733089199037697026577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23495822059466025131351051 35243733089199037697026577)
              ·
                refine ⟨26432799816899278272769933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35243733089199037697026577 26432799816899278272769933)
                ·
                  refine ⟨9912299931337229352288725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26432799816899278272769933 9912299931337229352288725)
                  ·
                    refine ⟨232319529640716312944267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9912299931337229352288725 232319529640716312944267)
                    ·
                      rfl

theorem cell22_678661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_678661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678661 prefixEnd_678661 := by exact prefixLift 678661
  have htrace : WordTrace (prefixWord ++ tailWord_678661) baseStart_678661 baseEnd_678661 := by
    simpa [prefixWord, tailWord_678661, baseEnd_678661] using wordTrace_append hprefix tailTrace_678661
  have hstable : (prefixWord ++ tailWord_678661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678661).length < 2 ^ (prefixWord ++ tailWord_678661).sum := by decide
  have hdescent : baseEnd_678661 < baseStart_678661 := by decide
  rcases family_descends (prefixWord ++ tailWord_678661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678693 : List Nat := [1, 3, 1, 2, 3, 1, 1, 3, 3, 4]
def baseStart_678693 : Nat := 118140960795 + 678693 * 2 ^ 59
def prefixEnd_678693 : Nat := 4983230072969 + 3 ^ 40 * 678693 * 2
def baseEnd_678693 : Nat := 232330483894678896144169

theorem tailTrace_678693 : CollatzResearch.WordTrace tailWord_678693 prefixEnd_678693 232330483894678896144169 := by
  unfold tailWord_678693
  simp only [CollatzResearch.WordTrace]
  refine ⟨24753967330218647381320733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16502644886812431587547155 24753967330218647381320733)
  ·
    refine ⟨9282737748831992767995275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24753967330218647381320733 9282737748831992767995275)
    ·
      refine ⟨13924106623247989151992913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9282737748831992767995275 13924106623247989151992913)
      ·
        refine ⟨10443079967435991863994685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13924106623247989151992913 10443079967435991863994685)
        ·
          refine ⟨3916154987788496948998007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10443079967435991863994685 3916154987788496948998007)
          ·
            refine ⟨5874232481682745423497011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3916154987788496948998007 5874232481682745423497011)
            ·
              refine ⟨8811348722524118135245517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5874232481682745423497011 8811348722524118135245517)
              ·
                refine ⟨3304255770946544300717069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8811348722524118135245517 3304255770946544300717069)
                ·
                  refine ⟨1239095914104954112768901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3304255770946544300717069 1239095914104954112768901)
                  ·
                    refine ⟨232330483894678896144169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1239095914104954112768901 232330483894678896144169)
                    ·
                      rfl

theorem cell22_678693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_678693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678693 prefixEnd_678693 := by exact prefixLift 678693
  have htrace : WordTrace (prefixWord ++ tailWord_678693) baseStart_678693 baseEnd_678693 := by
    simpa [prefixWord, tailWord_678693, baseEnd_678693] using wordTrace_append hprefix tailTrace_678693
  have hstable : (prefixWord ++ tailWord_678693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678693).length < 2 ^ (prefixWord ++ tailWord_678693).sum := by decide
  have hdescent : baseEnd_678693 < baseStart_678693 := by decide
  rcases family_descends (prefixWord ++ tailWord_678693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678738 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 3, 6]
def baseStart_678738 : Nat := 118140960795 + 678738 * 2 ^ 59
def prefixEnd_678738 : Nat := 4983230072969 + 3 ^ 40 * 678738 * 2
def baseEnd_678738 : Nat := 232345888314313778769031

theorem tailTrace_678738 : CollatzResearch.WordTrace tailWord_678738 prefixEnd_678738 232345888314313778769031 := by
  unfold tailWord_678738
  simp only [CollatzResearch.WordTrace]
  refine ⟨6188902153763905016677217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16503739076703746711139245 6188902153763905016677217)
  ·
    refine ⟨4641676615322928762507913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6188902153763905016677217 4641676615322928762507913)
    ·
      refine ⟨3481257461492196571880935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4641676615322928762507913 3481257461492196571880935)
      ·
        refine ⟨5221886192238294857821403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3481257461492196571880935 5221886192238294857821403)
        ·
          refine ⟨7832829288357442286732105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5221886192238294857821403 7832829288357442286732105)
          ·
            refine ⟨5874621966268081715049079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7832829288357442286732105 5874621966268081715049079)
            ·
              refine ⟨8811932949402122572573619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5874621966268081715049079 8811932949402122572573619)
              ·
                refine ⟨13217899424103183858860429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8811932949402122572573619 13217899424103183858860429)
                ·
                  refine ⟨4956712284038693947072661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13217899424103183858860429 4956712284038693947072661)
                  ·
                    refine ⟨232345888314313778769031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4956712284038693947072661 232345888314313778769031)
                    ·
                      rfl

theorem cell22_678738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_678738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678738 prefixEnd_678738 := by exact prefixLift 678738
  have htrace : WordTrace (prefixWord ++ tailWord_678738) baseStart_678738 baseEnd_678738 := by
    simpa [prefixWord, tailWord_678738, baseEnd_678738] using wordTrace_append hprefix tailTrace_678738
  have hstable : (prefixWord ++ tailWord_678738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678738).length < 2 ^ (prefixWord ++ tailWord_678738).sum := by decide
  have hdescent : baseEnd_678738 < baseStart_678738 := by decide
  rcases family_descends (prefixWord ++ tailWord_678738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678806 : List Nat := [5, 3, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_678806 : Nat := 118140960795 + 678806 * 2 ^ 59
def prefixEnd_678806 : Nat := 4983230072969 + 3 ^ 40 * 678806 * 2
def baseEnd_678806 : Nat := 232369166103984268068823

theorem tailTrace_678806 : CollatzResearch.WordTrace tailWord_678806 prefixEnd_678806 232369166103984268068823 := by
  unfold tailWord_678806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1547380548675579230011517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16505392519206178453456181 1547380548675579230011517)
  ·
    refine ⟨580267705753342211254319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1547380548675579230011517 580267705753342211254319)
    ·
      refine ⟨870401558630013316881479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 580267705753342211254319 870401558630013316881479)
      ·
        refine ⟨1305602337945019975322219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 870401558630013316881479 1305602337945019975322219)
        ·
          refine ⟨1958403506917529962983329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1305602337945019975322219 1958403506917529962983329)
          ·
            refine ⟨1468802630188147472237497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1958403506917529962983329 1468802630188147472237497)
            ·
              refine ⟨1101601972641110604178123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1468802630188147472237497 1101601972641110604178123)
              ·
                refine ⟨1652402958961665906267185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1101601972641110604178123 1652402958961665906267185)
                ·
                  refine ⟨1239302219221249429700389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1652402958961665906267185 1239302219221249429700389)
                  ·
                    refine ⟨232369166103984268068823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1239302219221249429700389 232369166103984268068823)
                    ·
                      rfl

theorem cell22_678806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_678806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678806 prefixEnd_678806 := by exact prefixLift 678806
  have htrace : WordTrace (prefixWord ++ tailWord_678806) baseStart_678806 baseEnd_678806 := by
    simpa [prefixWord, tailWord_678806, baseEnd_678806] using wordTrace_append hprefix tailTrace_678806
  have hstable : (prefixWord ++ tailWord_678806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678806).length < 2 ^ (prefixWord ++ tailWord_678806).sum := by decide
  have hdescent : baseEnd_678806 < baseStart_678806 := by decide
  rcases family_descends (prefixWord ++ tailWord_678806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678838 : List Nat := [5, 1, 4, 1, 2, 1, 1, 7]
def baseStart_678838 : Nat := 118140960795 + 678838 * 2 ^ 59
def prefixEnd_678838 : Nat := 4983230072969 + 3 ^ 40 * 678838 * 2
def baseEnd_678838 : Nat := 25820013373105205696525

theorem tailTrace_678838 : CollatzResearch.WordTrace tailWord_678838 prefixEnd_678838 25820013373105205696525 := by
  unfold tailWord_678838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1547453494668333571584323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16506170609795558096899445 1547453494668333571584323)
  ·
    refine ⟨2321180242002500357376485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1547453494668333571584323 2321180242002500357376485)
    ·
      refine ⟨435221295375468817008091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2321180242002500357376485 435221295375468817008091)
      ·
        refine ⟨652831943063203225512137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435221295375468817008091 652831943063203225512137)
        ·
          refine ⟨489623957297402419134103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 652831943063203225512137 489623957297402419134103)
          ·
            refine ⟨734435935946103628701155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489623957297402419134103 734435935946103628701155)
            ·
              refine ⟨1101653903919155443051733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 734435935946103628701155 1101653903919155443051733)
              ·
                refine ⟨25820013373105205696525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1101653903919155443051733 25820013373105205696525)
                ·
                  rfl

theorem cell22_678838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_678838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678838 prefixEnd_678838 := by exact prefixLift 678838
  have htrace : WordTrace (prefixWord ++ tailWord_678838) baseStart_678838 baseEnd_678838 := by
    simpa [prefixWord, tailWord_678838, baseEnd_678838] using wordTrace_append hprefix tailTrace_678838
  have hstable : (prefixWord ++ tailWord_678838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678838).length < 2 ^ (prefixWord ++ tailWord_678838).sum := by decide
  have hdescent : baseEnd_678838 < baseStart_678838 := by decide
  rcases family_descends (prefixWord ++ tailWord_678838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678860 : List Nat := [2, 2, 1, 4, 1, 1, 3, 2, 6]
def baseStart_678860 : Nat := 118140960795 + 678860 * 2 ^ 59
def prefixEnd_678860 : Nat := 4983230072969 + 3 ^ 40 * 678860 * 2
def baseEnd_678860 : Nat := 77462550469182042406219

theorem tailTrace_678860 : CollatzResearch.WordTrace tailWord_678860 prefixEnd_678860 77462550469182042406219 := by
  unfold tailWord_678860
  simp only [CollatzResearch.WordTrace]
  refine ⟨12380029160306817451325017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16506705547075756601766689 12380029160306817451325017)
  ·
    refine ⟨9285021870230113088493763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12380029160306817451325017 9285021870230113088493763)
    ·
      refine ⟨13927532805345169632740645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9285021870230113088493763 13927532805345169632740645)
      ·
        refine ⟨2611412401002219306138871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13927532805345169632740645 2611412401002219306138871)
        ·
          refine ⟨3917118601503328959208307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2611412401002219306138871 3917118601503328959208307)
          ·
            refine ⟨5875677902254993438812461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3917118601503328959208307 5875677902254993438812461)
            ·
              refine ⟨2203379213345622539554673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5875677902254993438812461 2203379213345622539554673)
              ·
                refine ⟨1652534410009216904666005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2203379213345622539554673 1652534410009216904666005)
                ·
                  refine ⟨77462550469182042406219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1652534410009216904666005 77462550469182042406219)
                  ·
                    rfl

theorem cell22_678860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 6].length) (baseStart_678860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678860 prefixEnd_678860 := by exact prefixLift 678860
  have htrace : WordTrace (prefixWord ++ tailWord_678860) baseStart_678860 baseEnd_678860 := by
    simpa [prefixWord, tailWord_678860, baseEnd_678860] using wordTrace_append hprefix tailTrace_678860
  have hstable : (prefixWord ++ tailWord_678860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678860).length < 2 ^ (prefixWord ++ tailWord_678860).sum := by decide
  have hdescent : baseEnd_678860 < baseStart_678860 := by decide
  rcases family_descends (prefixWord ++ tailWord_678860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678900 : List Nat := [2, 6, 2, 1, 1, 1, 3, 1, 5]
def baseStart_678900 : Nat := 118140960795 + 678900 * 2 ^ 59
def prefixEnd_678900 : Nat := 4983230072969 + 3 ^ 40 * 678900 * 2
def baseEnd_678900 : Nat := 77467114741666452072845

theorem tailTrace_678900 : CollatzResearch.WordTrace tailWord_678900 prefixEnd_678900 77467114741666452072845 := by
  unfold tailWord_678900
  simp only [CollatzResearch.WordTrace]
  refine ⟨12380758620234360867053077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16507678160312481156070769 12380758620234360867053077)
  ·
    refine ⟨580348060323485665643113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12380758620234360867053077 580348060323485665643113)
    ·
      refine ⟨435261045242614249232335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 580348060323485665643113 435261045242614249232335)
      ·
        refine ⟨652891567863921373848503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435261045242614249232335 652891567863921373848503)
        ·
          refine ⟨979337351795882060772755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652891567863921373848503 979337351795882060772755)
          ·
            refine ⟨1469006027693823091159133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 979337351795882060772755 1469006027693823091159133)
            ·
              refine ⟨550877260385183659184675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1469006027693823091159133 550877260385183659184675)
              ·
                refine ⟨826315890577775488777013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 550877260385183659184675 826315890577775488777013)
                ·
                  refine ⟨77467114741666452072845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 826315890577775488777013 77467114741666452072845)
                  ·
                    rfl

theorem cell22_678900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_678900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678900 prefixEnd_678900 := by exact prefixLift 678900
  have htrace : WordTrace (prefixWord ++ tailWord_678900) baseStart_678900 baseEnd_678900 := by
    simpa [prefixWord, tailWord_678900, baseEnd_678900] using wordTrace_append hprefix tailTrace_678900
  have hstable : (prefixWord ++ tailWord_678900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678900).length < 2 ^ (prefixWord ++ tailWord_678900).sum := by decide
  have hdescent : baseEnd_678900 < baseStart_678900 := by decide
  rcases family_descends (prefixWord ++ tailWord_678900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678922 : List Nat := [3, 1, 2, 2, 3, 1, 4, 6]
def baseStart_678922 : Nat := 118140960795 + 678922 * 2 ^ 59
def prefixEnd_678922 : Nat := 4983230072969 + 3 ^ 40 * 678922 * 2
def baseEnd_678922 : Nat := 25823208363844292463163

theorem tailTrace_678922 : CollatzResearch.WordTrace tailWord_678922 prefixEnd_678922 25823208363844292463163 := by
  unfold tailWord_678922
  simp only [CollatzResearch.WordTrace]
  refine ⟨6190579911597254872851755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16508213097592679660938013 6190579911597254872851755)
  ·
    refine ⟨9285869867395882309277633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6190579911597254872851755 9285869867395882309277633)
    ·
      refine ⟨6964402400546911731958225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9285869867395882309277633 6964402400546911731958225)
      ·
        refine ⟨5223301800410183798968669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6964402400546911731958225 5223301800410183798968669)
        ·
          refine ⟨1958738175153818924613251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5223301800410183798968669 1958738175153818924613251)
          ·
            refine ⟨2938107262730728386919877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1958738175153818924613251 2938107262730728386919877)
            ·
              refine ⟨550895111762011572547477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2938107262730728386919877 550895111762011572547477)
              ·
                refine ⟨25823208363844292463163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 550895111762011572547477 25823208363844292463163)
                ·
                  rfl

theorem cell22_678922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 6].length) (baseStart_678922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678922 prefixEnd_678922 := by exact prefixLift 678922
  have htrace : WordTrace (prefixWord ++ tailWord_678922) baseStart_678922 baseEnd_678922 := by
    simpa [prefixWord, tailWord_678922, baseEnd_678922] using wordTrace_append hprefix tailTrace_678922
  have hstable : (prefixWord ++ tailWord_678922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678922).length < 2 ^ (prefixWord ++ tailWord_678922).sum := by decide
  have hdescent : baseEnd_678922 < baseStart_678922 := by decide
  rcases family_descends (prefixWord ++ tailWord_678922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678965 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 1, 7]
def baseStart_678965 : Nat := 118140960795 + 678965 * 2 ^ 59
def prefixEnd_678965 : Nat := 4983230072969 + 3 ^ 40 * 678965 * 2
def baseEnd_678965 : Nat := 232423595053360853343335

theorem tailTrace_678965 : CollatzResearch.WordTrace tailWord_678965 prefixEnd_678965 232423595053360853343335 := by
  unfold tailWord_678965
  simp only [CollatzResearch.WordTrace]
  refine ⟨24763887985233237835222349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16509258656822158556814899 24763887985233237835222349)
  ·
    refine ⟨9286457994462464188208381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24763887985233237835222349 9286457994462464188208381)
    ·
      refine ⟨3482421747923424070578143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9286457994462464188208381 3482421747923424070578143)
      ·
        refine ⟨5223632621885136105867215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3482421747923424070578143 5223632621885136105867215)
        ·
          refine ⟨7835448932827704158800823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5223632621885136105867215 7835448932827704158800823)
          ·
            refine ⟨11753173399241556238201235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7835448932827704158800823 11753173399241556238201235)
            ·
              refine ⟨17629760098862334357301853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11753173399241556238201235 17629760098862334357301853)
              ·
                refine ⟨6611160037073375383988195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17629760098862334357301853 6611160037073375383988195)
                ·
                  refine ⟨9916740055610063075982293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6611160037073375383988195 9916740055610063075982293)
                  ·
                    refine ⟨232423595053360853343335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9916740055610063075982293 232423595053360853343335)
                    ·
                      rfl

theorem cell22_678965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_678965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_678965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_678965 prefixEnd_678965 := by exact prefixLift 678965
  have htrace : WordTrace (prefixWord ++ tailWord_678965) baseStart_678965 baseEnd_678965 := by
    simpa [prefixWord, tailWord_678965, baseEnd_678965] using wordTrace_append hprefix tailTrace_678965
  have hstable : (prefixWord ++ tailWord_678965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678965).length < 2 ^ (prefixWord ++ tailWord_678965).sum := by decide
  have hdescent : baseEnd_678965 < baseStart_678965 := by decide
  rcases family_descends (prefixWord ++ tailWord_678965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679040 : List Nat := [2, 1, 1, 2, 1, 3, 2, 10]
def baseStart_679040 : Nat := 118140960795 + 679040 * 2 ^ 59
def prefixEnd_679040 : Nat := 4983230072969 + 3 ^ 40 * 679040 * 2
def baseEnd_679040 : Nat := 25827696565120628635345

theorem tailTrace_679040 : CollatzResearch.WordTrace tailWord_679040 prefixEnd_679040 25827696565120628635345 := by
  unfold tailWord_679040
  simp only [CollatzResearch.WordTrace]
  refine ⟨12383311729980762822101287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16511082306641017096135049 12383311729980762822101287)
  ·
    refine ⟨18574967594971144233151931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12383311729980762822101287 18574967594971144233151931)
    ·
      refine ⟨27862451392456716349727897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18574967594971144233151931 27862451392456716349727897)
      ·
        refine ⟨20896838544342537262295923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27862451392456716349727897 20896838544342537262295923)
        ·
          refine ⟨31345257816513805893443885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20896838544342537262295923 31345257816513805893443885)
          ·
            refine ⟨11754471681192677210041457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31345257816513805893443885 11754471681192677210041457)
            ·
              refine ⟨8815853760894507907531093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11754471681192677210041457 8815853760894507907531093)
              ·
                refine ⟨25827696565120628635345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 8815853760894507907531093 25827696565120628635345)
                ·
                  rfl

theorem cell22_679040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 10].length) (baseStart_679040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_679040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_679040 prefixEnd_679040 := by exact prefixLift 679040
  have htrace : WordTrace (prefixWord ++ tailWord_679040) baseStart_679040 baseEnd_679040 := by
    simpa [prefixWord, tailWord_679040, baseEnd_679040] using wordTrace_append hprefix tailTrace_679040
  have hstable : (prefixWord ++ tailWord_679040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679040).length < 2 ^ (prefixWord ++ tailWord_679040).sum := by decide
  have hdescent : baseEnd_679040 < baseStart_679040 := by decide
  rcases family_descends (prefixWord ++ tailWord_679040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679048 : List Nat := [2, 1, 3, 4, 2, 2, 2, 1, 1, 4]
def baseStart_679048 : Nat := 118140960795 + 679048 * 2 ^ 59
def prefixEnd_679048 : Nat := 4983230072969 + 3 ^ 40 * 679048 * 2
def baseEnd_679048 : Nat := 232452007649576303518081

theorem tailTrace_679048 : CollatzResearch.WordTrace tailWord_679048 prefixEnd_679048 232452007649576303518081 := by
  unfold tailWord_679048
  simp only [CollatzResearch.WordTrace]
  refine ⟨12383457621966271505246899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16511276829288362006995865 12383457621966271505246899)
  ·
    refine ⟨18575186432949407257870349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12383457621966271505246899 18575186432949407257870349)
    ·
      refine ⟨6965694912356027721701381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18575186432949407257870349 6965694912356027721701381)
      ·
        refine ⟨1306067796066755197819009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6965694912356027721701381 1306067796066755197819009)
        ·
          refine ⟨979550847050066398364257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1306067796066755197819009 979550847050066398364257)
          ·
            refine ⟨734663135287549798773193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 979550847050066398364257 734663135287549798773193)
            ·
              refine ⟨550997351465662349079895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 734663135287549798773193 550997351465662349079895)
              ·
                refine ⟨826496027198493523619843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 550997351465662349079895 826496027198493523619843)
                ·
                  refine ⟨1239744040797740285429765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 826496027198493523619843 1239744040797740285429765)
                  ·
                    refine ⟨232452007649576303518081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1239744040797740285429765 232452007649576303518081)
                    ·
                      rfl

theorem cell22_679048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_679048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_679048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_679048 prefixEnd_679048 := by exact prefixLift 679048
  have htrace : WordTrace (prefixWord ++ tailWord_679048) baseStart_679048 baseEnd_679048 := by
    simpa [prefixWord, tailWord_679048, baseEnd_679048] using wordTrace_append hprefix tailTrace_679048
  have hstable : (prefixWord ++ tailWord_679048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679048).length < 2 ^ (prefixWord ++ tailWord_679048).sum := by decide
  have hdescent : baseEnd_679048 < baseStart_679048 := by decide
  rcases family_descends (prefixWord ++ tailWord_679048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679110 : List Nat := [6, 1, 2, 2, 1, 1, 1, 2, 2, 4]
def baseStart_679110 : Nat := 118140960795 + 679110 * 2 ^ 59
def prefixEnd_679110 : Nat := 4983230072969 + 3 ^ 40 * 679110 * 2
def baseEnd_679110 : Nat := 232473231516628808467891

theorem tailTrace_679110 : CollatzResearch.WordTrace tailWord_679110 prefixEnd_679110 232473231516628808467891 := by
  unfold tailWord_679110
  simp only [CollatzResearch.WordTrace]
  refine ⟨774036767803372737476587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16512784379805285066167189 774036767803372737476587)
  ·
    refine ⟨1161055151705059106214881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 774036767803372737476587 1161055151705059106214881)
    ·
      refine ⟨870791363778794329661161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1161055151705059106214881 870791363778794329661161)
      ·
        refine ⟨653093522834095747245871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 870791363778794329661161 653093522834095747245871)
        ·
          refine ⟨979640284251143620868807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 653093522834095747245871 979640284251143620868807)
          ·
            refine ⟨1469460426376715431303211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 979640284251143620868807 1469460426376715431303211)
            ·
              refine ⟨2204190639565073146954817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1469460426376715431303211 2204190639565073146954817)
              ·
                refine ⟨1653142979673804860216113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2204190639565073146954817 1653142979673804860216113)
                ·
                  refine ⟨1239857234755353645162085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1653142979673804860216113 1239857234755353645162085)
                  ·
                    refine ⟨232473231516628808467891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1239857234755353645162085 232473231516628808467891)
                    ·
                      rfl

theorem cell22_679110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_679110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_679110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_679110 prefixEnd_679110 := by exact prefixLift 679110
  have htrace : WordTrace (prefixWord ++ tailWord_679110) baseStart_679110 baseEnd_679110 := by
    simpa [prefixWord, tailWord_679110, baseEnd_679110] using wordTrace_append hprefix tailTrace_679110
  have hstable : (prefixWord ++ tailWord_679110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679110).length < 2 ^ (prefixWord ++ tailWord_679110).sum := by decide
  have hdescent : baseEnd_679110 < baseStart_679110 := by decide
  rcases family_descends (prefixWord ++ tailWord_679110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679136 : List Nat := [2, 1, 1, 3, 1, 6, 2, 1, 5]
def baseStart_679136 : Nat := 118140960795 + 679136 * 2 ^ 59
def prefixEnd_679136 : Nat := 4983230072969 + 3 ^ 40 * 679136 * 2
def baseEnd_679136 : Nat := 77494043949324469105937

theorem tailTrace_679136 : CollatzResearch.WordTrace tailWord_679136 prefixEnd_679136 77494043949324469105937 := by
  unfold tailWord_679136
  simp only [CollatzResearch.WordTrace]
  refine ⟨12385062433806867019848631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16513416578409156026464841 12385062433806867019848631)
  ·
    refine ⟨18577593650710300529772947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12385062433806867019848631 18577593650710300529772947)
    ·
      refine ⟨27866390476065450794659421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18577593650710300529772947 27866390476065450794659421)
      ·
        refine ⟨10449896428524544047997283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27866390476065450794659421 10449896428524544047997283)
        ·
          refine ⟨15674844642786816071995925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10449896428524544047997283 15674844642786816071995925)
          ·
            refine ⟨734758342630632003374809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15674844642786816071995925 734758342630632003374809)
            ·
              refine ⟨551068756972974002531107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 734758342630632003374809 551068756972974002531107)
              ·
                refine ⟨826603135459461003796661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 551068756972974002531107 826603135459461003796661)
                ·
                  refine ⟨77494043949324469105937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 826603135459461003796661 77494043949324469105937)
                  ·
                    rfl

theorem cell22_679136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 5].length) (baseStart_679136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_679136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_679136 prefixEnd_679136 := by exact prefixLift 679136
  have htrace : WordTrace (prefixWord ++ tailWord_679136) baseStart_679136 baseEnd_679136 := by
    simpa [prefixWord, tailWord_679136, baseEnd_679136] using wordTrace_append hprefix tailTrace_679136
  have hstable : (prefixWord ++ tailWord_679136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679136).length < 2 ^ (prefixWord ++ tailWord_679136).sum := by decide
  have hdescent : baseEnd_679136 < baseStart_679136 := by decide
  rcases family_descends (prefixWord ++ tailWord_679136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679196 : List Nat := [2, 2, 3, 1, 1, 1, 4, 3, 2, 3]
def baseStart_679196 : Nat := 118140960795 + 679196 * 2 ^ 59
def prefixEnd_679196 : Nat := 4983230072969 + 3 ^ 40 * 679196 * 2
def baseEnd_679196 : Nat := 232502671074153250817627

theorem tailTrace_679196 : CollatzResearch.WordTrace tailWord_679196 prefixEnd_679196 232502671074153250817627 := by
  unfold tailWord_679196
  simp only [CollatzResearch.WordTrace]
  refine ⟨12386156623698182143440721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16514875498264242857920961 12386156623698182143440721)
  ·
    refine ⟨9289617467773636607580541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12386156623698182143440721 9289617467773636607580541)
    ·
      refine ⟨3483606550415113727842703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9289617467773636607580541 3483606550415113727842703)
      ·
        refine ⟨5225409825622670591764055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3483606550415113727842703 5225409825622670591764055)
        ·
          refine ⟨7838114738434005887646083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5225409825622670591764055 7838114738434005887646083)
          ·
            refine ⟨11757172107651008831469125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7838114738434005887646083 11757172107651008831469125)
            ·
              refine ⟨2204469770184564155900461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11757172107651008831469125 2204469770184564155900461)
              ·
                refine ⟨826676163819211558462673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2204469770184564155900461 826676163819211558462673)
                ·
                  refine ⟨620007122864408668847005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 826676163819211558462673 620007122864408668847005)
                  ·
                    refine ⟨232502671074153250817627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 620007122864408668847005 232502671074153250817627)
                    ·
                      rfl

theorem cell22_679196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_679196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_679196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_679196 prefixEnd_679196 := by exact prefixLift 679196
  have htrace : WordTrace (prefixWord ++ tailWord_679196) baseStart_679196 baseEnd_679196 := by
    simpa [prefixWord, tailWord_679196, baseEnd_679196] using wordTrace_append hprefix tailTrace_679196
  have hstable : (prefixWord ++ tailWord_679196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679196).length < 2 ^ (prefixWord ++ tailWord_679196).sum := by decide
  have hdescent : baseEnd_679196 < baseStart_679196 := by decide
  rcases family_descends (prefixWord ++ tailWord_679196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679198 : List Nat := [4, 3, 2, 1, 2, 1, 1, 2, 6]
def baseStart_679198 : Nat := 118140960795 + 679198 * 2 ^ 59
def prefixEnd_679198 : Nat := 4983230072969 + 3 ^ 40 * 679198 * 2
def baseEnd_679198 : Nat := 77501118571675304089207

theorem tailTrace_679198 : CollatzResearch.WordTrace tailWord_679198 prefixEnd_679198 77501118571675304089207 := by
  unfold tailWord_679198
  simp only [CollatzResearch.WordTrace]
  refine ⟨3096548274173639828556781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16514924128926079085636165 3096548274173639828556781)
  ·
    refine ⟨1161205602815114935708793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3096548274173639828556781 1161205602815114935708793)
    ·
      refine ⟨870904202111336201781595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1161205602815114935708793 870904202111336201781595)
      ·
        refine ⟨1306356303167004302672393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 870904202111336201781595 1306356303167004302672393)
        ·
          refine ⟨979767227375253227004295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1306356303167004302672393 979767227375253227004295)
          ·
            refine ⟨1469650841062879840506443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 979767227375253227004295 1469650841062879840506443)
            ·
              refine ⟨2204476261594319760759665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1469650841062879840506443 2204476261594319760759665)
              ·
                refine ⟨1653357196195739820569749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2204476261594319760759665 1653357196195739820569749)
                ·
                  refine ⟨77501118571675304089207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1653357196195739820569749 77501118571675304089207)
                  ·
                    rfl

theorem cell22_679198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_679198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_679198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_679198 prefixEnd_679198 := by exact prefixLift 679198
  have htrace : WordTrace (prefixWord ++ tailWord_679198) baseStart_679198 baseEnd_679198 := by
    simpa [prefixWord, tailWord_679198, baseEnd_679198] using wordTrace_append hprefix tailTrace_679198
  have hstable : (prefixWord ++ tailWord_679198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679198).length < 2 ^ (prefixWord ++ tailWord_679198).sum := by decide
  have hdescent : baseEnd_679198 < baseStart_679198 := by decide
  rcases family_descends (prefixWord ++ tailWord_679198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679224 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 7, 3]
def baseStart_679224 : Nat := 118140960795 + 679224 * 2 ^ 59
def prefixEnd_679224 : Nat := 4983230072969 + 3 ^ 40 * 679224 * 2
def baseEnd_679224 : Nat := 232512256046370511117541

theorem tailTrace_679224 : CollatzResearch.WordTrace tailWord_679224 prefixEnd_679224 232512256046370511117541 := by
  unfold tailWord_679224
  simp only [CollatzResearch.WordTrace]
  refine ⟨12386667245647462534450363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16515556327529950045933817 12386667245647462534450363)
  ·
    refine ⟨18580000868471193801675545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12386667245647462534450363 18580000868471193801675545)
    ·
      refine ⟨13935000651353395351256659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18580000868471193801675545 13935000651353395351256659)
      ·
        refine ⟨20902500977030093026884989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13935000651353395351256659 20902500977030093026884989)
        ·
          refine ⟨7838437866386284885081871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20902500977030093026884989 7838437866386284885081871)
          ·
            refine ⟨11757656799579427327622807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7838437866386284885081871 11757656799579427327622807)
            ·
              refine ⟨17636485199369140991434211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11757656799579427327622807 17636485199369140991434211)
              ·
                refine ⟨26454727799053711487151317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17636485199369140991434211 26454727799053711487151317)
                ·
                  refine ⟨620032682790321362980109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 26454727799053711487151317 620032682790321362980109)
                  ·
                    refine ⟨232512256046370511117541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 620032682790321362980109 232512256046370511117541)
                    ·
                      rfl

theorem cell22_679224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 7, 3].length) (baseStart_679224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_679224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_679224 prefixEnd_679224 := by exact prefixLift 679224
  have htrace : WordTrace (prefixWord ++ tailWord_679224) baseStart_679224 baseEnd_679224 := by
    simpa [prefixWord, tailWord_679224, baseEnd_679224] using wordTrace_append hprefix tailTrace_679224
  have hstable : (prefixWord ++ tailWord_679224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679224).length < 2 ^ (prefixWord ++ tailWord_679224).sum := by decide
  have hdescent : baseEnd_679224 < baseStart_679224 := by decide
  rcases family_descends (prefixWord ++ tailWord_679224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679305 : List Nat := [1, 2, 1, 1, 8, 1, 2, 1, 5]
def baseStart_679305 : Nat := 118140960795 + 679305 * 2 ^ 59
def prefixEnd_679305 : Nat := 4983230072969 + 3 ^ 40 * 679305 * 2
def baseEnd_679305 : Nat := 77513328000571099947431

theorem tailTrace_679305 : CollatzResearch.WordTrace tailWord_679305 prefixEnd_679305 77513328000571099947431 := by
  unfold tailWord_679305
  simp only [CollatzResearch.WordTrace]
  refine ⟨24776288804001475902599369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16517525869334317268399579 24776288804001475902599369)
  ·
    refine ⟨18582216603001106926949527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24776288804001475902599369 18582216603001106926949527)
    ·
      refine ⟨27873324904501660390424291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18582216603001106926949527 27873324904501660390424291)
      ·
        refine ⟨41809987356752490585636437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27873324904501660390424291 41809987356752490585636437)
        ·
          refine ⟨489960789336943249050427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 41809987356752490585636437 489960789336943249050427)
          ·
            refine ⟨734941184005414873575641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489960789336943249050427 734941184005414873575641)
            ·
              refine ⟨551205888004061155181731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 734941184005414873575641 551205888004061155181731)
              ·
                refine ⟨826808832006091732772597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 551205888004061155181731 826808832006091732772597)
                ·
                  refine ⟨77513328000571099947431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 826808832006091732772597 77513328000571099947431)
                  ·
                    rfl

theorem cell22_679305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 5].length) (baseStart_679305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_679305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_679305 prefixEnd_679305 := by exact prefixLift 679305
  have htrace : WordTrace (prefixWord ++ tailWord_679305) baseStart_679305 baseEnd_679305 := by
    simpa [prefixWord, tailWord_679305, baseEnd_679305] using wordTrace_append hprefix tailTrace_679305
  have hstable : (prefixWord ++ tailWord_679305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679305).length < 2 ^ (prefixWord ++ tailWord_679305).sum := by decide
  have hdescent : baseEnd_679305 < baseStart_679305 := by decide
  rcases family_descends (prefixWord ++ tailWord_679305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679376 : List Nat := [2, 1, 1, 1, 1, 2, 2, 6, 3, 3]
def baseStart_679376 : Nat := 118140960795 + 679376 * 2 ^ 59
def prefixEnd_679376 : Nat := 4983230072969 + 3 ^ 40 * 679376 * 2
def baseEnd_679376 : Nat := 232564288752692781317075

theorem tailTrace_679376 : CollatzResearch.WordTrace tailWord_679376 prefixEnd_679376 232564288752692781317075 := by
  unfold tailWord_679376
  simp only [CollatzResearch.WordTrace]
  refine ⟨12389439193372127514216991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16519252257829503352289321 12389439193372127514216991)
  ·
    refine ⟨18584158790058191271325487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12389439193372127514216991 18584158790058191271325487)
    ·
      refine ⟨27876238185087286906988231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18584158790058191271325487 27876238185087286906988231)
      ·
        refine ⟨41814357277630930360482347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27876238185087286906988231 41814357277630930360482347)
        ·
          refine ⟨62721535916446395540723521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41814357277630930360482347 62721535916446395540723521)
          ·
            refine ⟨47041151937334796655542641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62721535916446395540723521 47041151937334796655542641)
            ·
              refine ⟨35280863953001097491656981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47041151937334796655542641 35280863953001097491656981)
              ·
                refine ⟨1653790497796926444921421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35280863953001097491656981 1653790497796926444921421)
                ·
                  refine ⟨620171436673847416845533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1653790497796926444921421 620171436673847416845533)
                  ·
                    refine ⟨232564288752692781317075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 620171436673847416845533 232564288752692781317075)
                    ·
                      rfl

theorem cell22_679376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 3, 3].length) (baseStart_679376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_679376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_679376 prefixEnd_679376 := by exact prefixLift 679376
  have htrace : WordTrace (prefixWord ++ tailWord_679376) baseStart_679376 baseEnd_679376 := by
    simpa [prefixWord, tailWord_679376, baseEnd_679376] using wordTrace_append hprefix tailTrace_679376
  have hstable : (prefixWord ++ tailWord_679376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679376).length < 2 ^ (prefixWord ++ tailWord_679376).sum := by decide
  have hdescent : baseEnd_679376 < baseStart_679376 := by decide
  rcases family_descends (prefixWord ++ tailWord_679376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679380 : List Nat := [2, 4, 1, 2, 3, 2, 1, 1, 2, 4]
def baseStart_679380 : Nat := 118140960795 + 679380 * 2 ^ 59
def prefixEnd_679380 : Nat := 4983230072969 + 3 ^ 40 * 679380 * 2
def baseEnd_679380 : Nat := 232565658034438104217063

theorem tailTrace_679380 : CollatzResearch.WordTrace tailWord_679380 prefixEnd_679380 232565658034438104217063 := by
  unfold tailWord_679380
  simp only [CollatzResearch.WordTrace]
  refine ⟨12389512139364881855789797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16519349519153175807719729 12389512139364881855789797)
  ·
    refine ⟨2323033526130915347960587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12389512139364881855789797 2323033526130915347960587)
    ·
      refine ⟨3484550289196373021940881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2323033526130915347960587 3484550289196373021940881)
      ·
        refine ⟨2613412716897279766455661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3484550289196373021940881 2613412716897279766455661)
        ·
          refine ⟨980029768836479912420873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2613412716897279766455661 980029768836479912420873)
          ·
            refine ⟨735022326627359934315655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 980029768836479912420873 735022326627359934315655)
            ·
              refine ⟨1102533489941039901473483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 735022326627359934315655 1102533489941039901473483)
              ·
                refine ⟨1653800234911559852210225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1102533489941039901473483 1653800234911559852210225)
                ·
                  refine ⟨1240350176183669889157669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1653800234911559852210225 1240350176183669889157669)
                  ·
                    refine ⟨232565658034438104217063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1240350176183669889157669 232565658034438104217063)
                    ·
                      rfl

theorem cell22_679380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_679380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_679380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_679380 prefixEnd_679380 := by exact prefixLift 679380
  have htrace : WordTrace (prefixWord ++ tailWord_679380) baseStart_679380 baseEnd_679380 := by
    simpa [prefixWord, tailWord_679380, baseEnd_679380] using wordTrace_append hprefix tailTrace_679380
  have hstable : (prefixWord ++ tailWord_679380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679380).length < 2 ^ (prefixWord ++ tailWord_679380).sum := by decide
  have hdescent : baseEnd_679380 < baseStart_679380 := by decide
  rcases family_descends (prefixWord ++ tailWord_679380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679406 : List Nat := [4, 1, 2, 1, 2, 1, 3, 1, 7]
def baseStart_679406 : Nat := 118140960795 + 679406 * 2 ^ 59
def prefixEnd_679406 : Nat := 4983230072969 + 3 ^ 40 * 679406 * 2
def baseEnd_679406 : Nat := 77524852788594234355661

theorem tailTrace_679406 : CollatzResearch.WordTrace tailWord_679406 prefixEnd_679406 77524852788594234355661 := by
  unfold tailWord_679406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3097496572079446269003259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16519981717757046768017381 3097496572079446269003259)
  ·
    refine ⟨4646244858119169403504889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3097496572079446269003259 4646244858119169403504889)
    ·
      refine ⟨3484683643589377052628667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4646244858119169403504889 3484683643589377052628667)
      ·
        refine ⟨5227025465384065578943001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3484683643589377052628667 5227025465384065578943001)
        ·
          refine ⟨3920269099038049184207251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5227025465384065578943001 3920269099038049184207251)
          ·
            refine ⟨5880403648557073776310877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3920269099038049184207251 5880403648557073776310877)
            ·
              refine ⟨2205151368208902666116579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5880403648557073776310877 2205151368208902666116579)
              ·
                refine ⟨3307727052313353999174869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2205151368208902666116579 3307727052313353999174869)
                ·
                  refine ⟨77524852788594234355661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3307727052313353999174869 77524852788594234355661)
                  ·
                    rfl

theorem cell22_679406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_679406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_679406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_679406 prefixEnd_679406 := by exact prefixLift 679406
  have htrace : WordTrace (prefixWord ++ tailWord_679406) baseStart_679406 baseEnd_679406 := by
    simpa [prefixWord, tailWord_679406, baseEnd_679406] using wordTrace_append hprefix tailTrace_679406
  have hstable : (prefixWord ++ tailWord_679406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679406).length < 2 ^ (prefixWord ++ tailWord_679406).sum := by decide
  have hdescent : baseEnd_679406 < baseStart_679406 := by decide
  rcases family_descends (prefixWord ++ tailWord_679406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679410 : List Nat := [3, 2, 1, 4, 1, 2, 2, 1, 3, 3]
def baseStart_679410 : Nat := 118140960795 + 679410 * 2 ^ 59
def prefixEnd_679410 : Nat := 4983230072969 + 3 ^ 40 * 679410 * 2
def baseEnd_679410 : Nat := 232575927647528025966971

theorem tailTrace_679410 : CollatzResearch.WordTrace tailWord_679410 prefixEnd_679410 232575927647528025966971 := by
  unfold tailWord_679410
  simp only [CollatzResearch.WordTrace]
  refine ⟨6195029617155269708792921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16520078979080719223447789 6195029617155269708792921)
  ·
    refine ⟨4646272212866452281594691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6195029617155269708792921 4646272212866452281594691)
    ·
      refine ⟨6969408319299678422392037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4646272212866452281594691 6969408319299678422392037)
      ·
        refine ⟨1306764059868689704198507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6969408319299678422392037 1306764059868689704198507)
        ·
          refine ⟨1960146089803034556297761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1306764059868689704198507 1960146089803034556297761)
          ·
            refine ⟨1470109567352275917223321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1960146089803034556297761 1470109567352275917223321)
            ·
              refine ⟨1102582175514206937917491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1470109567352275917223321 1102582175514206937917491)
              ·
                refine ⟨1653873263271310406876237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1102582175514206937917491 1653873263271310406876237)
                ·
                  refine ⟨620202473726741402578589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1653873263271310406876237 620202473726741402578589)
                  ·
                    refine ⟨232575927647528025966971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 620202473726741402578589 232575927647528025966971)
                    ·
                      rfl

theorem cell22_679410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_679410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_679410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_679410 prefixEnd_679410 := by exact prefixLift 679410
  have htrace : WordTrace (prefixWord ++ tailWord_679410) baseStart_679410 baseEnd_679410 := by
    simpa [prefixWord, tailWord_679410, baseEnd_679410] using wordTrace_append hprefix tailTrace_679410
  have hstable : (prefixWord ++ tailWord_679410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679410).length < 2 ^ (prefixWord ++ tailWord_679410).sum := by decide
  have hdescent : baseEnd_679410 < baseStart_679410 := by decide
  rcases family_descends (prefixWord ++ tailWord_679410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679421 : List Nat := [1, 4, 1, 1, 1, 4, 2, 1, 2, 5]
def baseStart_679421 : Nat := 118140960795 + 679421 * 2 ^ 59
def prefixEnd_679421 : Nat := 4983230072969 + 3 ^ 40 * 679421 * 2
def baseEnd_679421 : Nat := 232579693172327663941937

theorem tailTrace_679421 : CollatzResearch.WordTrace tailWord_679421 prefixEnd_679421 232579693172327663941937 := by
  unfold tailWord_679421
  simp only [CollatzResearch.WordTrace]
  refine ⟨24780519671581227713822117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16520346447720818475881411 24780519671581227713822117)
  ·
    refine ⟨4646347438421480196341647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24780519671581227713822117 4646347438421480196341647)
    ·
      refine ⟨6969521157632220294512471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4646347438421480196341647 6969521157632220294512471)
      ·
        refine ⟨10454281736448330441768707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6969521157632220294512471 10454281736448330441768707)
        ·
          refine ⟨15681422604672495662653061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10454281736448330441768707 15681422604672495662653061)
          ·
            refine ⟨2940266738376092936747449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15681422604672495662653061 2940266738376092936747449)
            ·
              refine ⟨2205200053782069702560587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2940266738376092936747449 2205200053782069702560587)
              ·
                refine ⟨3307800080673104553840881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2205200053782069702560587 3307800080673104553840881)
                ·
                  refine ⟨2480850060504828415380661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3307800080673104553840881 2480850060504828415380661)
                  ·
                    refine ⟨232579693172327663941937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2480850060504828415380661 232579693172327663941937)
                    ·
                      rfl

theorem cell22_679421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_679421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_679421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_679421 prefixEnd_679421 := by exact prefixLift 679421
  have htrace : WordTrace (prefixWord ++ tailWord_679421) baseStart_679421 baseEnd_679421 := by
    simpa [prefixWord, tailWord_679421, baseEnd_679421] using wordTrace_append hprefix tailTrace_679421
  have hstable : (prefixWord ++ tailWord_679421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679421).length < 2 ^ (prefixWord ++ tailWord_679421).sum := by decide
  have hdescent : baseEnd_679421 < baseStart_679421 := by decide
  rcases family_descends (prefixWord ++ tailWord_679421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679453 : List Nat := [1, 4, 2, 2, 1, 1, 1, 5, 1, 4]
def baseStart_679453 : Nat := 118140960795 + 679453 * 2 ^ 59
def prefixEnd_679453 : Nat := 4983230072969 + 3 ^ 40 * 679453 * 2
def baseEnd_679453 : Nat := 232590647426290247141839

theorem tailTrace_679453 : CollatzResearch.WordTrace tailWord_679453 prefixEnd_679453 232590647426290247141839 := by
  unfold tailWord_679453
  simp only [CollatzResearch.WordTrace]
  refine ⟨24781686807465297178987013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16521124538310198119324675 24781686807465297178987013)
  ·
    refine ⟨4646566276399743221060065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24781686807465297178987013 4646566276399743221060065)
    ·
      refine ⟨3484924707299807415795049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4646566276399743221060065 3484924707299807415795049)
      ·
        refine ⟨2613693530474855561846287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3484924707299807415795049 2613693530474855561846287)
        ·
          refine ⟨3920540295712283342769431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2613693530474855561846287 3920540295712283342769431)
          ·
            refine ⟨5880810443568425014154147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3920540295712283342769431 5880810443568425014154147)
            ·
              refine ⟨8821215665352637521231221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5880810443568425014154147 8821215665352637521231221)
              ·
                refine ⟨826988968626809767615427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8821215665352637521231221 826988968626809767615427)
                ·
                  refine ⟨1240483452940214651423141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 826988968626809767615427 1240483452940214651423141)
                  ·
                    refine ⟨232590647426290247141839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1240483452940214651423141 232590647426290247141839)
                    ·
                      rfl

theorem cell22_679453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_679453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_679453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_679453 prefixEnd_679453 := by exact prefixLift 679453
  have htrace : WordTrace (prefixWord ++ tailWord_679453) baseStart_679453 baseEnd_679453 := by
    simpa [prefixWord, tailWord_679453, baseEnd_679453] using wordTrace_append hprefix tailTrace_679453
  have hstable : (prefixWord ++ tailWord_679453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679453).length < 2 ^ (prefixWord ++ tailWord_679453).sum := by decide
  have hdescent : baseEnd_679453 < baseStart_679453 := by decide
  rcases family_descends (prefixWord ++ tailWord_679453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679498 : List Nat := [3, 1, 2, 1, 1, 3, 4, 1, 2, 4]
def baseStart_679498 : Nat := 118140960795 + 679498 * 2 ^ 59
def prefixEnd_679498 : Nat := 4983230072969 + 3 ^ 40 * 679498 * 2
def baseEnd_679498 : Nat := 232606051845925129766701

theorem tailTrace_679498 : CollatzResearch.WordTrace tailWord_679498 prefixEnd_679498 232606051845925129766701 := by
  unfold tailWord_679498
  simp only [CollatzResearch.WordTrace]
  refine ⟨6195832023075567466093787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16522218728201513242916765 6195832023075567466093787)
  ·
    refine ⟨9293748034613351199140681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6195832023075567466093787 9293748034613351199140681)
    ·
      refine ⟨6970311025960013399355511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9293748034613351199140681 6970311025960013399355511)
      ·
        refine ⟨10455466538940020099033267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6970311025960013399355511 10455466538940020099033267)
        ·
          refine ⟨15683199808410030148549901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10455466538940020099033267 15683199808410030148549901)
          ·
            refine ⟨5881199928153761305706213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15683199808410030148549901 5881199928153761305706213)
            ·
              refine ⟨1102724986528830244819915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5881199928153761305706213 1102724986528830244819915)
              ·
                refine ⟨1654087479793245367229873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1102724986528830244819915 1654087479793245367229873)
                ·
                  refine ⟨1240565609844934025422405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1654087479793245367229873 1240565609844934025422405)
                  ·
                    refine ⟨232606051845925129766701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1240565609844934025422405 232606051845925129766701)
                    ·
                      rfl

theorem cell22_679498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_679498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_679498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_679498 prefixEnd_679498 := by exact prefixLift 679498
  have htrace : WordTrace (prefixWord ++ tailWord_679498) baseStart_679498 baseEnd_679498 := by
    simpa [prefixWord, tailWord_679498, baseEnd_679498] using wordTrace_append hprefix tailTrace_679498
  have hstable : (prefixWord ++ tailWord_679498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679498).length < 2 ^ (prefixWord ++ tailWord_679498).sum := by decide
  have hdescent : baseEnd_679498 < baseStart_679498 := by decide
  rcases family_descends (prefixWord ++ tailWord_679498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679562 : List Nat := [3, 1, 2, 3, 2, 1, 1, 5, 1, 3]
def baseStart_679562 : Nat := 118140960795 + 679562 * 2 ^ 59
def prefixEnd_679562 : Nat := 4983230072969 + 3 ^ 40 * 679562 * 2
def baseEnd_679562 : Nat := 232627960353850296166505

theorem tailTrace_679562 : CollatzResearch.WordTrace tailWord_679562 prefixEnd_679562 232627960353850296166505 := by
  unfold tailWord_679562
  simp only [CollatzResearch.WordTrace]
  refine ⟨6196415591017602198676235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16523774909380272529803293 6196415591017602198676235)
  ·
    refine ⟨9294623386526403298014353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6196415591017602198676235 9294623386526403298014353)
    ·
      refine ⟨6970967539894802473510765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9294623386526403298014353 6970967539894802473510765)
      ·
        refine ⟨2614112827460550927566537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6970967539894802473510765 2614112827460550927566537)
        ·
          refine ⟨1960584620595413195674903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2614112827460550927566537 1960584620595413195674903)
          ·
            refine ⟨2940876930893119793512355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1960584620595413195674903 2940876930893119793512355)
            ·
              refine ⟨4411315396339679690268533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2940876930893119793512355 4411315396339679690268533)
              ·
                refine ⟨413560818406844970962675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4411315396339679690268533 413560818406844970962675)
                ·
                  refine ⟨620341227610267456444013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 413560818406844970962675 620341227610267456444013)
                  ·
                    refine ⟨232627960353850296166505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 620341227610267456444013 232627960353850296166505)
                    ·
                      rfl

theorem cell22_679562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_679562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_679562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_679562 prefixEnd_679562 := by exact prefixLift 679562
  have htrace : WordTrace (prefixWord ++ tailWord_679562) baseStart_679562 baseEnd_679562 := by
    simpa [prefixWord, tailWord_679562, baseEnd_679562] using wordTrace_append hprefix tailTrace_679562
  have hstable : (prefixWord ++ tailWord_679562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679562).length < 2 ^ (prefixWord ++ tailWord_679562).sum := by decide
  have hdescent : baseEnd_679562 < baseStart_679562 := by decide
  rcases family_descends (prefixWord ++ tailWord_679562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679575 : List Nat := [1, 1, 3, 3, 2, 4, 1, 2, 5]
def baseStart_679575 : Nat := 118140960795 + 679575 * 2 ^ 59
def prefixEnd_679575 : Nat := 4983230072969 + 3 ^ 40 * 679575 * 2
def baseEnd_679575 : Nat := 77544136839840865197155

theorem tailTrace_679575 : CollatzResearch.WordTrace tailWord_679575 prefixEnd_679575 77544136839840865197155 := by
  unfold tailWord_679575
  simp only [CollatzResearch.WordTrace]
  refine ⟨24786136513023312014928179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16524091008682208009952119 24786136513023312014928179)
  ·
    refine ⟨37179204769534968022392269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24786136513023312014928179 37179204769534968022392269)
    ·
      refine ⟨13942201788575613008397101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37179204769534968022392269 13942201788575613008397101)
      ·
        refine ⟨5228325670715854878148913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13942201788575613008397101 5228325670715854878148913)
        ·
          refine ⟨3921244253036891158611685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5228325670715854878148913 3921244253036891158611685)
          ·
            refine ⟨735233297444417092239691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3921244253036891158611685 735233297444417092239691)
            ·
              refine ⟨1102849946166625638359537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 735233297444417092239691 1102849946166625638359537)
              ·
                refine ⟨827137459624969228769653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1102849946166625638359537 827137459624969228769653)
                ·
                  refine ⟨77544136839840865197155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 827137459624969228769653 77544136839840865197155)
                  ·
                    rfl

theorem cell22_679575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 5].length) (baseStart_679575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_679575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_679575 prefixEnd_679575 := by exact prefixLift 679575
  have htrace : WordTrace (prefixWord ++ tailWord_679575) baseStart_679575 baseEnd_679575 := by
    simpa [prefixWord, tailWord_679575, baseEnd_679575] using wordTrace_append hprefix tailTrace_679575
  have hstable : (prefixWord ++ tailWord_679575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679575).length < 2 ^ (prefixWord ++ tailWord_679575).sum := by decide
  have hdescent : baseEnd_679575 < baseStart_679575 := by decide
  rcases family_descends (prefixWord ++ tailWord_679575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679633 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 4, 4]
def baseStart_679633 : Nat := 118140960795 + 679633 * 2 ^ 59
def prefixEnd_679633 : Nat := 4983230072969 + 3 ^ 40 * 679633 * 2
def baseEnd_679633 : Nat := 232652265104829777641287

theorem tailTrace_679633 : CollatzResearch.WordTrace tailWord_679633 prefixEnd_679633 232652265104829777641287 := by
  unfold tailWord_679633
  simp only [CollatzResearch.WordTrace]
  refine ⟨24788251946813187920539553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16525501297875458613693035 24788251946813187920539553)
  ·
    refine ⟨18591188960109890940404665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24788251946813187920539553 18591188960109890940404665)
    ·
      refine ⟨13943391720082418205303499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18591188960109890940404665 13943391720082418205303499)
      ·
        refine ⟨20915087580123627307955249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13943391720082418205303499 20915087580123627307955249)
        ·
          refine ⟨15686315685092720480966437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20915087580123627307955249 15686315685092720480966437)
          ·
            refine ⟨2941184190954885090181207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15686315685092720480966437 2941184190954885090181207)
            ·
              refine ⟨4411776286432327635271811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2941184190954885090181207 4411776286432327635271811)
              ·
                refine ⟨6617664429648491452907717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4411776286432327635271811 6617664429648491452907717)
                ·
                  refine ⟨1240812080559092147420197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6617664429648491452907717 1240812080559092147420197)
                  ·
                    refine ⟨232652265104829777641287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1240812080559092147420197 232652265104829777641287)
                    ·
                      rfl

theorem cell22_679633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_679633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_679633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_679633 prefixEnd_679633 := by exact prefixLift 679633
  have htrace : WordTrace (prefixWord ++ tailWord_679633) baseStart_679633 baseEnd_679633 := by
    simpa [prefixWord, tailWord_679633, baseEnd_679633] using wordTrace_append hprefix tailTrace_679633
  have hstable : (prefixWord ++ tailWord_679633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679633).length < 2 ^ (prefixWord ++ tailWord_679633).sum := by decide
  have hdescent : baseEnd_679633 < baseStart_679633 := by decide
  rcases family_descends (prefixWord ++ tailWord_679633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679723 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 7, 4]
def baseStart_679723 : Nat := 118140960795 + 679723 * 2 ^ 59
def prefixEnd_679723 : Nat := 4983230072969 + 3 ^ 40 * 679723 * 2
def baseEnd_679723 : Nat := 232683073944099542891011

theorem tailTrace_679723 : CollatzResearch.WordTrace tailWord_679723 prefixEnd_679723 232683073944099542891011 := by
  unfold tailWord_679723
  simp only [CollatzResearch.WordTrace]
  refine ⟨24791534516487133291315823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16527689677658088860877215 24791534516487133291315823)
  ·
    refine ⟨37187301774730699936973735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24791534516487133291315823 37187301774730699936973735)
    ·
      refine ⟨55780952662096049905460603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37187301774730699936973735 55780952662096049905460603)
      ·
        refine ⟨83671428993144074858190905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55780952662096049905460603 83671428993144074858190905)
        ·
          refine ⟨62753571744858056143643179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83671428993144074858190905 62753571744858056143643179)
          ·
            refine ⟨94130357617287084215464769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62753571744858056143643179 94130357617287084215464769)
            ·
              refine ⟨70597768212965313161598577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94130357617287084215464769 70597768212965313161598577)
              ·
                refine ⟨52948326159723984871198933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70597768212965313161598577 52948326159723984871198933)
                ·
                  refine ⟨1240976394368530895418725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 52948326159723984871198933 1240976394368530895418725)
                  ·
                    refine ⟨232683073944099542891011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1240976394368530895418725 232683073944099542891011)
                    ·
                      rfl

theorem cell22_679723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 4].length) (baseStart_679723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_679723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_679723 prefixEnd_679723 := by exact prefixLift 679723
  have htrace : WordTrace (prefixWord ++ tailWord_679723) baseStart_679723 baseEnd_679723 := by
    simpa [prefixWord, tailWord_679723, baseEnd_679723] using wordTrace_append hprefix tailTrace_679723
  have hstable : (prefixWord ++ tailWord_679723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679723).length < 2 ^ (prefixWord ++ tailWord_679723).sum := by decide
  have hdescent : baseEnd_679723 < baseStart_679723 := by decide
  rcases family_descends (prefixWord ++ tailWord_679723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679892 : List Nat := [2, 4, 1, 2, 1, 1, 1, 3, 3, 4]
def baseStart_679892 : Nat := 118140960795 + 679892 * 2 ^ 59
def prefixEnd_679892 : Nat := 4983230072969 + 3 ^ 40 * 679892 * 2
def baseEnd_679892 : Nat := 232740926097839435415493

theorem tailTrace_679892 : CollatzResearch.WordTrace tailWord_679892 prefixEnd_679892 232740926097839435415493 := by
  unfold tailWord_679892
  simp only [CollatzResearch.WordTrace]
  refine ⟨12398849226437437577108965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16531798968583250102811953 12398849226437437577108965)
  ·
    refine ⟨2324784229957019545707931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12398849226437437577108965 2324784229957019545707931)
    ·
      refine ⟨3487176344935529318561897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2324784229957019545707931 3487176344935529318561897)
      ·
        refine ⟨2615382258701646988921423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3487176344935529318561897 2615382258701646988921423)
        ·
          refine ⟨3923073388052470483382135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2615382258701646988921423 3923073388052470483382135)
          ·
            refine ⟨5884610082078705725073203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3923073388052470483382135 5884610082078705725073203)
            ·
              refine ⟨8826915123118058587609805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5884610082078705725073203 8826915123118058587609805)
              ·
                refine ⟨3310093171169271970353677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8826915123118058587609805 3310093171169271970353677)
                ·
                  refine ⟨1241284939188476988882629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3310093171169271970353677 1241284939188476988882629)
                  ·
                    refine ⟨232740926097839435415493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1241284939188476988882629 232740926097839435415493)
                    ·
                      rfl

theorem cell22_679892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_679892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_679892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_679892 prefixEnd_679892 := by exact prefixLift 679892
  have htrace : WordTrace (prefixWord ++ tailWord_679892) baseStart_679892 baseEnd_679892 := by
    simpa [prefixWord, tailWord_679892, baseEnd_679892] using wordTrace_append hprefix tailTrace_679892
  have hstable : (prefixWord ++ tailWord_679892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679892).length < 2 ^ (prefixWord ++ tailWord_679892).sum := by decide
  have hdescent : baseEnd_679892 < baseStart_679892 := by decide
  rcases family_descends (prefixWord ++ tailWord_679892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679969 : List Nat := [1, 2, 3, 2, 5, 1, 8]
def baseStart_679969 : Nat := 118140960795 + 679969 * 2 ^ 59
def prefixEnd_679969 : Nat := 4983230072969 + 3 ^ 40 * 679969 * 2
def baseEnd_679969 : Nat := 8621010547090255601491

theorem tailTrace_679969 : CollatzResearch.WordTrace tailWord_679969 prefixEnd_679969 8621010547090255601491 := by
  unfold tailWord_679969
  simp only [CollatzResearch.WordTrace]
  refine ⟨24800506873595917304770961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16533671249063944869847307 24800506873595917304770961)
  ·
    refine ⟨18600380155196937978578221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24800506873595917304770961 18600380155196937978578221)
    ·
      refine ⟨6975142558198851741966833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18600380155196937978578221 6975142558198851741966833)
      ·
        refine ⟨5231356918649138806475125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6975142558198851741966833 5231356918649138806475125)
        ·
          refine ⟨490439711123356763107043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5231356918649138806475125 490439711123356763107043)
          ·
            refine ⟨735659566685035144660565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490439711123356763107043 735659566685035144660565)
            ·
              refine ⟨8621010547090255601491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 735659566685035144660565 8621010547090255601491)
              ·
                rfl

theorem cell22_679969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 8].length) (baseStart_679969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_679969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_679969 prefixEnd_679969 := by exact prefixLift 679969
  have htrace : WordTrace (prefixWord ++ tailWord_679969) baseStart_679969 baseEnd_679969 := by
    simpa [prefixWord, tailWord_679969, baseEnd_679969] using wordTrace_append hprefix tailTrace_679969
  have hstable : (prefixWord ++ tailWord_679969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679969).length < 2 ^ (prefixWord ++ tailWord_679969).sum := by decide
  have hdescent : baseEnd_679969 < baseStart_679969 := by decide
  rcases family_descends (prefixWord ++ tailWord_679969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679984 : List Nat := [2, 1, 1, 1, 2, 5, 3, 1, 3, 3]
def baseStart_679984 : Nat := 118140960795 + 679984 * 2 ^ 59
def prefixEnd_679984 : Nat := 4983230072969 + 3 ^ 40 * 679984 * 2
def baseEnd_679984 : Nat := 232772419577981862115211

theorem tailTrace_679984 : CollatzResearch.WordTrace tailWord_679984 prefixEnd_679984 232772419577981862115211 := by
  unfold tailWord_679984
  simp only [CollatzResearch.WordTrace]
  refine ⟨12400526984270787433283503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16534035979027716577711337 12400526984270787433283503)
  ·
    refine ⟨18600790476406181149925255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12400526984270787433283503 18600790476406181149925255)
    ·
      refine ⟨27901185714609271724887883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18600790476406181149925255 27901185714609271724887883)
      ·
        refine ⟨41851778571913907587331825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27901185714609271724887883 41851778571913907587331825)
        ·
          refine ⟨31388833928935430690498869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41851778571913907587331825 31388833928935430690498869)
          ·
            refine ⟨2942703180837696627234269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31388833928935430690498869 2942703180837696627234269)
            ·
              refine ⟨1103513692814136235212851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2942703180837696627234269 1103513692814136235212851)
              ·
                refine ⟨1655270539221204352819277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1103513692814136235212851 1655270539221204352819277)
                ·
                  refine ⟨620726452207951632307229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1655270539221204352819277 620726452207951632307229)
                  ·
                    refine ⟨232772419577981862115211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 620726452207951632307229 232772419577981862115211)
                    ·
                      rfl

theorem cell22_679984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 3, 3].length) (baseStart_679984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_679984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_679984 prefixEnd_679984 := by exact prefixLift 679984
  have htrace : WordTrace (prefixWord ++ tailWord_679984) baseStart_679984 baseEnd_679984 := by
    simpa [prefixWord, tailWord_679984, baseEnd_679984] using wordTrace_append hprefix tailTrace_679984
  have hstable : (prefixWord ++ tailWord_679984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679984).length < 2 ^ (prefixWord ++ tailWord_679984).sum := by decide
  have hdescent : baseEnd_679984 < baseStart_679984 := by decide
  rcases family_descends (prefixWord ++ tailWord_679984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680074 : List Nat := [3, 1, 2, 3, 1, 2, 2, 2, 1, 5]
def baseStart_680074 : Nat := 118140960795 + 680074 * 2 ^ 59
def prefixEnd_680074 : Nat := 4983230072969 + 3 ^ 40 * 680074 * 2
def baseEnd_680074 : Nat := 232803228417251627364935

theorem tailTrace_680074 : CollatzResearch.WordTrace tailWord_680074 prefixEnd_680074 232803228417251627364935 := by
  unfold tailWord_680074
  simp only [CollatzResearch.WordTrace]
  refine ⟨6201084134553880059335819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16536224358810346824895517 6201084134553880059335819)
  ·
    refine ⟨9301626201830820089003729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6201084134553880059335819 9301626201830820089003729)
    ·
      refine ⟨6976219651373115066752797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9301626201830820089003729 6976219651373115066752797)
      ·
        refine ⟨2616082369264918150032299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6976219651373115066752797 2616082369264918150032299)
        ·
          refine ⟨3924123553897377225048449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2616082369264918150032299 3924123553897377225048449)
          ·
            refine ⟨2943092665423032918786337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3924123553897377225048449 2943092665423032918786337)
            ·
              refine ⟨2207319499067274689089753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2943092665423032918786337 2207319499067274689089753)
              ·
                refine ⟨1655489624300456016817315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2207319499067274689089753 1655489624300456016817315)
                ·
                  refine ⟨2483234436450684025225973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1655489624300456016817315 2483234436450684025225973)
                  ·
                    refine ⟨232803228417251627364935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2483234436450684025225973 232803228417251627364935)
                    ·
                      rfl

theorem cell22_680074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_680074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_680074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_680074 prefixEnd_680074 := by exact prefixLift 680074
  have htrace : WordTrace (prefixWord ++ tailWord_680074) baseStart_680074 baseEnd_680074 := by
    simpa [prefixWord, tailWord_680074, baseEnd_680074] using wordTrace_append hprefix tailTrace_680074
  have hstable : (prefixWord ++ tailWord_680074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680074).length < 2 ^ (prefixWord ++ tailWord_680074).sum := by decide
  have hdescent : baseEnd_680074 < baseStart_680074 := by decide
  rcases family_descends (prefixWord ++ tailWord_680074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680179 : List Nat := [1, 1, 1, 2, 2, 4, 3, 1, 3, 4]
def baseStart_680179 : Nat := 118140960795 + 680179 * 2 ^ 59
def prefixEnd_680179 : Nat := 4983230072969 + 3 ^ 40 * 680179 * 2
def baseEnd_680179 : Nat := 232839172063066353489613

theorem tailTrace_680179 : CollatzResearch.WordTrace tailWord_680179 prefixEnd_680179 232839172063066353489613 := by
  unfold tailWord_680179
  simp only [CollatzResearch.WordTrace]
  refine ⟨24808166202835123169915591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16538777468556748779943727 24808166202835123169915591)
  ·
    refine ⟨37212249304252684754873387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24808166202835123169915591 37212249304252684754873387)
    ·
      refine ⟨55818373956379027132310081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37212249304252684754873387 55818373956379027132310081)
      ·
        refine ⟨41863780467284270349232561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55818373956379027132310081 41863780467284270349232561)
        ·
          refine ⟨31397835350463202761924421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41863780467284270349232561 31397835350463202761924421)
          ·
            refine ⟨5887094128211850517860829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31397835350463202761924421 5887094128211850517860829)
            ·
              refine ⟨2207660298079443944197811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5887094128211850517860829 2207660298079443944197811)
              ·
                refine ⟨3311490447119165916296717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2207660298079443944197811 3311490447119165916296717)
                ·
                  refine ⟨1241808917669687218611269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3311490447119165916296717 1241808917669687218611269)
                  ·
                    refine ⟨232839172063066353489613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1241808917669687218611269 232839172063066353489613)
                    ·
                      rfl

theorem cell22_680179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 4].length) (baseStart_680179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_680179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_680179 prefixEnd_680179 := by exact prefixLift 680179
  have htrace : WordTrace (prefixWord ++ tailWord_680179) baseStart_680179 baseEnd_680179 := by
    simpa [prefixWord, tailWord_680179, baseEnd_680179] using wordTrace_append hprefix tailTrace_680179
  have hstable : (prefixWord ++ tailWord_680179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680179).length < 2 ^ (prefixWord ++ tailWord_680179).sum := by decide
  have hdescent : baseEnd_680179 < baseStart_680179 := by decide
  rcases family_descends (prefixWord ++ tailWord_680179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680226 : List Nat := [3, 3, 1, 1, 3, 1, 1, 3, 1, 5]
def baseStart_680226 : Nat := 118140960795 + 680226 * 2 ^ 59
def prefixEnd_680226 : Nat := 4983230072969 + 3 ^ 40 * 680226 * 2
def baseEnd_680226 : Nat := 232855261123573897564469

theorem tailTrace_680226 : CollatzResearch.WordTrace tailWord_680226 prefixEnd_680226 232855261123573897564469 := by
  unfold tailWord_680226
  simp only [CollatzResearch.WordTrace]
  refine ⟨6202470108416212549219133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16539920289109900131251021 6202470108416212549219133)
  ·
    refine ⟨2325926290656079705957175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6202470108416212549219133 2325926290656079705957175)
    ·
      refine ⟨3488889435984119558935763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2325926290656079705957175 3488889435984119558935763)
      ·
        refine ⟨5233334153976179338403645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3488889435984119558935763 5233334153976179338403645)
        ·
          refine ⟨1962500307741067251901367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5233334153976179338403645 1962500307741067251901367)
          ·
            refine ⟨2943750461611600877852051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1962500307741067251901367 2943750461611600877852051)
            ·
              refine ⟨4415625692417401316778077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2943750461611600877852051 4415625692417401316778077)
              ·
                refine ⟨1655859634656525493791779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4415625692417401316778077 1655859634656525493791779)
                ·
                  refine ⟨2483789451984788240687669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1655859634656525493791779 2483789451984788240687669)
                  ·
                    refine ⟨232855261123573897564469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2483789451984788240687669 232855261123573897564469)
                    ·
                      rfl

theorem cell22_680226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_680226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_680226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_680226 prefixEnd_680226 := by exact prefixLift 680226
  have htrace : WordTrace (prefixWord ++ tailWord_680226) baseStart_680226 baseEnd_680226 := by
    simpa [prefixWord, tailWord_680226, baseEnd_680226] using wordTrace_append hprefix tailTrace_680226
  have hstable : (prefixWord ++ tailWord_680226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680226).length < 2 ^ (prefixWord ++ tailWord_680226).sum := by decide
  have hdescent : baseEnd_680226 < baseStart_680226 := by decide
  rcases family_descends (prefixWord ++ tailWord_680226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680241 : List Nat := [1, 2, 2, 3, 4, 1, 1, 1, 1, 6]
def baseStart_680241 : Nat := 118140960795 + 680241 * 2 ^ 59
def prefixEnd_680241 : Nat := 4983230072969 + 3 ^ 40 * 680241 * 2
def baseEnd_680241 : Nat := 232860395930118858439423

theorem tailTrace_680241 : CollatzResearch.WordTrace tailWord_680241 prefixEnd_680241 232860395930118858439423 := by
  unfold tailWord_680241
  simp only [CollatzResearch.WordTrace]
  refine ⟨24810427528610507758672577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16540285019073671839115051 24810427528610507758672577)
  ·
    refine ⟨18607820646457880819004433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24810427528610507758672577 18607820646457880819004433)
    ·
      refine ⟨13955865484843410614253325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18607820646457880819004433 13955865484843410614253325)
      ·
        refine ⟨5233449556816278980344997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13955865484843410614253325 5233449556816278980344997)
        ·
          refine ⟨981271791903052308814687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5233449556816278980344997 981271791903052308814687)
          ·
            refine ⟨1471907687854578463222031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 981271791903052308814687 1471907687854578463222031)
            ·
              refine ⟨2207861531781867694833047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1471907687854578463222031 2207861531781867694833047)
              ·
                refine ⟨3311792297672801542249571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2207861531781867694833047 3311792297672801542249571)
                ·
                  refine ⟨4967688446509202313374357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3311792297672801542249571 4967688446509202313374357)
                  ·
                    refine ⟨232860395930118858439423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4967688446509202313374357 232860395930118858439423)
                    ·
                      rfl

theorem cell22_680241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_680241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_680241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_680241 prefixEnd_680241 := by exact prefixLift 680241
  have htrace : WordTrace (prefixWord ++ tailWord_680241) baseStart_680241 baseEnd_680241 := by
    simpa [prefixWord, tailWord_680241, baseEnd_680241] using wordTrace_append hprefix tailTrace_680241
  have hstable : (prefixWord ++ tailWord_680241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680241).length < 2 ^ (prefixWord ++ tailWord_680241).sum := by decide
  have hdescent : baseEnd_680241 < baseStart_680241 := by decide
  rcases family_descends (prefixWord ++ tailWord_680241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680260 : List Nat := [2, 3, 4, 1, 2, 1, 1, 1, 4, 3]
def baseStart_680260 : Nat := 118140960795 + 680260 * 2 ^ 59
def prefixEnd_680260 : Nat := 4983230072969 + 3 ^ 40 * 680260 * 2
def baseEnd_680260 : Nat := 232866900018409142214365

theorem tailTrace_680260 : CollatzResearch.WordTrace tailWord_680260 prefixEnd_680260 232866900018409142214365 := by
  unfold tailWord_680260
  simp only [CollatzResearch.WordTrace]
  refine ⟨12405560257770837001807117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16540747010361116002409489 12405560257770837001807117)
  ·
    refine ⟨4652085096664063875677669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12405560257770837001807117 4652085096664063875677669)
    ·
      refine ⟨872265955624511976689563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4652085096664063875677669 872265955624511976689563)
      ·
        refine ⟨1308398933436767965034345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 872265955624511976689563 1308398933436767965034345)
        ·
          refine ⟨981299200077575973775759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1308398933436767965034345 981299200077575973775759)
          ·
            refine ⟨1471948800116363960663639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 981299200077575973775759 1471948800116363960663639)
            ·
              refine ⟨2207923200174545940995459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1471948800116363960663639 2207923200174545940995459)
              ·
                refine ⟨3311884800261818911493189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2207923200174545940995459 3311884800261818911493189)
                ·
                  refine ⟨620978400049091045904973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3311884800261818911493189 620978400049091045904973)
                  ·
                    refine ⟨232866900018409142214365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 620978400049091045904973 232866900018409142214365)
                    ·
                      rfl

theorem cell22_680260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_680260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_680260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_680260 prefixEnd_680260 := by exact prefixLift 680260
  have htrace : WordTrace (prefixWord ++ tailWord_680260) baseStart_680260 baseEnd_680260 := by
    simpa [prefixWord, tailWord_680260, baseEnd_680260] using wordTrace_append hprefix tailTrace_680260
  have hstable : (prefixWord ++ tailWord_680260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680260).length < 2 ^ (prefixWord ++ tailWord_680260).sum := by decide
  have hdescent : baseEnd_680260 < baseStart_680260 := by decide
  rcases family_descends (prefixWord ++ tailWord_680260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680361 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 6, 3]
def baseStart_680361 : Nat := 118140960795 + 680361 * 2 ^ 59
def prefixEnd_680361 : Nat := 4983230072969 + 3 ^ 40 * 680361 * 2
def baseEnd_680361 : Nat := 232901474382478545439055

theorem tailTrace_680361 : CollatzResearch.WordTrace tailWord_680361 prefixEnd_680361 232901474382478545439055 := by
  unfold tailWord_680361
  simp only [CollatzResearch.WordTrace]
  refine ⟨24814804288175768253040937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16543202858783845502027291 24814804288175768253040937)
  ·
    refine ⟨18611103216131826189780703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24814804288175768253040937 18611103216131826189780703)
    ·
      refine ⟨27916654824197739284671055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18611103216131826189780703 27916654824197739284671055)
      ·
        refine ⟨41874982236296608927006583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27916654824197739284671055 41874982236296608927006583)
        ·
          refine ⟨62812473354444913390509875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41874982236296608927006583 62812473354444913390509875)
          ·
            refine ⟨94218710031667370085764813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62812473354444913390509875 94218710031667370085764813)
            ·
              refine ⟨35332016261875263782161805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94218710031667370085764813 35332016261875263782161805)
              ·
                refine ⟨13249506098203223918310677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35332016261875263782161805 13249506098203223918310677)
                ·
                  refine ⟨621070598353276121170813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13249506098203223918310677 621070598353276121170813)
                  ·
                    refine ⟨232901474382478545439055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 621070598353276121170813 232901474382478545439055)
                    ·
                      rfl

theorem cell22_680361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 6, 3].length) (baseStart_680361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_680361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_680361 prefixEnd_680361 := by exact prefixLift 680361
  have htrace : WordTrace (prefixWord ++ tailWord_680361) baseStart_680361 baseEnd_680361 := by
    simpa [prefixWord, tailWord_680361, baseEnd_680361] using wordTrace_append hprefix tailTrace_680361
  have hstable : (prefixWord ++ tailWord_680361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680361).length < 2 ^ (prefixWord ++ tailWord_680361).sum := by decide
  have hdescent : baseEnd_680361 < baseStart_680361 := by decide
  rcases family_descends (prefixWord ++ tailWord_680361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680380 : List Nat := [2, 2, 2, 4, 1, 2, 1, 4, 4]
def baseStart_680380 : Nat := 118140960795 + 680380 * 2 ^ 59
def prefixEnd_680380 : Nat := 4983230072969 + 3 ^ 40 * 680380 * 2
def baseEnd_680380 : Nat := 77635992823589609737999

theorem tailTrace_680380 : CollatzResearch.WordTrace tailWord_680380 prefixEnd_680380 77635992823589609737999 := by
  unfold tailWord_680380
  simp only [CollatzResearch.WordTrace]
  refine ⟨12407748637553467248991297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16543664850071289665321729 12407748637553467248991297)
  ·
    refine ⟨9305811478165100436743473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12407748637553467248991297 9305811478165100436743473)
    ·
      refine ⟨6979358608623825327557605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9305811478165100436743473 6979358608623825327557605)
      ·
        refine ⟨1308629739116967248917051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6979358608623825327557605 1308629739116967248917051)
        ·
          refine ⟨1962944608675450873375577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1308629739116967248917051 1962944608675450873375577)
          ·
            refine ⟨1472208456506588155031683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1962944608675450873375577 1472208456506588155031683)
            ·
              refine ⟨2208312684759882232547525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1472208456506588155031683 2208312684759882232547525)
              ·
                refine ⟨414058628392477918602661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2208312684759882232547525 414058628392477918602661)
                ·
                  refine ⟨77635992823589609737999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 414058628392477918602661 77635992823589609737999)
                  ·
                    rfl

theorem cell22_680380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 4, 4].length) (baseStart_680380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_680380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_680380 prefixEnd_680380 := by exact prefixLift 680380
  have htrace : WordTrace (prefixWord ++ tailWord_680380) baseStart_680380 baseEnd_680380 := by
    simpa [prefixWord, tailWord_680380, baseEnd_680380] using wordTrace_append hprefix tailTrace_680380
  have hstable : (prefixWord ++ tailWord_680380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680380).length < 2 ^ (prefixWord ++ tailWord_680380).sum := by decide
  have hdescent : baseEnd_680380 < baseStart_680380 := by decide
  rcases family_descends (prefixWord ++ tailWord_680380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680391 : List Nat := [1, 1, 4, 1, 1, 4, 3, 7]
def baseStart_680391 : Nat := 118140960795 + 680391 * 2 ^ 59
def prefixEnd_680391 : Nat := 4983230072969 + 3 ^ 40 * 680391 * 2
def baseEnd_680391 : Nat := 25879082666174274132107

theorem tailTrace_680391 : CollatzResearch.WordTrace tailWord_680391 prefixEnd_680391 25879082666174274132107 := by
  unfold tailWord_680391
  simp only [CollatzResearch.WordTrace]
  refine ⟨24815898478067083376633027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16543932318711388917755351 24815898478067083376633027)
  ·
    refine ⟨37223847717100625064949541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24815898478067083376633027 37223847717100625064949541)
    ·
      refine ⟨6979471446956367199678039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37223847717100625064949541 6979471446956367199678039)
      ·
        refine ⟨10469207170434550799517059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6979471446956367199678039 10469207170434550799517059)
        ·
          refine ⟨15703810755651826199275589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10469207170434550799517059 15703810755651826199275589)
          ·
            refine ⟨2944464516684717412364173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15703810755651826199275589 2944464516684717412364173)
            ·
              refine ⟨1104174193756769029636565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2944464516684717412364173 1104174193756769029636565)
              ·
                refine ⟨25879082666174274132107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1104174193756769029636565 25879082666174274132107)
                ·
                  rfl

theorem cell22_680391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 7].length) (baseStart_680391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_680391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_680391 prefixEnd_680391 := by exact prefixLift 680391
  have htrace : WordTrace (prefixWord ++ tailWord_680391) baseStart_680391 baseEnd_680391 := by
    simpa [prefixWord, tailWord_680391, baseEnd_680391] using wordTrace_append hprefix tailTrace_680391
  have hstable : (prefixWord ++ tailWord_680391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680391).length < 2 ^ (prefixWord ++ tailWord_680391).sum := by decide
  have hdescent : baseEnd_680391 < baseStart_680391 := by decide
  rcases family_descends (prefixWord ++ tailWord_680391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680423 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 5, 3]
def baseStart_680423 : Nat := 118140960795 + 680423 * 2 ^ 59
def prefixEnd_680423 : Nat := 4983230072969 + 3 ^ 40 * 680423 * 2
def baseEnd_680423 : Nat := 232922698249531050388865

theorem tailTrace_680423 : CollatzResearch.WordTrace tailWord_680423 prefixEnd_680423 232922698249531050388865 := by
  unfold tailWord_680423
  simp only [CollatzResearch.WordTrace]
  refine ⟨24817065613951152841797923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16544710409300768561198615 24817065613951152841797923)
  ·
    refine ⟨37225598420926729262696885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24817065613951152841797923 37225598420926729262696885)
    ·
      refine ⟨3489899851961880868377833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37225598420926729262696885 3489899851961880868377833)
      ·
        refine ⟨2617424888971410651283375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3489899851961880868377833 2617424888971410651283375)
        ·
          refine ⟨3926137333457115976925063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2617424888971410651283375 3926137333457115976925063)
          ·
            refine ⟨5889206000185673965387595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3926137333457115976925063 5889206000185673965387595)
            ·
              refine ⟨8833809000278510948081393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5889206000185673965387595 8833809000278510948081393)
              ·
                refine ⟨6625356750208883211061045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8833809000278510948081393 6625356750208883211061045)
                ·
                  refine ⟨621127195332082801036973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6625356750208883211061045 621127195332082801036973)
                  ·
                    refine ⟨232922698249531050388865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 621127195332082801036973 232922698249531050388865)
                    ·
                      rfl

theorem cell22_680423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_680423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_680423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_680423 prefixEnd_680423 := by exact prefixLift 680423
  have htrace : WordTrace (prefixWord ++ tailWord_680423) baseStart_680423 baseEnd_680423 := by
    simpa [prefixWord, tailWord_680423, baseEnd_680423] using wordTrace_append hprefix tailTrace_680423
  have hstable : (prefixWord ++ tailWord_680423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680423).length < 2 ^ (prefixWord ++ tailWord_680423).sum := by decide
  have hdescent : baseEnd_680423 < baseStart_680423 := by decide
  rcases family_descends (prefixWord ++ tailWord_680423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680440 : List Nat := [2, 1, 2, 1, 1, 4, 1, 6, 1, 3]
def baseStart_680440 : Nat := 118140960795 + 680440 * 2 ^ 59
def prefixEnd_680440 : Nat := 4983230072969 + 3 ^ 40 * 680440 * 2
def baseEnd_680440 : Nat := 232928517696948672713813

theorem tailTrace_680440 : CollatzResearch.WordTrace tailWord_680440 prefixEnd_680440 232928517696948672713813 := by
  unfold tailWord_680440
  simp only [CollatzResearch.WordTrace]
  refine ⟨12408842827444782372583387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16545123769926376496777849 12408842827444782372583387)
  ·
    refine ⟨18613264241167173558875081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12408842827444782372583387 18613264241167173558875081)
    ·
      refine ⟨13959948180875380169156311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18613264241167173558875081 13959948180875380169156311)
      ·
        refine ⟨20939922271313070253734467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13959948180875380169156311 20939922271313070253734467)
        ·
          refine ⟨31409883406969605380601701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20939922271313070253734467 31409883406969605380601701)
          ·
            refine ⟨5889353138806801008862819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31409883406969605380601701 5889353138806801008862819)
            ·
              refine ⟨8834029708210201513294229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5889353138806801008862819 8834029708210201513294229)
              ·
                refine ⟨414095142572353195935667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8834029708210201513294229 414095142572353195935667)
                ·
                  refine ⟨621142713858529793903501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 414095142572353195935667 621142713858529793903501)
                  ·
                    refine ⟨232928517696948672713813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 621142713858529793903501 232928517696948672713813)
                    ·
                      rfl

theorem cell22_680440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 6, 1, 3].length) (baseStart_680440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_680440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_680440 prefixEnd_680440 := by exact prefixLift 680440
  have htrace : WordTrace (prefixWord ++ tailWord_680440) baseStart_680440 baseEnd_680440 := by
    simpa [prefixWord, tailWord_680440, baseEnd_680440] using wordTrace_append hprefix tailTrace_680440
  have hstable : (prefixWord ++ tailWord_680440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680440).length < 2 ^ (prefixWord ++ tailWord_680440).sum := by decide
  have hdescent : baseEnd_680440 < baseStart_680440 := by decide
  rcases family_descends (prefixWord ++ tailWord_680440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680451 : List Nat := [1, 1, 1, 3, 2, 1, 3, 3, 2, 5]
def baseStart_680451 : Nat := 118140960795 + 680451 * 2 ^ 59
def prefixEnd_680451 : Nat := 4983230072969 + 3 ^ 40 * 680451 * 2
def baseEnd_680451 : Nat := 232932283221748310688779

theorem tailTrace_680451 : CollatzResearch.WordTrace tailWord_680451 prefixEnd_680451 232932283221748310688779 := by
  unfold tailWord_680451
  simp only [CollatzResearch.WordTrace]
  refine ⟨24818086857849713623817207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16545391238566475749211471 24818086857849713623817207)
  ·
    refine ⟨37227130286774570435725811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24818086857849713623817207 37227130286774570435725811)
    ·
      refine ⟨55840695430161855653588717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37227130286774570435725811 55840695430161855653588717)
      ·
        refine ⟨20940260786310695870095769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55840695430161855653588717 20940260786310695870095769)
        ·
          refine ⟨15705195589733021902571827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20940260786310695870095769 15705195589733021902571827)
          ·
            refine ⟨23557793384599532853857741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15705195589733021902571827 23557793384599532853857741)
            ·
              refine ⟨8834172519224824820196653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23557793384599532853857741 8834172519224824820196653)
              ·
                refine ⟨3312814694709309307573745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8834172519224824820196653 3312814694709309307573745)
                ·
                  refine ⟨2484611021031981980680309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3312814694709309307573745 2484611021031981980680309)
                  ·
                    refine ⟨232932283221748310688779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2484611021031981980680309 232932283221748310688779)
                    ·
                      rfl

theorem cell22_680451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 5].length) (baseStart_680451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_680451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_680451 prefixEnd_680451 := by exact prefixLift 680451
  have htrace : WordTrace (prefixWord ++ tailWord_680451) baseStart_680451 baseEnd_680451 := by
    simpa [prefixWord, tailWord_680451, baseEnd_680451] using wordTrace_append hprefix tailTrace_680451
  have hstable : (prefixWord ++ tailWord_680451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680451).length < 2 ^ (prefixWord ++ tailWord_680451).sum := by decide
  have hdescent : baseEnd_680451 < baseStart_680451 := by decide
  rcases family_descends (prefixWord ++ tailWord_680451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680498 : List Nat := [3, 2, 1, 1, 2, 1, 5, 1, 6]
def baseStart_680498 : Nat := 118140960795 + 680498 * 2 ^ 59
def prefixEnd_680498 : Nat := 4983230072969 + 3 ^ 40 * 680498 * 2
def baseEnd_680498 : Nat := 77649457427418618254545

theorem tailTrace_680498 : CollatzResearch.WordTrace tailWord_680498 prefixEnd_680498 77649457427418618254545 := by
  unfold tailWord_680498
  simp only [CollatzResearch.WordTrace]
  refine ⟨6204950272169860162694537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16546534059119627100518765 6204950272169860162694537)
  ·
    refine ⟨4653712704127395122020903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6204950272169860162694537 4653712704127395122020903)
    ·
      refine ⟨6980569056191092683031355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4653712704127395122020903 6980569056191092683031355)
      ·
        refine ⟨10470853584286639024547033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6980569056191092683031355 10470853584286639024547033)
        ·
          refine ⟨7853140188214979268410275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10470853584286639024547033 7853140188214979268410275)
          ·
            refine ⟨11779710282322468902615413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7853140188214979268410275 11779710282322468902615413)
            ·
              refine ⟨1104347838967731459620195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11779710282322468902615413 1104347838967731459620195)
              ·
                refine ⟨1656521758451597189430293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1104347838967731459620195 1656521758451597189430293)
                ·
                  refine ⟨77649457427418618254545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1656521758451597189430293 77649457427418618254545)
                  ·
                    rfl

theorem cell22_680498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_680498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_680498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_680498 prefixEnd_680498 := by exact prefixLift 680498
  have htrace : WordTrace (prefixWord ++ tailWord_680498) baseStart_680498 baseEnd_680498 := by
    simpa [prefixWord, tailWord_680498, baseEnd_680498] using wordTrace_append hprefix tailTrace_680498
  have hstable : (prefixWord ++ tailWord_680498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680498).length < 2 ^ (prefixWord ++ tailWord_680498).sum := by decide
  have hdescent : baseEnd_680498 < baseStart_680498 := by decide
  rcases family_descends (prefixWord ++ tailWord_680498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680542 : List Nat := [4, 4, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_680542 : Nat := 118140960795 + 680542 * 2 ^ 59
def prefixEnd_680542 : Nat := 4983230072969 + 3 ^ 40 * 680542 * 2
def baseEnd_680542 : Nat := 232963434381454406663501

theorem tailTrace_680542 : CollatzResearch.WordTrace tailWord_680542 prefixEnd_680542 232963434381454406663501 := by
  unfold tailWord_680542
  simp only [CollatzResearch.WordTrace]
  refine ⟨3102675737565004520672485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16547603933680024110253253 3102675737565004520672485)
  ·
    refine ⟨581751700793438347626091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3102675737565004520672485 581751700793438347626091)
    ·
      refine ⟨872627551190157521439137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 581751700793438347626091 872627551190157521439137)
      ·
        refine ⟨654470663392618141079353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 872627551190157521439137 654470663392618141079353)
        ·
          refine ⟨490852997544463605809515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 654470663392618141079353 490852997544463605809515)
          ·
            refine ⟨736279496316695408714273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490852997544463605809515 736279496316695408714273)
            ·
              refine ⟨552209622237521556535705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 736279496316695408714273 552209622237521556535705)
              ·
                refine ⟨414157216678141167401779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 552209622237521556535705 414157216678141167401779)
                ·
                  refine ⟨621235825017211751102669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 414157216678141167401779 621235825017211751102669)
                  ·
                    refine ⟨232963434381454406663501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 621235825017211751102669 232963434381454406663501)
                    ·
                      rfl

theorem cell22_680542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_680542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_680542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_680542 prefixEnd_680542 := by exact prefixLift 680542
  have htrace : WordTrace (prefixWord ++ tailWord_680542) baseStart_680542 baseEnd_680542 := by
    simpa [prefixWord, tailWord_680542, baseEnd_680542] using wordTrace_append hprefix tailTrace_680542
  have hstable : (prefixWord ++ tailWord_680542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680542).length < 2 ^ (prefixWord ++ tailWord_680542).sum := by decide
  have hdescent : baseEnd_680542 < baseStart_680542 := by decide
  rcases family_descends (prefixWord ++ tailWord_680542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680549 : List Nat := [1, 3, 1, 3, 4, 2, 2, 2, 4]
def baseStart_680549 : Nat := 118140960795 + 680549 * 2 ^ 59
def prefixEnd_680549 : Nat := 4983230072969 + 3 ^ 40 * 680549 * 2
def baseEnd_680549 : Nat := 77655276874836240579493

theorem tailTrace_680549 : CollatzResearch.WordTrace tailWord_680549 prefixEnd_680549 77655276874836240579493 := by
  unfold tailWord_680549
  simp only [CollatzResearch.WordTrace]
  refine ⟨24821661211494676360884701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16547774140996450907256467 24821661211494676360884701)
  ·
    refine ⟨9308122954310503635331763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24821661211494676360884701 9308122954310503635331763)
    ·
      refine ⟨13962184431465755452997645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9308122954310503635331763 13962184431465755452997645)
      ·
        refine ⟨5235819161799658294874117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13962184431465755452997645 5235819161799658294874117)
        ·
          refine ⟨981716092837435930288897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5235819161799658294874117 981716092837435930288897)
          ·
            refine ⟨736287069628076947716673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 981716092837435930288897 736287069628076947716673)
            ·
              refine ⟨552215302221057710787505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 736287069628076947716673 552215302221057710787505)
              ·
                refine ⟨414161476665793283090629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 552215302221057710787505 414161476665793283090629)
                ·
                  refine ⟨77655276874836240579493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 414161476665793283090629 77655276874836240579493)
                  ·
                    rfl

theorem cell22_680549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 2, 4].length) (baseStart_680549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_680549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_680549 prefixEnd_680549 := by exact prefixLift 680549
  have htrace : WordTrace (prefixWord ++ tailWord_680549) baseStart_680549 baseEnd_680549 := by
    simpa [prefixWord, tailWord_680549, baseEnd_680549] using wordTrace_append hprefix tailTrace_680549
  have hstable : (prefixWord ++ tailWord_680549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680549).length < 2 ^ (prefixWord ++ tailWord_680549).sum := by decide
  have hdescent : baseEnd_680549 < baseStart_680549 := by decide
  rcases family_descends (prefixWord ++ tailWord_680549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680560 : List Nat := [2, 1, 1, 1, 7, 2, 1, 7]
def baseStart_680560 : Nat := 118140960795 + 680560 * 2 ^ 59
def prefixEnd_680560 : Nat := 4983230072969 + 3 ^ 40 * 680560 * 2
def baseEnd_680560 : Nat := 25885510683256484412605

theorem tailTrace_680560 : CollatzResearch.WordTrace tailWord_680560 prefixEnd_680560 25885510683256484412605 := by
  unfold tailWord_680560
  simp only [CollatzResearch.WordTrace]
  refine ⟨12411031207227412619767567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16548041609636550159690089 12411031207227412619767567)
  ·
    refine ⟨18616546810841118929651351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12411031207227412619767567 18616546810841118929651351)
    ·
      refine ⟨27924820216261678394477027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18616546810841118929651351 27924820216261678394477027)
      ·
        refine ⟨41887230324392517591715541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27924820216261678394477027 41887230324392517591715541)
        ·
          refine ⟨981731960727949631055833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 41887230324392517591715541 981731960727949631055833)
          ·
            refine ⟨736298970545962223291875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 981731960727949631055833 736298970545962223291875)
            ·
              refine ⟨1104448455818943334937813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 736298970545962223291875 1104448455818943334937813)
              ·
                refine ⟨25885510683256484412605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1104448455818943334937813 25885510683256484412605)
                ·
                  rfl

theorem cell22_680560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 7].length) (baseStart_680560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_680560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_680560 prefixEnd_680560 := by exact prefixLift 680560
  have htrace : WordTrace (prefixWord ++ tailWord_680560) baseStart_680560 baseEnd_680560 := by
    simpa [prefixWord, tailWord_680560, baseEnd_680560] using wordTrace_append hprefix tailTrace_680560
  have hstable : (prefixWord ++ tailWord_680560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680560).length < 2 ^ (prefixWord ++ tailWord_680560).sum := by decide
  have hdescent : baseEnd_680560 < baseStart_680560 := by decide
  rcases family_descends (prefixWord ++ tailWord_680560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680605 : List Nat := [1, 4, 2, 1, 1, 1, 5, 2, 5]
def baseStart_680605 : Nat := 118140960795 + 680605 * 2 ^ 59
def prefixEnd_680605 : Nat := 4983230072969 + 3 ^ 40 * 680605 * 2
def baseEnd_680605 : Nat := 77661666856314414112769

theorem tailTrace_680605 : CollatzResearch.WordTrace tailWord_680605 prefixEnd_680605 77661666856314414112769 := by
  unfold tailWord_680605
  simp only [CollatzResearch.WordTrace]
  refine ⟨24823703699291797924923269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16549135799527865283282179 24823703699291797924923269)
  ·
    refine ⟨4654444443617212110923113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24823703699291797924923269 4654444443617212110923113)
    ·
      refine ⟨3490833332712909083192335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4654444443617212110923113 3490833332712909083192335)
      ·
        refine ⟨5236249999069363624788503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3490833332712909083192335 5236249999069363624788503)
        ·
          refine ⟨7854374998604045437182755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5236249999069363624788503 7854374998604045437182755)
          ·
            refine ⟨11781562497906068155774133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7854374998604045437182755 11781562497906068155774133)
            ·
              refine ⟨1104521484178693889603825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11781562497906068155774133 1104521484178693889603825)
              ·
                refine ⟨828391113134020417202869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1104521484178693889603825 828391113134020417202869)
                ·
                  refine ⟨77661666856314414112769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 828391113134020417202869 77661666856314414112769)
                  ·
                    rfl

theorem cell22_680605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_680605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_680605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_680605 prefixEnd_680605 := by exact prefixLift 680605
  have htrace : WordTrace (prefixWord ++ tailWord_680605) baseStart_680605 baseEnd_680605 := by
    simpa [prefixWord, tailWord_680605, baseEnd_680605] using wordTrace_append hprefix tailTrace_680605
  have hstable : (prefixWord ++ tailWord_680605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680605).length < 2 ^ (prefixWord ++ tailWord_680605).sum := by decide
  have hdescent : baseEnd_680605 < baseStart_680605 := by decide
  rcases family_descends (prefixWord ++ tailWord_680605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680652 : List Nat := [2, 2, 1, 5, 1, 1, 2, 3, 1, 4]
def baseStart_680652 : Nat := 118140960795 + 680652 * 2 ^ 59
def prefixEnd_680652 : Nat := 4983230072969 + 3 ^ 40 * 680652 * 2
def baseEnd_680652 : Nat := 233001089629450786413163

theorem tailTrace_680652 : CollatzResearch.WordTrace tailWord_680652 prefixEnd_680652 233001089629450786413163 := by
  unfold tailWord_680652
  simp only [CollatzResearch.WordTrace]
  refine ⟨12412708965060762475942105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16550278620081016634589473 12412708965060762475942105)
  ·
    refine ⟨9309531723795571856956579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12412708965060762475942105 9309531723795571856956579)
    ·
      refine ⟨13964297585693357785434869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9309531723795571856956579 13964297585693357785434869)
      ·
        refine ⟨1309152898658752292384519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13964297585693357785434869 1309152898658752292384519)
        ·
          refine ⟨1963729347988128438576779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1309152898658752292384519 1963729347988128438576779)
          ·
            refine ⟨2945594021982192657865169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1963729347988128438576779 2945594021982192657865169)
            ·
              refine ⟨2209195516486644493398877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2945594021982192657865169 2209195516486644493398877)
              ·
                refine ⟨828448318682491685024579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2209195516486644493398877 828448318682491685024579)
                ·
                  refine ⟨1242672478023737527536869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 828448318682491685024579 1242672478023737527536869)
                  ·
                    refine ⟨233001089629450786413163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1242672478023737527536869 233001089629450786413163)
                    ·
                      rfl

theorem cell22_680652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_680652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_680652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_680652 prefixEnd_680652 := by exact prefixLift 680652
  have htrace : WordTrace (prefixWord ++ tailWord_680652) baseStart_680652 baseEnd_680652 := by
    simpa [prefixWord, tailWord_680652, baseEnd_680652] using wordTrace_append hprefix tailTrace_680652
  have hstable : (prefixWord ++ tailWord_680652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680652).length < 2 ^ (prefixWord ++ tailWord_680652).sum := by decide
  have hdescent : baseEnd_680652 < baseStart_680652 := by decide
  rcases family_descends (prefixWord ++ tailWord_680652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680665 : List Nat := [1, 2, 1, 2, 3, 2, 1, 3, 4, 3]
def baseStart_680665 : Nat := 118140960795 + 680665 * 2 ^ 59
def prefixEnd_680665 : Nat := 4983230072969 + 3 ^ 40 * 680665 * 2
def baseEnd_680665 : Nat := 233005539795123085838123

theorem tailTrace_680665 : CollatzResearch.WordTrace tailWord_680665 prefixEnd_680665 233005539795123085838123 := by
  unfold tailWord_680665
  simp only [CollatzResearch.WordTrace]
  refine ⟨24825892079074428172107449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16550594719382952114738299 24825892079074428172107449)
  ·
    refine ⟨18619419059305821129080587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24825892079074428172107449 18619419059305821129080587)
    ·
      refine ⟨27929128588958731693620881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18619419059305821129080587 27929128588958731693620881)
      ·
        refine ⟨20946846441719048770215661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27929128588958731693620881 20946846441719048770215661)
        ·
          refine ⟨7855067415644643288830873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20946846441719048770215661 7855067415644643288830873)
          ·
            refine ⟨5891300561733482466623155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7855067415644643288830873 5891300561733482466623155)
            ·
              refine ⟨8836950842600223699934733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5891300561733482466623155 8836950842600223699934733)
              ·
                refine ⟨3313856565975083887475525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8836950842600223699934733 3313856565975083887475525)
                ·
                  refine ⟨621348106120328228901661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3313856565975083887475525 621348106120328228901661)
                  ·
                    refine ⟨233005539795123085838123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 621348106120328228901661 233005539795123085838123)
                    ·
                      rfl

theorem cell22_680665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 4, 3].length) (baseStart_680665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_680665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_680665 prefixEnd_680665 := by exact prefixLift 680665
  have htrace : WordTrace (prefixWord ++ tailWord_680665) baseStart_680665 baseEnd_680665 := by
    simpa [prefixWord, tailWord_680665, baseEnd_680665] using wordTrace_append hprefix tailTrace_680665
  have hstable : (prefixWord ++ tailWord_680665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680665).length < 2 ^ (prefixWord ++ tailWord_680665).sum := by decide
  have hdescent : baseEnd_680665 < baseStart_680665 := by decide
  rcases family_descends (prefixWord ++ tailWord_680665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680804 : List Nat := [2, 3, 1, 1, 4, 2, 2, 2, 1, 4]
def baseStart_680804 : Nat := 118140960795 + 680804 * 2 ^ 59
def prefixEnd_680804 : Nat := 4983230072969 + 3 ^ 40 * 680804 * 2
def baseEnd_680804 : Nat := 233053122335773056612697

theorem tailTrace_680804 : CollatzResearch.WordTrace tailWord_680804 prefixEnd_680804 233053122335773056612697 := by
  unfold tailWord_680804
  simp only [CollatzResearch.WordTrace]
  refine ⟨12415480912785427455708733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16553974550380569940944977 12415480912785427455708733)
  ·
    refine ⟨4655805342294535295890775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12415480912785427455708733 4655805342294535295890775)
    ·
      refine ⟨6983708013441802943836163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4655805342294535295890775 6983708013441802943836163)
      ·
        refine ⟨10475562020162704415754245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6983708013441802943836163 10475562020162704415754245)
        ·
          refine ⟨1964167878780507077953921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10475562020162704415754245 1964167878780507077953921)
          ·
            refine ⟨1473125909085380308465441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1964167878780507077953921 1473125909085380308465441)
            ·
              refine ⟨1104844431814035231349081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1473125909085380308465441 1104844431814035231349081)
              ·
                refine ⟨828633323860526423511811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1104844431814035231349081 828633323860526423511811)
                ·
                  refine ⟨1242949985790789635267717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 828633323860526423511811 1242949985790789635267717)
                  ·
                    refine ⟨233053122335773056612697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1242949985790789635267717 233053122335773056612697)
                    ·
                      rfl

theorem cell22_680804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_680804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_680804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_680804 prefixEnd_680804 := by exact prefixLift 680804
  have htrace : WordTrace (prefixWord ++ tailWord_680804) baseStart_680804 baseEnd_680804 := by
    simpa [prefixWord, tailWord_680804, baseEnd_680804] using wordTrace_append hprefix tailTrace_680804
  have hstable : (prefixWord ++ tailWord_680804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680804).length < 2 ^ (prefixWord ++ tailWord_680804).sum := by decide
  have hdescent : baseEnd_680804 < baseStart_680804 := by decide
  rcases family_descends (prefixWord ++ tailWord_680804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680815 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 6, 4]
def baseStart_680815 : Nat := 118140960795 + 680815 * 2 ^ 59
def prefixEnd_680815 : Nat := 4983230072969 + 3 ^ 40 * 680815 * 2
def baseEnd_680815 : Nat := 233056887860572694587663

theorem tailTrace_680815 : CollatzResearch.WordTrace tailWord_680815 prefixEnd_680815 233056887860572694587663 := by
  unfold tailWord_680815
  simp only [CollatzResearch.WordTrace]
  refine ⟨24831363028531003790067899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16554242019020669193378599 24831363028531003790067899)
  ·
    refine ⟨37247044542796505685101849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24831363028531003790067899 37247044542796505685101849)
    ·
      refine ⟨27935283407097379263826387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37247044542796505685101849 27935283407097379263826387)
      ·
        refine ⟨41902925110646068895739581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27935283407097379263826387 41902925110646068895739581)
        ·
          refine ⟨15713596916492275835902343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41902925110646068895739581 15713596916492275835902343)
          ·
            refine ⟨23570395374738413753853515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15713596916492275835902343 23570395374738413753853515)
            ·
              refine ⟨35355593062107620630780273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23570395374738413753853515 35355593062107620630780273)
              ·
                refine ⟨26516694796580715473085205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35355593062107620630780273 26516694796580715473085205)
                ·
                  refine ⟨1242970068589721037800869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26516694796580715473085205 1242970068589721037800869)
                  ·
                    refine ⟨233056887860572694587663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1242970068589721037800869 233056887860572694587663)
                    ·
                      rfl

theorem cell22_680815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 4].length) (baseStart_680815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_680815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_680815 prefixEnd_680815 := by exact prefixLift 680815
  have htrace : WordTrace (prefixWord ++ tailWord_680815) baseStart_680815 baseEnd_680815 := by
    simpa [prefixWord, tailWord_680815, baseEnd_680815] using wordTrace_append hprefix tailTrace_680815
  have hstable : (prefixWord ++ tailWord_680815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680815).length < 2 ^ (prefixWord ++ tailWord_680815).sum := by decide
  have hdescent : baseEnd_680815 < baseStart_680815 := by decide
  rcases family_descends (prefixWord ++ tailWord_680815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680817 : List Nat := [1, 2, 2, 2, 1, 4, 1, 2, 4, 3]
def baseStart_680817 : Nat := 118140960795 + 680817 * 2 ^ 59
def prefixEnd_680817 : Nat := 4983230072969 + 3 ^ 40 * 680817 * 2
def baseEnd_680817 : Nat := 233057572501445356037657

theorem tailTrace_680817 : CollatzResearch.WordTrace tailWord_680817 prefixEnd_680817 233057572501445356037657 := by
  unfold tailWord_680817
  simp only [CollatzResearch.WordTrace]
  refine ⟨24831435974523758131640705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16554290649682505421093803 24831435974523758131640705)
  ·
    refine ⟨18623576980892818598730529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24831435974523758131640705 18623576980892818598730529)
    ·
      refine ⟨13967682735669613949047897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18623576980892818598730529 13967682735669613949047897)
      ·
        refine ⟨10475762051752210461785923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13967682735669613949047897 10475762051752210461785923)
        ·
          refine ⟨15713643077628315692678885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10475762051752210461785923 15713643077628315692678885)
          ·
            refine ⟨2946308077055309192377291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15713643077628315692678885 2946308077055309192377291)
            ·
              refine ⟨4419462115582963788565937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2946308077055309192377291 4419462115582963788565937)
              ·
                refine ⟨3314596586687222841424453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4419462115582963788565937 3314596586687222841424453)
                ·
                  refine ⟨621486860003854282767085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3314596586687222841424453 621486860003854282767085)
                  ·
                    refine ⟨233057572501445356037657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 621486860003854282767085 233057572501445356037657)
                    ·
                      rfl

theorem cell22_680817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 4, 3].length) (baseStart_680817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_680817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_680817 prefixEnd_680817 := by exact prefixLift 680817
  have htrace : WordTrace (prefixWord ++ tailWord_680817) baseStart_680817 baseEnd_680817 := by
    simpa [prefixWord, tailWord_680817, baseEnd_680817] using wordTrace_append hprefix tailTrace_680817
  have hstable : (prefixWord ++ tailWord_680817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680817).length < 2 ^ (prefixWord ++ tailWord_680817).sum := by decide
  have hdescent : baseEnd_680817 < baseStart_680817 := by decide
  rcases family_descends (prefixWord ++ tailWord_680817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680896 : List Nat := [2, 1, 1, 2, 3, 4, 1, 4, 1, 3]
def baseStart_680896 : Nat := 118140960795 + 680896 * 2 ^ 59
def prefixEnd_680896 : Nat := 4983230072969 + 3 ^ 40 * 680896 * 2
def baseEnd_680896 : Nat := 233084615815915483312415

theorem tailTrace_680896 : CollatzResearch.WordTrace tailWord_680896 prefixEnd_680896 233084615815915483312415 := by
  unfold tailWord_680896
  simp only [CollatzResearch.WordTrace]
  refine ⟨12417158670618777311883271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16556211560825036415844361 12417158670618777311883271)
  ·
    refine ⟨18625738005928165967824907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12417158670618777311883271 18625738005928165967824907)
    ·
      refine ⟨27938607008892248951737361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18625738005928165967824907 27938607008892248951737361)
      ·
        refine ⟨20953955256669186713803021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27938607008892248951737361 20953955256669186713803021)
        ·
          refine ⟨7857733221250945017676133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20953955256669186713803021 7857733221250945017676133)
          ·
            refine ⟨1473324978984552190814275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7857733221250945017676133 1473324978984552190814275)
            ·
              refine ⟨2209987468476828286221413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1473324978984552190814275 2209987468476828286221413)
              ·
                refine ⟨414372650339405303666515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2209987468476828286221413 414372650339405303666515)
                ·
                  refine ⟨621558975509107955499773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 414372650339405303666515 621558975509107955499773)
                  ·
                    refine ⟨233084615815915483312415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 621558975509107955499773 233084615815915483312415)
                    ·
                      rfl

theorem cell22_680896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 4, 1, 3].length) (baseStart_680896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_680896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_680896 prefixEnd_680896 := by exact prefixLift 680896
  have htrace : WordTrace (prefixWord ++ tailWord_680896) baseStart_680896 baseEnd_680896 := by
    simpa [prefixWord, tailWord_680896, baseEnd_680896] using wordTrace_append hprefix tailTrace_680896
  have hstable : (prefixWord ++ tailWord_680896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680896).length < 2 ^ (prefixWord ++ tailWord_680896).sum := by decide
  have hdescent : baseEnd_680896 < baseStart_680896 := by decide
  rcases family_descends (prefixWord ++ tailWord_680896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680905 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 1, 10]
def baseStart_680905 : Nat := 118140960795 + 680905 * 2 ^ 59
def prefixEnd_680905 : Nat := 4983230072969 + 3 ^ 40 * 680905 * 2
def baseEnd_680905 : Nat := 233087696699842459837387

theorem tailTrace_680905 : CollatzResearch.WordTrace tailWord_680905 prefixEnd_680905 233087696699842459837387 := by
  unfold tailWord_680905
  simp only [CollatzResearch.WordTrace]
  refine ⟨24834645598204949160844169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16556430398803299440562779 24834645598204949160844169)
  ·
    refine ⟨18625984198653711870633127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24834645598204949160844169 18625984198653711870633127)
    ·
      refine ⟨27938976297980567805949691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18625984198653711870633127 27938976297980567805949691)
      ·
        refine ⟨41908464446970851708924537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27938976297980567805949691 41908464446970851708924537)
        ·
          refine ⟨31431348335228138781693403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41908464446970851708924537 31431348335228138781693403)
          ·
            refine ⟨47147022502842208172540105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31431348335228138781693403 47147022502842208172540105)
            ·
              refine ⟨35360266877131656129405079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47147022502842208172540105 35360266877131656129405079)
              ·
                refine ⟨53040400315697484194107619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35360266877131656129405079 53040400315697484194107619)
                ·
                  refine ⟨79560600473546226291161429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53040400315697484194107619 79560600473546226291161429)
                  ·
                    refine ⟨233087696699842459837387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 79560600473546226291161429 233087696699842459837387)
                    ·
                      rfl

theorem cell22_680905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 10].length) (baseStart_680905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_680905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_680905 prefixEnd_680905 := by exact prefixLift 680905
  have htrace : WordTrace (prefixWord ++ tailWord_680905) baseStart_680905 baseEnd_680905 := by
    simpa [prefixWord, tailWord_680905, baseEnd_680905] using wordTrace_append hprefix tailTrace_680905
  have hstable : (prefixWord ++ tailWord_680905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680905).length < 2 ^ (prefixWord ++ tailWord_680905).sum := by decide
  have hdescent : baseEnd_680905 < baseStart_680905 := by decide
  rcases family_descends (prefixWord ++ tailWord_680905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680907 : List Nat := [1, 1, 1, 1, 3, 6, 1, 1, 2, 5]
def baseStart_680907 : Nat := 118140960795 + 680907 * 2 ^ 59
def prefixEnd_680907 : Nat := 4983230072969 + 3 ^ 40 * 680907 * 2
def baseEnd_680907 : Nat := 233088381340715121287381

theorem tailTrace_680907 : CollatzResearch.WordTrace tailWord_680907 prefixEnd_680907 233088381340715121287381 := by
  unfold tailWord_680907
  simp only [CollatzResearch.WordTrace]
  refine ⟨24834718544197703502416975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16556479029465135668277983 24834718544197703502416975)
  ·
    refine ⟨37252077816296555253625463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24834718544197703502416975 37252077816296555253625463)
    ·
      refine ⟨55878116724444832880438195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37252077816296555253625463 55878116724444832880438195)
      ·
        refine ⟨83817175086667249320657293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55878116724444832880438195 83817175086667249320657293)
        ·
          refine ⟨31431440657500218495246485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83817175086667249320657293 31431440657500218495246485)
          ·
            refine ⟨1473348780820322741964679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31431440657500218495246485 1473348780820322741964679)
            ·
              refine ⟨2210023171230484112947019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1473348780820322741964679 2210023171230484112947019)
              ·
                refine ⟨3315034756845726169420529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2210023171230484112947019 3315034756845726169420529)
                ·
                  refine ⟨2486276067634294627065397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3315034756845726169420529 2486276067634294627065397)
                  ·
                    refine ⟨233088381340715121287381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2486276067634294627065397 233088381340715121287381)
                    ·
                      rfl

theorem cell22_680907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 5].length) (baseStart_680907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_680907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_680907 prefixEnd_680907 := by exact prefixLift 680907
  have htrace : WordTrace (prefixWord ++ tailWord_680907) baseStart_680907 baseEnd_680907 := by
    simpa [prefixWord, tailWord_680907, baseEnd_680907] using wordTrace_append hprefix tailTrace_680907
  have hstable : (prefixWord ++ tailWord_680907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680907).length < 2 ^ (prefixWord ++ tailWord_680907).sum := by decide
  have hdescent : baseEnd_680907 < baseStart_680907 := by decide
  rcases family_descends (prefixWord ++ tailWord_680907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680930 : List Nat := [3, 3, 3, 1, 1, 2, 2, 3, 1, 3]
def baseStart_680930 : Nat := 118140960795 + 680930 * 2 ^ 59
def prefixEnd_680930 : Nat := 4983230072969 + 3 ^ 40 * 680930 * 2
def baseEnd_680930 : Nat := 233096254710750727962311

theorem tailTrace_680930 : CollatzResearch.WordTrace tailWord_680930 prefixEnd_680930 233096254710750727962311 := by
  unfold tailWord_680930
  simp only [CollatzResearch.WordTrace]
  refine ⟨6208889355778594607626061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16557038282076252287002829 6208889355778594607626061)
  ·
    refine ⟨2328333508416972977859773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6208889355778594607626061 2328333508416972977859773)
    ·
      refine ⟨873125065656364866697415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2328333508416972977859773 873125065656364866697415)
      ·
        refine ⟨1309687598484547300046123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 873125065656364866697415 1309687598484547300046123)
        ·
          refine ⟨1964531397726820950069185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1309687598484547300046123 1964531397726820950069185)
          ·
            refine ⟨1473398548295115712551889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1964531397726820950069185 1473398548295115712551889)
            ·
              refine ⟨1105048911221336784413917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1473398548295115712551889 1105048911221336784413917)
              ·
                refine ⟨414393341708001294155219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1105048911221336784413917 414393341708001294155219)
                ·
                  refine ⟨621590012562001941232829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 414393341708001294155219 621590012562001941232829)
                  ·
                    refine ⟨233096254710750727962311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 621590012562001941232829 233096254710750727962311)
                    ·
                      rfl

theorem cell22_680930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_680930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_680930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_680930 prefixEnd_680930 := by exact prefixLift 680930
  have htrace : WordTrace (prefixWord ++ tailWord_680930) baseStart_680930 baseEnd_680930 := by
    simpa [prefixWord, tailWord_680930, baseEnd_680930] using wordTrace_append hprefix tailTrace_680930
  have hstable : (prefixWord ++ tailWord_680930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680930).length < 2 ^ (prefixWord ++ tailWord_680930).sum := by decide
  have hdescent : baseEnd_680930 < baseStart_680930 := by decide
  rcases family_descends (prefixWord ++ tailWord_680930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680967 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 3, 6]
def baseStart_680967 : Nat := 118140960795 + 680967 * 2 ^ 59
def prefixEnd_680967 : Nat := 4983230072969 + 3 ^ 40 * 680967 * 2
def baseEnd_680967 : Nat := 233108920566894964787197

theorem tailTrace_680967 : CollatzResearch.WordTrace tailWord_680967 prefixEnd_680967 233108920566894964787197 := by
  unfold tailWord_680967
  simp only [CollatzResearch.WordTrace]
  refine ⟨24836906923980333749601155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16557937949320222499734103 24836906923980333749601155)
  ·
    refine ⟨37255360385970500624401733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24836906923980333749601155 37255360385970500624401733)
    ·
      refine ⟨6985380072369468867075325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37255360385970500624401733 6985380072369468867075325)
      ·
        refine ⟨2619517527138550825153247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6985380072369468867075325 2619517527138550825153247)
        ·
          refine ⟨3929276290707826237729871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2619517527138550825153247 3929276290707826237729871)
          ·
            refine ⟨5893914436061739356594807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3929276290707826237729871 5893914436061739356594807)
            ·
              refine ⟨8840871654092609034892211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5893914436061739356594807 8840871654092609034892211)
              ·
                refine ⟨13261307481138913552338317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8840871654092609034892211 13261307481138913552338317)
                ·
                  refine ⟨4972990305427092582126869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13261307481138913552338317 4972990305427092582126869)
                  ·
                    refine ⟨233108920566894964787197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4972990305427092582126869 233108920566894964787197)
                    ·
                      rfl

theorem cell22_680967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_680967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_680967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_680967 prefixEnd_680967 := by exact prefixLift 680967
  have htrace : WordTrace (prefixWord ++ tailWord_680967) baseStart_680967 baseEnd_680967 := by
    simpa [prefixWord, tailWord_680967, baseEnd_680967] using wordTrace_append hprefix tailTrace_680967
  have hstable : (prefixWord ++ tailWord_680967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680967).length < 2 ^ (prefixWord ++ tailWord_680967).sum := by decide
  have hdescent : baseEnd_680967 < baseStart_680967 := by decide
  rcases family_descends (prefixWord ++ tailWord_680967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680969 : List Nat := [1, 2, 1, 1, 3, 1, 1, 7, 2, 3]
def baseStart_680969 : Nat := 118140960795 + 680969 * 2 ^ 59
def prefixEnd_680969 : Nat := 4983230072969 + 3 ^ 40 * 680969 * 2
def baseEnd_680969 : Nat := 233109605207767626237191

theorem tailTrace_680969 : CollatzResearch.WordTrace tailWord_680969 prefixEnd_680969 233109605207767626237191 := by
  unfold tailWord_680969
  simp only [CollatzResearch.WordTrace]
  refine ⟨24836979869973088091173961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16557986579982058727449307 24836979869973088091173961)
  ·
    refine ⟨18627734902479816068380471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24836979869973088091173961 18627734902479816068380471)
    ·
      refine ⟨27941602353719724102570707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18627734902479816068380471 27941602353719724102570707)
      ·
        refine ⟨41912403530579586153856061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27941602353719724102570707 41912403530579586153856061)
        ·
          refine ⟨15717151323967344807696023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41912403530579586153856061 15717151323967344807696023)
          ·
            refine ⟨23575726985951017211544035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15717151323967344807696023 23575726985951017211544035)
            ·
              refine ⟨35363590478926525817316053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23575726985951017211544035 35363590478926525817316053)
              ·
                refine ⟨828834151849840448843345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 35363590478926525817316053 828834151849840448843345)
                ·
                  refine ⟨621625613887380336632509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 828834151849840448843345 621625613887380336632509)
                  ·
                    refine ⟨233109605207767626237191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 621625613887380336632509 233109605207767626237191)
                    ·
                      rfl

theorem cell22_680969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 2, 3].length) (baseStart_680969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_680969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_680969 prefixEnd_680969 := by exact prefixLift 680969
  have htrace : WordTrace (prefixWord ++ tailWord_680969) baseStart_680969 baseEnd_680969 := by
    simpa [prefixWord, tailWord_680969, baseEnd_680969] using wordTrace_append hprefix tailTrace_680969
  have hstable : (prefixWord ++ tailWord_680969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680969).length < 2 ^ (prefixWord ++ tailWord_680969).sum := by decide
  have hdescent : baseEnd_680969 < baseStart_680969 := by decide
  rcases family_descends (prefixWord ++ tailWord_680969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680988 : List Nat := [2, 2, 3, 1, 4, 2, 1, 3, 4]
def baseStart_680988 : Nat := 118140960795 + 680988 * 2 ^ 59
def prefixEnd_680988 : Nat := 4983230072969 + 3 ^ 40 * 680988 * 2
def baseEnd_680988 : Nat := 77705369765352636670711

theorem tailTrace_680988 : CollatzResearch.WordTrace tailWord_680988 prefixEnd_680988 77705369765352636670711 := by
  unfold tailWord_680988
  simp only [CollatzResearch.WordTrace]
  refine ⟨12418836428452127168057809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16558448571269502890743745 12418836428452127168057809)
  ·
    refine ⟨9314127321339095376043357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12418836428452127168057809 9314127321339095376043357)
    ·
      refine ⟨3492797745502160766016259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9314127321339095376043357 3492797745502160766016259)
      ·
        refine ⟨5239196618253241149024389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3492797745502160766016259 5239196618253241149024389)
        ·
          refine ⟨982349365922482715442073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5239196618253241149024389 982349365922482715442073)
          ·
            refine ⟨736762024441862036581555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 982349365922482715442073 736762024441862036581555)
            ·
              refine ⟨1105143036662793054872333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 736762024441862036581555 1105143036662793054872333)
              ·
                refine ⟨414428638748547395577125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1105143036662793054872333 414428638748547395577125)
                ·
                  refine ⟨77705369765352636670711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 414428638748547395577125 77705369765352636670711)
                  ·
                    rfl

theorem cell22_680988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 3, 4].length) (baseStart_680988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_680988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_680988 prefixEnd_680988 := by exact prefixLift 680988
  have htrace : WordTrace (prefixWord ++ tailWord_680988) baseStart_680988 baseEnd_680988 := by
    simpa [prefixWord, tailWord_680988, baseEnd_680988] using wordTrace_append hprefix tailTrace_680988
  have hstable : (prefixWord ++ tailWord_680988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680988).length < 2 ^ (prefixWord ++ tailWord_680988).sum := by decide
  have hdescent : baseEnd_680988 < baseStart_680988 := by decide
  rcases family_descends (prefixWord ++ tailWord_680988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680999 : List Nat := [1, 1, 7, 1, 1, 1, 10]
def baseStart_680999 : Nat := 118140960795 + 680999 * 2 ^ 59
def prefixEnd_680999 : Nat := 4983230072969 + 3 ^ 40 * 680999 * 2
def baseEnd_680999 : Nat := 8634069437809538814337

theorem tailTrace_680999 : CollatzResearch.WordTrace tailWord_680999 prefixEnd_680999 8634069437809538814337 := by
  unfold tailWord_680999
  simp only [CollatzResearch.WordTrace]
  refine ⟨24838074059864403214766051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16558716039909602143177367 24838074059864403214766051)
  ·
    refine ⟨37257111089796604822149077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24838074059864403214766051 37257111089796604822149077)
    ·
      refine ⟨873213541167107925519119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 37257111089796604822149077 873213541167107925519119)
      ·
        refine ⟨1309820311750661888278679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 873213541167107925519119 1309820311750661888278679)
        ·
          refine ⟨1964730467625992832418019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1309820311750661888278679 1964730467625992832418019)
          ·
            refine ⟨2947095701438989248627029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1964730467625992832418019 2947095701438989248627029)
            ·
              refine ⟨8634069437809538814337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2947095701438989248627029 8634069437809538814337)
              ·
                rfl

theorem cell22_680999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 10].length) (baseStart_680999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_680999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_680999 prefixEnd_680999 := by exact prefixLift 680999
  have htrace : WordTrace (prefixWord ++ tailWord_680999) baseStart_680999 baseEnd_680999 := by
    simpa [prefixWord, tailWord_680999, baseEnd_680999] using wordTrace_append hprefix tailTrace_680999
  have hstable : (prefixWord ++ tailWord_680999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680999).length < 2 ^ (prefixWord ++ tailWord_680999).sum := by decide
  have hdescent : baseEnd_680999 < baseStart_680999 := by decide
  rcases family_descends (prefixWord ++ tailWord_680999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681065 : List Nat := [1, 2, 1, 1, 1, 8, 2, 2, 1, 3]
def baseStart_681065 : Nat := 118140960795 + 681065 * 2 ^ 59
def prefixEnd_681065 : Nat := 4983230072969 + 3 ^ 40 * 681065 * 2
def baseEnd_681065 : Nat := 233142467969655375836897

theorem tailTrace_681065 : CollatzResearch.WordTrace tailWord_681065 prefixEnd_681065 233142467969655375836897 := by
  unfold tailWord_681065
  simp only [CollatzResearch.WordTrace]
  refine ⟨24840481277625296486668649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16560320851750197657779099 24840481277625296486668649)
  ·
    refine ⟨18630360958218972365001487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24840481277625296486668649 18630360958218972365001487)
    ·
      refine ⟨27945541437328458547502231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18630360958218972365001487 27945541437328458547502231)
      ·
        refine ⟨41918312155992687821253347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27945541437328458547502231 41918312155992687821253347)
        ·
          refine ⟨62877468233989031731880021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41918312155992687821253347 62877468233989031731880021)
          ·
            refine ⟨736845330867058965607969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 62877468233989031731880021 736845330867058965607969)
            ·
              refine ⟨552633998150294224205977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 736845330867058965607969 552633998150294224205977)
              ·
                refine ⟨414475498612720668154483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 552633998150294224205977 414475498612720668154483)
                ·
                  refine ⟨621713247919081002231725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 414475498612720668154483 621713247919081002231725)
                  ·
                    refine ⟨233142467969655375836897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 621713247919081002231725 233142467969655375836897)
                    ·
                      rfl

theorem cell22_681065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 2, 1, 3].length) (baseStart_681065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_681065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_681065 prefixEnd_681065 := by exact prefixLift 681065
  have htrace : WordTrace (prefixWord ++ tailWord_681065) baseStart_681065 baseEnd_681065 := by
    simpa [prefixWord, tailWord_681065, baseEnd_681065] using wordTrace_append hprefix tailTrace_681065
  have hstable : (prefixWord ++ tailWord_681065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681065).length < 2 ^ (prefixWord ++ tailWord_681065).sum := by decide
  have hdescent : baseEnd_681065 < baseStart_681065 := by decide
  rcases family_descends (prefixWord ++ tailWord_681065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681074 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 5, 4]
def baseStart_681074 : Nat := 118140960795 + 681074 * 2 ^ 59
def prefixEnd_681074 : Nat := 4983230072969 + 3 ^ 40 * 681074 * 2
def baseEnd_681074 : Nat := 233145548853582352361869

theorem tailTrace_681074 : CollatzResearch.WordTrace tailWord_681074 prefixEnd_681074 233145548853582352361869 := by
  unfold tailWord_681074
  simp only [CollatzResearch.WordTrace]
  refine ⟨6210202383648172755936569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16560539689728460682497517 6210202383648172755936569)
  ·
    refine ⟨4657651787736129566952427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6210202383648172755936569 4657651787736129566952427)
    ·
      refine ⟨6986477681604194350428641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4657651787736129566952427 6986477681604194350428641)
      ·
        refine ⟨5239858261203145762821481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6986477681604194350428641 5239858261203145762821481)
        ·
          refine ⟨3929893695902359322116111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5239858261203145762821481 3929893695902359322116111)
          ·
            refine ⟨5894840543853538983174167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3929893695902359322116111 5894840543853538983174167)
            ·
              refine ⟨8842260815780308474761251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5894840543853538983174167 8842260815780308474761251)
              ·
                refine ⟨13263391223670462712141877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8842260815780308474761251 13263391223670462712141877)
                ·
                  refine ⟨1243442927219105879263301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13263391223670462712141877 1243442927219105879263301)
                  ·
                    refine ⟨233145548853582352361869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1243442927219105879263301 233145548853582352361869)
                    ·
                      rfl

theorem cell22_681074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_681074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_681074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_681074 prefixEnd_681074 := by exact prefixLift 681074
  have htrace : WordTrace (prefixWord ++ tailWord_681074) baseStart_681074 baseEnd_681074 := by
    simpa [prefixWord, tailWord_681074, baseEnd_681074] using wordTrace_append hprefix tailTrace_681074
  have hstable : (prefixWord ++ tailWord_681074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681074).length < 2 ^ (prefixWord ++ tailWord_681074).sum := by decide
  have hdescent : baseEnd_681074 < baseStart_681074 := by decide
  rcases family_descends (prefixWord ++ tailWord_681074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681089 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 8]
def baseStart_681089 : Nat := 118140960795 + 681089 * 2 ^ 59
def prefixEnd_681089 : Nat := 4983230072969 + 3 ^ 40 * 681089 * 2
def baseEnd_681089 : Nat := 77716894553375771078941

theorem tailTrace_681089 : CollatzResearch.WordTrace tailWord_681089 prefixEnd_681089 77716894553375771078941 := by
  unfold tailWord_681089
  simp only [CollatzResearch.WordTrace]
  refine ⟨24841356629538348585542321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16560904419692232390361547 24841356629538348585542321)
  ·
    refine ⟨18631017472153761439156741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24841356629538348585542321 18631017472153761439156741)
    ·
      refine ⟨3493315776028830269841889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18631017472153761439156741 3493315776028830269841889)
      ·
        refine ⟨2619986832021622702381417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3493315776028830269841889 2619986832021622702381417)
        ·
          refine ⟨1964990124016217026786063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2619986832021622702381417 1964990124016217026786063)
          ·
            refine ⟨2947485186024325540179095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1964990124016217026786063 2947485186024325540179095)
            ·
              refine ⟨4421227779036488310268643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2947485186024325540179095 4421227779036488310268643)
              ·
                refine ⟨6631841668554732465402965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4421227779036488310268643 6631841668554732465402965)
                ·
                  refine ⟨77716894553375771078941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6631841668554732465402965 77716894553375771078941)
                  ·
                    rfl

theorem cell22_681089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 8].length) (baseStart_681089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_681089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_681089 prefixEnd_681089 := by exact prefixLift 681089
  have htrace : WordTrace (prefixWord ++ tailWord_681089) baseStart_681089 baseEnd_681089 := by
    simpa [prefixWord, tailWord_681089, baseEnd_681089] using wordTrace_append hprefix tailTrace_681089
  have hstable : (prefixWord ++ tailWord_681089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681089).length < 2 ^ (prefixWord ++ tailWord_681089).sum := by decide
  have hdescent : baseEnd_681089 < baseStart_681089 := by decide
  rcases family_descends (prefixWord ++ tailWord_681089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681121 : List Nat := [1, 2, 3, 3, 1, 1, 3, 1, 4, 3]
def baseStart_681121 : Nat := 118140960795 + 681121 * 2 ^ 59
def prefixEnd_681121 : Nat := 4983230072969 + 3 ^ 40 * 681121 * 2
def baseEnd_681121 : Nat := 233161637914089896436725

theorem tailTrace_681121 : CollatzResearch.WordTrace tailWord_681121 prefixEnd_681121 233161637914089896436725 := by
  unfold tailWord_681121
  simp only [CollatzResearch.WordTrace]
  refine ⟨24842523765422418050707217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16561682510281612033804811 24842523765422418050707217)
  ·
    refine ⟨18631892824066813538030413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24842523765422418050707217 18631892824066813538030413)
    ·
      refine ⟨6986959809025055076761405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18631892824066813538030413 6986959809025055076761405)
      ·
        refine ⟨2620109928384395653785527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6986959809025055076761405 2620109928384395653785527)
        ·
          refine ⟨3930164892576593480678291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2620109928384395653785527 3930164892576593480678291)
          ·
            refine ⟨5895247338864890221017437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3930164892576593480678291 5895247338864890221017437)
            ·
              refine ⟨2210717752074333832881539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5895247338864890221017437 2210717752074333832881539)
              ·
                refine ⟨3316076628111500749322309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2210717752074333832881539 3316076628111500749322309)
                ·
                  refine ⟨621764367770906390497933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3316076628111500749322309 621764367770906390497933)
                  ·
                    refine ⟨233161637914089896436725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 621764367770906390497933 233161637914089896436725)
                    ·
                      rfl

theorem cell22_681121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_681121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_681121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_681121 prefixEnd_681121 := by exact prefixLift 681121
  have htrace : WordTrace (prefixWord ++ tailWord_681121) baseStart_681121 baseEnd_681121 := by
    simpa [prefixWord, tailWord_681121, baseEnd_681121] using wordTrace_append hprefix tailTrace_681121
  have hstable : (prefixWord ++ tailWord_681121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681121).length < 2 ^ (prefixWord ++ tailWord_681121).sum := by decide
  have hdescent : baseEnd_681121 < baseStart_681121 := by decide
  rcases family_descends (prefixWord ++ tailWord_681121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681142 : List Nat := [5, 1, 3, 2, 1, 1, 2, 2, 1, 4]
def baseStart_681142 : Nat := 118140960795 + 681142 * 2 ^ 59
def prefixEnd_681142 : Nat := 4983230072969 + 3 ^ 40 * 681142 * 2
def baseEnd_681142 : Nat := 233168826643252841661661

theorem tailTrace_681142 : CollatzResearch.WordTrace tailWord_681142 prefixEnd_681142 233168826643252841661661 := by
  unfold tailWord_681142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1552705606146646164826355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16562193132230892424814453 1552705606146646164826355)
  ·
    refine ⟨2329058409219969247239533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1552705606146646164826355 2329058409219969247239533)
    ·
      refine ⟨873396903457488467714825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2329058409219969247239533 873396903457488467714825)
      ·
        refine ⟨655047677593116350786119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 873396903457488467714825 655047677593116350786119)
        ·
          refine ⟨982571516389674526179179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 655047677593116350786119 982571516389674526179179)
          ·
            refine ⟨1473857274584511789268769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 982571516389674526179179 1473857274584511789268769)
            ·
              refine ⟨1105392955938383841951577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1473857274584511789268769 1105392955938383841951577)
              ·
                refine ⟨829044716953787881463683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1105392955938383841951577 829044716953787881463683)
                ·
                  refine ⟨1243567075430681822195525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 829044716953787881463683 1243567075430681822195525)
                  ·
                    refine ⟨233168826643252841661661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1243567075430681822195525 233168826643252841661661)
                    ·
                      rfl

theorem cell22_681142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_681142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_681142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_681142 prefixEnd_681142 := by exact prefixLift 681142
  have htrace : WordTrace (prefixWord ++ tailWord_681142) baseStart_681142 baseEnd_681142 := by
    simpa [prefixWord, tailWord_681142, baseEnd_681142] using wordTrace_append hprefix tailTrace_681142
  have hstable : (prefixWord ++ tailWord_681142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681142).length < 2 ^ (prefixWord ++ tailWord_681142).sum := by decide
  have hdescent : baseEnd_681142 < baseStart_681142 := by decide
  rcases family_descends (prefixWord ++ tailWord_681142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681183 : List Nat := [1, 1, 2, 3, 2, 1, 2, 6, 1, 3]
def baseStart_681183 : Nat := 118140960795 + 681183 * 2 ^ 59
def prefixEnd_681183 : Nat := 4983230072969 + 3 ^ 40 * 681183 * 2
def baseEnd_681183 : Nat := 233182861781142401386535

theorem tailTrace_681183 : CollatzResearch.WordTrace tailWord_681183 prefixEnd_681183 233182861781142401386535 := by
  unfold tailWord_681183
  simp only [CollatzResearch.WordTrace]
  refine ⟨24844785091197802639464203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16563190060798535092976135 24844785091197802639464203)
  ·
    refine ⟨37267177636796703959196305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24844785091197802639464203 37267177636796703959196305)
    ·
      refine ⟨27950383227597527969397229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37267177636796703959196305 27950383227597527969397229)
      ·
        refine ⟨10481393710349072988523961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27950383227597527969397229 10481393710349072988523961)
        ·
          refine ⟨7861045282761804741392971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10481393710349072988523961 7861045282761804741392971)
          ·
            refine ⟨11791567924142707112089457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7861045282761804741392971 11791567924142707112089457)
            ·
              refine ⟨8843675943107030334067093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11791567924142707112089457 8843675943107030334067093)
              ·
                refine ⟨414547309833142046909395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8843675943107030334067093 414547309833142046909395)
                ·
                  refine ⟨621820964749713070364093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 414547309833142046909395 621820964749713070364093)
                  ·
                    refine ⟨233182861781142401386535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 621820964749713070364093 233182861781142401386535)
                    ·
                      rfl

theorem cell22_681183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 6, 1, 3].length) (baseStart_681183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_681183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_681183 prefixEnd_681183 := by exact prefixLift 681183
  have htrace : WordTrace (prefixWord ++ tailWord_681183) baseStart_681183 baseEnd_681183 := by
    simpa [prefixWord, tailWord_681183, baseEnd_681183] using wordTrace_append hprefix tailTrace_681183
  have hstable : (prefixWord ++ tailWord_681183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681183).length < 2 ^ (prefixWord ++ tailWord_681183).sum := by decide
  have hdescent : baseEnd_681183 < baseStart_681183 := by decide
  rcases family_descends (prefixWord ++ tailWord_681183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681196 : List Nat := [2, 2, 1, 1, 2, 5, 1, 3, 5]
def baseStart_681196 : Nat := 118140960795 + 681196 * 2 ^ 59
def prefixEnd_681196 : Nat := 4983230072969 + 3 ^ 40 * 681196 * 2
def baseEnd_681196 : Nat := 77729103982271566937165

theorem tailTrace_681196 : CollatzResearch.WordTrace tailWord_681196 prefixEnd_681196 77729103982271566937165 := by
  unfold tailWord_681196
  simp only [CollatzResearch.WordTrace]
  refine ⟨12422629620075352929843721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16563506160100470573124961 12422629620075352929843721)
  ·
    refine ⟨9316972215056514697382791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12422629620075352929843721 9316972215056514697382791)
    ·
      refine ⟨13975458322584772046074187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9316972215056514697382791 13975458322584772046074187)
      ·
        refine ⟨20963187483877158069111281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13975458322584772046074187 20963187483877158069111281)
        ·
          refine ⟨15722390612907868551833461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20963187483877158069111281 15722390612907868551833461)
          ·
            refine ⟨1473974119960112676734387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15722390612907868551833461 1473974119960112676734387)
            ·
              refine ⟨2210961179940169015101581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1473974119960112676734387 2210961179940169015101581)
              ·
                refine ⟨829110442477563380663093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2210961179940169015101581 829110442477563380663093)
                ·
                  refine ⟨77729103982271566937165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 829110442477563380663093 77729103982271566937165)
                  ·
                    rfl

theorem cell22_681196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 5].length) (baseStart_681196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_681196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_681196 prefixEnd_681196 := by exact prefixLift 681196
  have htrace : WordTrace (prefixWord ++ tailWord_681196) baseStart_681196 baseEnd_681196 := by
    simpa [prefixWord, tailWord_681196, baseEnd_681196] using wordTrace_append hprefix tailTrace_681196
  have hstable : (prefixWord ++ tailWord_681196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681196).length < 2 ^ (prefixWord ++ tailWord_681196).sum := by decide
  have hdescent : baseEnd_681196 < baseStart_681196 := by decide
  rcases family_descends (prefixWord ++ tailWord_681196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681234 : List Nat := [3, 2, 4, 2, 1, 1, 1, 4, 1, 3]
def baseStart_681234 : Nat := 118140960795 + 681234 * 2 ^ 59
def prefixEnd_681234 : Nat := 4983230072969 + 3 ^ 40 * 681234 * 2
def baseEnd_681234 : Nat := 233200320123395268361379

theorem tailTrace_681234 : CollatzResearch.WordTrace tailWord_681234 prefixEnd_681234 233200320123395268361379 := by
  unfold tailWord_681234
  simp only [CollatzResearch.WordTrace]
  refine ⟨6211661303503259587392689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16564430142675358899713837 6211661303503259587392689)
  ·
    refine ⟨4658745977627444690544517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6211661303503259587392689 4658745977627444690544517)
    ·
      refine ⟨873514870805145879477097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4658745977627444690544517 873514870805145879477097)
      ·
        refine ⟨655136153103859409607823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 873514870805145879477097 655136153103859409607823)
        ·
          refine ⟨982704229655789114411735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 655136153103859409607823 982704229655789114411735)
          ·
            refine ⟨1474056344483683671617603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 982704229655789114411735 1474056344483683671617603)
            ·
              refine ⟨2211084516725525507426405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1474056344483683671617603 2211084516725525507426405)
              ·
                refine ⟨414578346886036032642451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2211084516725525507426405 414578346886036032642451)
                ·
                  refine ⟨621867520329054048963677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 414578346886036032642451 621867520329054048963677)
                  ·
                    refine ⟨233200320123395268361379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 621867520329054048963677 233200320123395268361379)
                    ·
                      rfl

theorem cell22_681234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_681234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_681234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_681234 prefixEnd_681234 := by exact prefixLift 681234
  have htrace : WordTrace (prefixWord ++ tailWord_681234) baseStart_681234 baseEnd_681234 := by
    simpa [prefixWord, tailWord_681234, baseEnd_681234] using wordTrace_append hprefix tailTrace_681234
  have hstable : (prefixWord ++ tailWord_681234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681234).length < 2 ^ (prefixWord ++ tailWord_681234).sum := by decide
  have hdescent : baseEnd_681234 < baseStart_681234 := by decide
  rcases family_descends (prefixWord ++ tailWord_681234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681258 : List Nat := [3, 1, 4, 2, 1, 2, 1, 2, 6]
def baseStart_681258 : Nat := 118140960795 + 681258 * 2 ^ 59
def prefixEnd_681258 : Nat := 4983230072969 + 3 ^ 40 * 681258 * 2
def baseEnd_681258 : Nat := 77736178604622401920435

theorem tailTrace_681258 : CollatzResearch.WordTrace tailWord_681258 prefixEnd_681258 77736178604622401920435 := by
  unfold tailWord_681258
  simp only [CollatzResearch.WordTrace]
  refine ⟨6211880141481522612111107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16565013710617393632296285 6211880141481522612111107)
  ·
    refine ⟨9317820212222283918166661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6211880141481522612111107 9317820212222283918166661)
    ·
      refine ⟨1747091289791678234656249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9317820212222283918166661 1747091289791678234656249)
      ·
        refine ⟨1310318467343758675992187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1747091289791678234656249 1310318467343758675992187)
        ·
          refine ⟨1965477701015638013988281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1310318467343758675992187 1965477701015638013988281)
          ·
            refine ⟨1474108275761728510491211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1965477701015638013988281 1474108275761728510491211)
            ·
              refine ⟨2211162413642592765736817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1474108275761728510491211 2211162413642592765736817)
              ·
                refine ⟨1658371810231944574302613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2211162413642592765736817 1658371810231944574302613)
                ·
                  refine ⟨77736178604622401920435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1658371810231944574302613 77736178604622401920435)
                  ·
                    rfl

theorem cell22_681258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 6].length) (baseStart_681258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_681258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_681258 prefixEnd_681258 := by exact prefixLift 681258
  have htrace : WordTrace (prefixWord ++ tailWord_681258) baseStart_681258 baseEnd_681258 := by
    simpa [prefixWord, tailWord_681258, baseEnd_681258] using wordTrace_append hprefix tailTrace_681258
  have hstable : (prefixWord ++ tailWord_681258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681258).length < 2 ^ (prefixWord ++ tailWord_681258).sum := by decide
  have hdescent : baseEnd_681258 < baseStart_681258 := by decide
  rcases family_descends (prefixWord ++ tailWord_681258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681320 : List Nat := [2, 1, 4, 2, 3, 2, 2, 6]
def baseStart_681320 : Nat := 118140960795 + 681320 * 2 ^ 59
def prefixEnd_681320 : Nat := 4983230072969 + 3 ^ 40 * 681320 * 2
def baseEnd_681320 : Nat := 25914417742324412301235

theorem tailTrace_681320 : CollatzResearch.WordTrace tailWord_681320 prefixEnd_681320 25914417742324412301235 := by
  unfold tailWord_681320
  simp only [CollatzResearch.WordTrace]
  refine ⟨12424890945850737518600707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16566521261134316691467609 12424890945850737518600707)
  ·
    refine ⟨18637336418776106277901061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12424890945850737518600707 18637336418776106277901061)
    ·
      refine ⟨3494500578520519927106449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18637336418776106277901061 3494500578520519927106449)
      ·
        refine ⟨2620875433890389945329837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3494500578520519927106449 2620875433890389945329837)
        ·
          refine ⟨982828287708896229498689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2620875433890389945329837 982828287708896229498689)
          ·
            refine ⟨737121215781672172124017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 982828287708896229498689 737121215781672172124017)
            ·
              refine ⟨552840911836254129093013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 737121215781672172124017 552840911836254129093013)
              ·
                refine ⟨25914417742324412301235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 552840911836254129093013 25914417742324412301235)
                ·
                  rfl

theorem cell22_681320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 6].length) (baseStart_681320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_681320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_681320 prefixEnd_681320 := by exact prefixLift 681320
  have htrace : WordTrace (prefixWord ++ tailWord_681320) baseStart_681320 baseEnd_681320 := by
    simpa [prefixWord, tailWord_681320, baseEnd_681320] using wordTrace_append hprefix tailTrace_681320
  have hstable : (prefixWord ++ tailWord_681320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681320).length < 2 ^ (prefixWord ++ tailWord_681320).sum := by decide
  have hdescent : baseEnd_681320 < baseStart_681320 := by decide
  rcases family_descends (prefixWord ++ tailWord_681320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681361 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 5, 4]
def baseStart_681361 : Nat := 118140960795 + 681361 * 2 ^ 59
def prefixEnd_681361 : Nat := 4983230072969 + 3 ^ 40 * 681361 * 2
def baseEnd_681361 : Nat := 233243794818809270435989

theorem tailTrace_681361 : CollatzResearch.WordTrace tailWord_681361 prefixEnd_681361 233243794818809270435989 := by
  unfold tailWord_681361
  simp only [CollatzResearch.WordTrace]
  refine ⟨24851277284552939039443937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16567518189701959359629291 24851277284552939039443937)
  ·
    refine ⟨18638457963414704279582953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24851277284552939039443937 18638457963414704279582953)
    ·
      refine ⟨13978843472561028209687215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18638457963414704279582953 13978843472561028209687215)
      ·
        refine ⟨20968265208841542314530823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13978843472561028209687215 20968265208841542314530823)
        ·
          refine ⟨31452397813262313471796235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20968265208841542314530823 31452397813262313471796235)
          ·
            refine ⟨47178596719893470207694353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31452397813262313471796235 47178596719893470207694353)
            ·
              refine ⟨35383947539920102655770765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47178596719893470207694353 35383947539920102655770765)
              ·
                refine ⟨13268980327470038495914037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35383947539920102655770765 13268980327470038495914037)
                ·
                  refine ⟨1243966905700316108991941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13268980327470038495914037 1243966905700316108991941)
                  ·
                    refine ⟨233243794818809270435989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1243966905700316108991941 233243794818809270435989)
                    ·
                      rfl

theorem cell22_681361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_681361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_681361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_681361 prefixEnd_681361 := by exact prefixLift 681361
  have htrace : WordTrace (prefixWord ++ tailWord_681361) baseStart_681361 baseEnd_681361 := by
    simpa [prefixWord, tailWord_681361, baseEnd_681361] using wordTrace_append hprefix tailTrace_681361
  have hstable : (prefixWord ++ tailWord_681361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681361).length < 2 ^ (prefixWord ++ tailWord_681361).sum := by decide
  have hdescent : baseEnd_681361 < baseStart_681361 := by decide
  rcases family_descends (prefixWord ++ tailWord_681361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681376 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 8]
def baseStart_681376 : Nat := 118140960795 + 681376 * 2 ^ 59
def prefixEnd_681376 : Nat := 4983230072969 + 3 ^ 40 * 681376 * 2
def baseEnd_681376 : Nat := 77749643208451410436981

theorem tailTrace_681376 : CollatzResearch.WordTrace tailWord_681376 prefixEnd_681376 77749643208451410436981 := by
  unfold tailWord_681376
  simp only [CollatzResearch.WordTrace]
  refine ⟨12425912189749298300619991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16567882919665731067493321 12425912189749298300619991)
  ·
    refine ⟨18638868284623947450929987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12425912189749298300619991 18638868284623947450929987)
    ·
      refine ⟨27958302426935921176394981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18638868284623947450929987 27958302426935921176394981)
      ·
        refine ⟨5242181705050485220574059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27958302426935921176394981 5242181705050485220574059)
        ·
          refine ⟨7863272557575727830861089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5242181705050485220574059 7863272557575727830861089)
          ·
            refine ⟨5897454418181795873145817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7863272557575727830861089 5897454418181795873145817)
            ·
              refine ⟨4423090813636346904859363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5897454418181795873145817 4423090813636346904859363)
              ·
                refine ⟨6634636220454520357289045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4423090813636346904859363 6634636220454520357289045)
                ·
                  refine ⟨77749643208451410436981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6634636220454520357289045 77749643208451410436981)
                  ·
                    rfl

theorem cell22_681376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 8].length) (baseStart_681376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_681376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_681376 prefixEnd_681376 := by exact prefixLift 681376
  have htrace : WordTrace (prefixWord ++ tailWord_681376) baseStart_681376 baseEnd_681376 := by
    simpa [prefixWord, tailWord_681376, baseEnd_681376] using wordTrace_append hprefix tailTrace_681376
  have hstable : (prefixWord ++ tailWord_681376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681376).length < 2 ^ (prefixWord ++ tailWord_681376).sum := by decide
  have hdescent : baseEnd_681376 < baseStart_681376 := by decide
  rcases family_descends (prefixWord ++ tailWord_681376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681408 : List Nat := [2, 1, 1, 2, 3, 1, 2, 3, 4, 3]
def baseStart_681408 : Nat := 118140960795 + 681408 * 2 ^ 59
def prefixEnd_681408 : Nat := 4983230072969 + 3 ^ 40 * 681408 * 2
def baseEnd_681408 : Nat := 233259883879316814510845

theorem tailTrace_681408 : CollatzResearch.WordTrace tailWord_681408 prefixEnd_681408 233259883879316814510845 := by
  unfold tailWord_681408
  simp only [CollatzResearch.WordTrace]
  refine ⟨12426495757691333033202439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16568661010255110710936585 12426495757691333033202439)
  ·
    refine ⟨18639743636536999549803659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12426495757691333033202439 18639743636536999549803659)
    ·
      refine ⟨27959615454805499324705489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18639743636536999549803659 27959615454805499324705489)
      ·
        refine ⟨20969711591104124493529117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27959615454805499324705489 20969711591104124493529117)
        ·
          refine ⟨7863641846664046685073419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20969711591104124493529117 7863641846664046685073419)
          ·
            refine ⟨11795462769996070027610129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7863641846664046685073419 11795462769996070027610129)
            ·
              refine ⟨8846597077497052520707597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11795462769996070027610129 8846597077497052520707597)
              ·
                refine ⟨3317473904061394695265349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8846597077497052520707597 3317473904061394695265349)
                ·
                  refine ⟨622026357011511505362253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3317473904061394695265349 622026357011511505362253)
                  ·
                    refine ⟨233259883879316814510845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 622026357011511505362253 233259883879316814510845)
                    ·
                      rfl

theorem cell22_681408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 4, 3].length) (baseStart_681408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_681408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_681408 prefixEnd_681408 := by exact prefixLift 681408
  have htrace : WordTrace (prefixWord ++ tailWord_681408) baseStart_681408 baseEnd_681408 := by
    simpa [prefixWord, tailWord_681408, baseEnd_681408] using wordTrace_append hprefix tailTrace_681408
  have hstable : (prefixWord ++ tailWord_681408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681408).length < 2 ^ (prefixWord ++ tailWord_681408).sum := by decide
  have hdescent : baseEnd_681408 < baseStart_681408 := by decide
  rcases family_descends (prefixWord ++ tailWord_681408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681451 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 1, 8]
def baseStart_681451 : Nat := 118140960795 + 681451 * 2 ^ 59
def prefixEnd_681451 : Nat := 4983230072969 + 3 ^ 40 * 681451 * 2
def baseEnd_681451 : Nat := 233274603658079035685713

theorem tailTrace_681451 : CollatzResearch.WordTrace tailWord_681451 prefixEnd_681451 233274603658079035685713 := by
  unfold tailWord_681451
  simp only [CollatzResearch.WordTrace]
  refine ⟨24854559854226884410220207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16569706569484589606813471 24854559854226884410220207)
  ·
    refine ⟨37281839781340326615330311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24854559854226884410220207 37281839781340326615330311)
    ·
      refine ⟨55922759672010489922995467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37281839781340326615330311 55922759672010489922995467)
      ·
        refine ⟨83884139508015734884493201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55922759672010489922995467 83884139508015734884493201)
        ·
          refine ⟨62913104631011801163369901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83884139508015734884493201 62913104631011801163369901)
          ·
            refine ⟨23592414236629425436263713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62913104631011801163369901 23592414236629425436263713)
            ·
              refine ⟨17694310677472069077197785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23592414236629425436263713 17694310677472069077197785)
              ·
                refine ⟨13270733008104051807898339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17694310677472069077197785 13270733008104051807898339)
                ·
                  refine ⟨19906099512156077711847509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13270733008104051807898339 19906099512156077711847509)
                  ·
                    refine ⟨233274603658079035685713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 19906099512156077711847509 233274603658079035685713)
                    ·
                      rfl

theorem cell22_681451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 8].length) (baseStart_681451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_681451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_681451 prefixEnd_681451 := by exact prefixLift 681451
  have htrace : WordTrace (prefixWord ++ tailWord_681451) baseStart_681451 baseEnd_681451 := by
    simpa [prefixWord, tailWord_681451, baseEnd_681451] using wordTrace_append hprefix tailTrace_681451
  have hstable : (prefixWord ++ tailWord_681451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681451).length < 2 ^ (prefixWord ++ tailWord_681451).sum := by decide
  have hdescent : baseEnd_681451 < baseStart_681451 := by decide
  rcases family_descends (prefixWord ++ tailWord_681451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681504 : List Nat := [2, 1, 1, 6, 1, 1, 3, 3, 1, 3]
def baseStart_681504 : Nat := 118140960795 + 681504 * 2 ^ 59
def prefixEnd_681504 : Nat := 4983230072969 + 3 ^ 40 * 681504 * 2
def baseEnd_681504 : Nat := 233292746641204564110551

theorem tailTrace_681504 : CollatzResearch.WordTrace tailWord_681504 prefixEnd_681504 233292746641204564110551 := by
  unfold tailWord_681504
  simp only [CollatzResearch.WordTrace]
  refine ⟨12428246461517437230949783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16570995282023249641266377 12428246461517437230949783)
  ·
    refine ⟨18642369692276155846424675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12428246461517437230949783 18642369692276155846424675)
    ·
      refine ⟨27963554538414233769637013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18642369692276155846424675 27963554538414233769637013)
      ·
        refine ⟨1310791618988167207951735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27963554538414233769637013 1310791618988167207951735)
        ·
          refine ⟨1966187428482250811927603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1310791618988167207951735 1966187428482250811927603)
          ·
            refine ⟨2949281142723376217891405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1966187428482250811927603 2949281142723376217891405)
            ·
              refine ⟨1105980428521266081709277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2949281142723376217891405 1105980428521266081709277)
              ·
                refine ⟨414742660695474780640979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1105980428521266081709277 414742660695474780640979)
                ·
                  refine ⟨622113991043212170961469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 414742660695474780640979 622113991043212170961469)
                  ·
                    refine ⟨233292746641204564110551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 622113991043212170961469 233292746641204564110551)
                    ·
                      rfl

theorem cell22_681504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 3, 1, 3].length) (baseStart_681504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_681504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_681504 prefixEnd_681504 := by exact prefixLift 681504
  have htrace : WordTrace (prefixWord ++ tailWord_681504) baseStart_681504 baseEnd_681504 := by
    simpa [prefixWord, tailWord_681504, baseEnd_681504] using wordTrace_append hprefix tailTrace_681504
  have hstable : (prefixWord ++ tailWord_681504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681504).length < 2 ^ (prefixWord ++ tailWord_681504).sum := by decide
  have hdescent : baseEnd_681504 < baseStart_681504 := by decide
  rcases family_descends (prefixWord ++ tailWord_681504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681564 : List Nat := [2, 2, 4, 1, 2, 2, 3, 1, 1, 4]
def baseStart_681564 : Nat := 118140960795 + 681564 * 2 ^ 59
def prefixEnd_681564 : Nat := 4983230072969 + 3 ^ 40 * 681564 * 2
def baseEnd_681564 : Nat := 233313285867384407610367

theorem tailTrace_681564 : CollatzResearch.WordTrace tailWord_681564 prefixEnd_681564 233313285867384407610367 := by
  unfold tailWord_681564
  simp only [CollatzResearch.WordTrace]
  refine ⟨12429340651408752354541873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16572454201878336472722497 12429340651408752354541873)
  ·
    refine ⟨9322005488556564265906405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12429340651408752354541873 9322005488556564265906405)
    ·
      refine ⟨1747876029104355799857451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9322005488556564265906405 1747876029104355799857451)
      ·
        refine ⟨2621814043656533699786177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1747876029104355799857451 2621814043656533699786177)
        ·
          refine ⟨1966360532742400274839633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2621814043656533699786177 1966360532742400274839633)
          ·
            refine ⟨1474770399556800206129725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1966360532742400274839633 1474770399556800206129725)
            ·
              refine ⟨553038899833800077298647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1474770399556800206129725 553038899833800077298647)
              ·
                refine ⟨829558349750700115947971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 553038899833800077298647 829558349750700115947971)
                ·
                  refine ⟨1244337524626050173921957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 829558349750700115947971 1244337524626050173921957)
                  ·
                    refine ⟨233313285867384407610367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1244337524626050173921957 233313285867384407610367)
                    ·
                      rfl

theorem cell22_681564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_681564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_681564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_681564 prefixEnd_681564 := by exact prefixLift 681564
  have htrace : WordTrace (prefixWord ++ tailWord_681564) baseStart_681564 baseEnd_681564 := by
    simpa [prefixWord, tailWord_681564, baseEnd_681564] using wordTrace_append hprefix tailTrace_681564
  have hstable : (prefixWord ++ tailWord_681564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681564).length < 2 ^ (prefixWord ++ tailWord_681564).sum := by decide
  have hdescent : baseEnd_681564 < baseStart_681564 := by decide
  rcases family_descends (prefixWord ++ tailWord_681564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681573 : List Nat := [1, 3, 1, 3, 3, 11]
def baseStart_681573 : Nat := 118140960795 + 681573 * 2 ^ 59
def prefixEnd_681573 : Nat := 4983230072969 + 3 ^ 40 * 681573 * 2
def baseEnd_681573 : Nat := 2880448972238412149819

theorem tailTrace_681573 : CollatzResearch.WordTrace tailWord_681573 prefixEnd_681573 2880448972238412149819 := by
  unfold tailWord_681573
  simp only [CollatzResearch.WordTrace]
  refine ⟨24859009559784899246161373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16572673039856599497440915 24859009559784899246161373)
  ·
    refine ⟨9322128584919337217310515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24859009559784899246161373 9322128584919337217310515)
    ·
      refine ⟨13983192877379005825965773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9322128584919337217310515 13983192877379005825965773)
      ·
        refine ⟨5243697329017127184737165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13983192877379005825965773 5243697329017127184737165)
        ·
          refine ⟨1966386498381422694276437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5243697329017127184737165 1966386498381422694276437)
          ·
            refine ⟨2880448972238412149819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1966386498381422694276437 2880448972238412149819)
            ·
              rfl

theorem cell22_681573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 11].length) (baseStart_681573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_681573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_681573 prefixEnd_681573 := by exact prefixLift 681573
  have htrace : WordTrace (prefixWord ++ tailWord_681573) baseStart_681573 baseEnd_681573 := by
    simpa [prefixWord, tailWord_681573, baseEnd_681573] using wordTrace_append hprefix tailTrace_681573
  have hstable : (prefixWord ++ tailWord_681573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681573).length < 2 ^ (prefixWord ++ tailWord_681573).sum := by decide
  have hdescent : baseEnd_681573 < baseStart_681573 := by decide
  rcases family_descends (prefixWord ++ tailWord_681573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681575 : List Nat := [1, 1, 5, 1, 1, 1, 4, 2, 2, 4]
def baseStart_681575 : Nat := 118140960795 + 681575 * 2 ^ 59
def prefixEnd_681575 : Nat := 4983230072969 + 3 ^ 40 * 681575 * 2
def baseEnd_681575 : Nat := 233317051392184045585333

theorem tailTrace_681575 : CollatzResearch.WordTrace tailWord_681575 prefixEnd_681575 233317051392184045585333 := by
  unfold tailWord_681575
  simp only [CollatzResearch.WordTrace]
  refine ⟨24859082505777653587734179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16572721670518435725156119 24859082505777653587734179)
  ·
    refine ⟨37288623758666480381601269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24859082505777653587734179 37288623758666480381601269)
    ·
      refine ⟨3495808477374982535775119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37288623758666480381601269 3495808477374982535775119)
      ·
        refine ⟨5243712716062473803662679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3495808477374982535775119 5243712716062473803662679)
        ·
          refine ⟨7865569074093710705494019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5243712716062473803662679 7865569074093710705494019)
          ·
            refine ⟨11798353611140566058241029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7865569074093710705494019 11798353611140566058241029)
            ·
              refine ⟨2212191302088856135920193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11798353611140566058241029 2212191302088856135920193)
              ·
                refine ⟨1659143476566642101940145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2212191302088856135920193 1659143476566642101940145)
                ·
                  refine ⟨1244357607424981576455109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1659143476566642101940145 1244357607424981576455109)
                  ·
                    refine ⟨233317051392184045585333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1244357607424981576455109 233317051392184045585333)
                    ·
                      rfl

theorem cell22_681575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_681575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_681575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_681575 prefixEnd_681575 := by exact prefixLift 681575
  have htrace : WordTrace (prefixWord ++ tailWord_681575) baseStart_681575 baseEnd_681575 := by
    simpa [prefixWord, tailWord_681575, baseEnd_681575] using wordTrace_append hprefix tailTrace_681575
  have hstable : (prefixWord ++ tailWord_681575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681575).length < 2 ^ (prefixWord ++ tailWord_681575).sum := by decide
  have hdescent : baseEnd_681575 < baseStart_681575 := by decide
  rcases family_descends (prefixWord ++ tailWord_681575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681603 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 4, 6]
def baseStart_681603 : Nat := 118140960795 + 681603 * 2 ^ 59
def prefixEnd_681603 : Nat := 4983230072969 + 3 ^ 40 * 681603 * 2
def baseEnd_681603 : Nat := 233326636364401305885247

theorem tailTrace_681603 : CollatzResearch.WordTrace tailWord_681603 prefixEnd_681603 233326636364401305885247 := by
  unfold tailWord_681603
  simp only [CollatzResearch.WordTrace]
  refine ⟨24860103749676214369753463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16573402499784142913168975 24860103749676214369753463)
  ·
    refine ⟨37290155624514321554630195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24860103749676214369753463 37290155624514321554630195)
    ·
      refine ⟨55935233436771482331945293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37290155624514321554630195 55935233436771482331945293)
      ·
        refine ⟨20975712538789305874479485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55935233436771482331945293 20975712538789305874479485)
        ·
          refine ⟨7865892202045989702929807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20975712538789305874479485 7865892202045989702929807)
          ·
            refine ⟨11798838303068984554394711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7865892202045989702929807 11798838303068984554394711)
            ·
              refine ⟨17698257454603476831592067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11798838303068984554394711 17698257454603476831592067)
              ·
                refine ⟨26547386181905215247388101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17698257454603476831592067 26547386181905215247388101)
                ·
                  refine ⟨4977634909107227858885269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26547386181905215247388101 4977634909107227858885269)
                  ·
                    refine ⟨233326636364401305885247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4977634909107227858885269 233326636364401305885247)
                    ·
                      rfl

theorem cell22_681603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 6].length) (baseStart_681603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_681603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_681603 prefixEnd_681603 := by exact prefixLift 681603
  have htrace : WordTrace (prefixWord ++ tailWord_681603) baseStart_681603 baseEnd_681603 := by
    simpa [prefixWord, tailWord_681603, baseEnd_681603] using wordTrace_append hprefix tailTrace_681603
  have hstable : (prefixWord ++ tailWord_681603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681603).length < 2 ^ (prefixWord ++ tailWord_681603).sum := by decide
  have hdescent : baseEnd_681603 < baseStart_681603 := by decide
  rcases family_descends (prefixWord ++ tailWord_681603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681650 : List Nat := [3, 2, 1, 1, 1, 2, 4, 1, 2, 5]
def baseStart_681650 : Nat := 118140960795 + 681650 * 2 ^ 59
def prefixEnd_681650 : Nat := 4983230072969 + 3 ^ 40 * 681650 * 2
def baseEnd_681650 : Nat := 233342725424908849960103

theorem tailTrace_681650 : CollatzResearch.WordTrace tailWord_681650 prefixEnd_681650 233342725424908849960103 := by
  unfold tailWord_681650
  simp only [CollatzResearch.WordTrace]
  refine ⟨6215454495126485349178601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16574545320337294264476269 6215454495126485349178601)
  ·
    refine ⟨4661590871344864011883951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6215454495126485349178601 4661590871344864011883951)
    ·
      refine ⟨6992386307017296017825927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4661590871344864011883951 6992386307017296017825927)
      ·
        refine ⟨10488579460525944026738891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6992386307017296017825927 10488579460525944026738891)
        ·
          refine ⟨15732869190788916040108337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10488579460525944026738891 15732869190788916040108337)
          ·
            refine ⟨11799651893091687030081253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15732869190788916040108337 11799651893091687030081253)
            ·
              refine ⟨2212434729954691318140235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11799651893091687030081253 2212434729954691318140235)
              ·
                refine ⟨3318652094932036977210353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2212434729954691318140235 3318652094932036977210353)
                ·
                  refine ⟨2488989071199027732907765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3318652094932036977210353 2488989071199027732907765)
                  ·
                    refine ⟨233342725424908849960103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2488989071199027732907765 233342725424908849960103)
                    ·
                      rfl

theorem cell22_681650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_681650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_681650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_681650 prefixEnd_681650 := by exact prefixLift 681650
  have htrace : WordTrace (prefixWord ++ tailWord_681650) baseStart_681650 baseEnd_681650 := by
    simpa [prefixWord, tailWord_681650, baseEnd_681650] using wordTrace_append hprefix tailTrace_681650
  have hstable : (prefixWord ++ tailWord_681650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681650).length < 2 ^ (prefixWord ++ tailWord_681650).sum := by decide
  have hdescent : baseEnd_681650 < baseStart_681650 := by decide
  rcases family_descends (prefixWord ++ tailWord_681650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681703 : List Nat := [1, 1, 5, 4, 2, 1, 2, 1, 5]
def baseStart_681703 : Nat := 118140960795 + 681703 * 2 ^ 59
def prefixEnd_681703 : Nat := 4983230072969 + 3 ^ 40 * 681703 * 2
def baseEnd_681703 : Nat := 77786956136011459461647

theorem tailTrace_681703 : CollatzResearch.WordTrace tailWord_681703 prefixEnd_681703 77786956136011459461647 := by
  unfold tailWord_681703
  simp only [CollatzResearch.WordTrace]
  refine ⟨24863751049313931448393763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16575834032875954298929175 24863751049313931448393763)
  ·
    refine ⟨37295626573970897172590645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24863751049313931448393763 37295626573970897172590645)
    ·
      refine ⟨3496464991309771609930373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37295626573970897172590645 3496464991309771609930373)
      ·
        refine ⟨655587185870582176861945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3496464991309771609930373 655587185870582176861945)
        ·
          refine ⟨491690389402936632646459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 655587185870582176861945 491690389402936632646459)
          ·
            refine ⟨737535584104404948969689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491690389402936632646459 737535584104404948969689)
            ·
              refine ⟨553151688078303711727267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 737535584104404948969689 553151688078303711727267)
              ·
                refine ⟨829727532117455567590901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 553151688078303711727267 829727532117455567590901)
                ·
                  refine ⟨77786956136011459461647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 829727532117455567590901 77786956136011459461647)
                  ·
                    rfl

theorem cell22_681703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 5].length) (baseStart_681703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_681703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_681703 prefixEnd_681703 := by exact prefixLift 681703
  have htrace : WordTrace (prefixWord ++ tailWord_681703) baseStart_681703 baseEnd_681703 := by
    simpa [prefixWord, tailWord_681703, baseEnd_681703] using wordTrace_append hprefix tailTrace_681703
  have hstable : (prefixWord ++ tailWord_681703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681703).length < 2 ^ (prefixWord ++ tailWord_681703).sum := by decide
  have hdescent : baseEnd_681703 < baseStart_681703 := by decide
  rcases family_descends (prefixWord ++ tailWord_681703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681716 : List Nat := [2, 6, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_681716 : Nat := 118140960795 + 681716 * 2 ^ 59
def prefixEnd_681716 : Nat := 4983230072969 + 3 ^ 40 * 681716 * 2
def baseEnd_681716 : Nat := 233365318573706677809901

theorem tailTrace_681716 : CollatzResearch.WordTrace tailWord_681716 prefixEnd_681716 233365318573706677809901 := by
  unfold tailWord_681716
  simp only [CollatzResearch.WordTrace]
  refine ⟨12432112599133417334308501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16576150132177889779078001 12432112599133417334308501)
  ·
    refine ⟨582755278084378937545711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12432112599133417334308501 582755278084378937545711)
    ·
      refine ⟨874132917126568406318567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 582755278084378937545711 874132917126568406318567)
      ·
        refine ⟨1311199375689852609477851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 874132917126568406318567 1311199375689852609477851)
        ·
          refine ⟨1966799063534778914216777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1311199375689852609477851 1966799063534778914216777)
          ·
            refine ⟨1475099297651084185662583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1966799063534778914216777 1475099297651084185662583)
            ·
              refine ⟨2212648946476626278493875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1475099297651084185662583 2212648946476626278493875)
              ·
                refine ⟨3318973419714939417740813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2212648946476626278493875 3318973419714939417740813)
                ·
                  refine ⟨1244615032393102281652805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3318973419714939417740813 1244615032393102281652805)
                  ·
                    refine ⟨233365318573706677809901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1244615032393102281652805 233365318573706677809901)
                    ·
                      rfl

theorem cell22_681716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_681716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_681716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_681716 prefixEnd_681716 := by exact prefixLift 681716
  have htrace : WordTrace (prefixWord ++ tailWord_681716) baseStart_681716 baseEnd_681716 := by
    simpa [prefixWord, tailWord_681716, baseEnd_681716] using wordTrace_append hprefix tailTrace_681716
  have hstable : (prefixWord ++ tailWord_681716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681716).length < 2 ^ (prefixWord ++ tailWord_681716).sum := by decide
  have hdescent : baseEnd_681716 < baseStart_681716 := by decide
  rcases family_descends (prefixWord ++ tailWord_681716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681741 : List Nat := [1, 7, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_681741 : Nat := 118140960795 + 681741 * 2 ^ 59
def prefixEnd_681741 : Nat := 4983230072969 + 3 ^ 40 * 681741 * 2
def baseEnd_681741 : Nat := 233373876584614945934825

theorem tailTrace_681741 : CollatzResearch.WordTrace tailWord_681741 prefixEnd_681741 233373876584614945934825 := by
  unfold tailWord_681741
  simp only [CollatzResearch.WordTrace]
  refine ⟨24865137023176263938277077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16576758015450842625518051 24865137023176263938277077)
  ·
    refine ⟨582776648980693686053369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 24865137023176263938277077 582776648980693686053369)
    ·
      refine ⟨437082486735520264540027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 582776648980693686053369 437082486735520264540027)
      ·
        refine ⟨655623730103280396810041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437082486735520264540027 655623730103280396810041)
        ·
          refine ⟨491717797577460297607531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 655623730103280396810041 491717797577460297607531)
          ·
            refine ⟨737576696366190446411297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491717797577460297607531 737576696366190446411297)
            ·
              refine ⟨553182522274642834808473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 737576696366190446411297 553182522274642834808473)
              ·
                refine ⟨414886891705982126106355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 553182522274642834808473 414886891705982126106355)
                ·
                  refine ⟨622330337558973189159533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 414886891705982126106355 622330337558973189159533)
                  ·
                    refine ⟨233373876584614945934825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 622330337558973189159533 233373876584614945934825)
                    ·
                      rfl

theorem cell22_681741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_681741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_681741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_681741 prefixEnd_681741 := by exact prefixLift 681741
  have htrace : WordTrace (prefixWord ++ tailWord_681741) baseStart_681741 baseEnd_681741 := by
    simpa [prefixWord, tailWord_681741, baseEnd_681741] using wordTrace_append hprefix tailTrace_681741
  have hstable : (prefixWord ++ tailWord_681741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681741).length < 2 ^ (prefixWord ++ tailWord_681741).sum := by decide
  have hdescent : baseEnd_681741 < baseStart_681741 := by decide
  rcases family_descends (prefixWord ++ tailWord_681741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681746 : List Nat := [3, 2, 4, 1, 1, 1, 1, 4, 2, 3]
def baseStart_681746 : Nat := 118140960795 + 681746 * 2 ^ 59
def prefixEnd_681746 : Nat := 4983230072969 + 3 ^ 40 * 681746 * 2
def baseEnd_681746 : Nat := 233375588186796599559809

theorem tailTrace_681746 : CollatzResearch.WordTrace tailWord_681746 prefixEnd_681746 233375588186796599559809 := by
  unfold tailWord_681746
  simp only [CollatzResearch.WordTrace]
  refine ⟨6216329847039537448052273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16576879592105433194806061 6216329847039537448052273)
  ·
    refine ⟨4662247385279653086039205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6216329847039537448052273 4662247385279653086039205)
    ·
      refine ⟨874171384739934953632351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4662247385279653086039205 874171384739934953632351)
      ·
        refine ⟨1311257077109902430448527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 874171384739934953632351 1311257077109902430448527)
        ·
          refine ⟨1966885615664853645672791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1311257077109902430448527 1966885615664853645672791)
          ·
            refine ⟨2950328423497280468509187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1966885615664853645672791 2950328423497280468509187)
            ·
              refine ⟨4425492635245920702763781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2950328423497280468509187 4425492635245920702763781)
              ·
                refine ⟨829779869108610131768209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4425492635245920702763781 829779869108610131768209)
                ·
                  refine ⟨622334901831457598826157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 829779869108610131768209 622334901831457598826157)
                  ·
                    refine ⟨233375588186796599559809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 622334901831457598826157 233375588186796599559809)
                    ·
                      rfl

theorem cell22_681746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_681746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_681746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_681746 prefixEnd_681746 := by exact prefixLift 681746
  have htrace : WordTrace (prefixWord ++ tailWord_681746) baseStart_681746 baseEnd_681746 := by
    simpa [prefixWord, tailWord_681746, baseEnd_681746] using wordTrace_append hprefix tailTrace_681746
  have hstable : (prefixWord ++ tailWord_681746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681746).length < 2 ^ (prefixWord ++ tailWord_681746).sum := by decide
  have hdescent : baseEnd_681746 < baseStart_681746 := by decide
  rcases family_descends (prefixWord ++ tailWord_681746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681832 : List Nat := [2, 1, 4, 2, 1, 1, 1, 4, 6]
def baseStart_681832 : Nat := 118140960795 + 681832 * 2 ^ 59
def prefixEnd_681832 : Nat := 4983230072969 + 3 ^ 40 * 681832 * 2
def baseEnd_681832 : Nat := 77801675914773680636515

theorem tailTrace_681832 : CollatzResearch.WordTrace tailWord_681832 prefixEnd_681832 77801675914773680636515 := by
  unfold tailWord_681832
  simp only [CollatzResearch.WordTrace]
  refine ⟨12434228032923293239919875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16578970710564390986559833 12434228032923293239919875)
  ·
    refine ⟨18651342049384939859879813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12434228032923293239919875 18651342049384939859879813)
    ·
      refine ⟨3497126634259676223727465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18651342049384939859879813 3497126634259676223727465)
      ·
        refine ⟨2622844975694757167795599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3497126634259676223727465 2622844975694757167795599)
        ·
          refine ⟨3934267463542135751693399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2622844975694757167795599 3934267463542135751693399)
          ·
            refine ⟨5901401195313203627540099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3934267463542135751693399 5901401195313203627540099)
            ·
              refine ⟨8852101792969805441310149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5901401195313203627540099 8852101792969805441310149)
              ·
                refine ⟨1659769086181838520245653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8852101792969805441310149 1659769086181838520245653)
                ·
                  refine ⟨77801675914773680636515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1659769086181838520245653 77801675914773680636515)
                  ·
                    rfl

theorem cell22_681832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 6].length) (baseStart_681832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_681832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_681832 prefixEnd_681832 := by exact prefixLift 681832
  have htrace : WordTrace (prefixWord ++ tailWord_681832) baseStart_681832 baseEnd_681832 := by
    simpa [prefixWord, tailWord_681832, baseEnd_681832] using wordTrace_append hprefix tailTrace_681832
  have hstable : (prefixWord ++ tailWord_681832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681832).length < 2 ^ (prefixWord ++ tailWord_681832).sum := by decide
  have hdescent : baseEnd_681832 < baseStart_681832 := by decide
  rcases family_descends (prefixWord ++ tailWord_681832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681866 : List Nat := [3, 1, 2, 4, 2, 2, 1, 1, 6]
def baseStart_681866 : Nat := 118140960795 + 681866 * 2 ^ 59
def prefixEnd_681866 : Nat := 4983230072969 + 3 ^ 40 * 681866 * 2
def baseEnd_681866 : Nat := 77805555546385428853147

theorem tailTrace_681866 : CollatzResearch.WordTrace tailWord_681866 prefixEnd_681866 77805555546385428853147 := by
  unfold tailWord_681866
  simp only [CollatzResearch.WordTrace]
  refine ⟨6217424036930852571644363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16579797431815606857718301 6217424036930852571644363)
  ·
    refine ⟨9326136055396278857466545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6217424036930852571644363 9326136055396278857466545)
    ·
      refine ⟨6994602041547209143099909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9326136055396278857466545 6994602041547209143099909)
      ·
        refine ⟨1311487882790101714331233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6994602041547209143099909 1311487882790101714331233)
        ·
          refine ⟨983615912092576285748425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1311487882790101714331233 983615912092576285748425)
          ·
            refine ⟨737711934069432214311319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 983615912092576285748425 737711934069432214311319)
            ·
              refine ⟨1106567901104148321466979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 737711934069432214311319 1106567901104148321466979)
              ·
                refine ⟨1659851851656222482200469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1106567901104148321466979 1659851851656222482200469)
                ·
                  refine ⟨77805555546385428853147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1659851851656222482200469 77805555546385428853147)
                  ·
                    rfl

theorem cell22_681866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 6].length) (baseStart_681866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_681866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_681866 prefixEnd_681866 := by exact prefixLift 681866
  have htrace : WordTrace (prefixWord ++ tailWord_681866) baseStart_681866 baseEnd_681866 := by
    simpa [prefixWord, tailWord_681866, baseEnd_681866] using wordTrace_append hprefix tailTrace_681866
  have hstable : (prefixWord ++ tailWord_681866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681866).length < 2 ^ (prefixWord ++ tailWord_681866).sum := by decide
  have hdescent : baseEnd_681866 < baseStart_681866 := by decide
  rcases family_descends (prefixWord ++ tailWord_681866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681877 : List Nat := [1, 3, 2, 1, 1, 3, 4, 7]
def baseStart_681877 : Nat := 118140960795 + 681877 * 2 ^ 59
def prefixEnd_681877 : Nat := 4983230072969 + 3 ^ 40 * 681877 * 2
def baseEnd_681877 : Nat := 25935603573772880503823

theorem tailTrace_681877 : CollatzResearch.WordTrace tailWord_681877 prefixEnd_681877 25935603573772880503823 := by
  unfold tailWord_681877
  simp only [CollatzResearch.WordTrace]
  refine ⟨24870097350683559165227885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16580064900455706110151923 24870097350683559165227885)
  ·
    refine ⟨9326286506506334686960457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24870097350683559165227885 9326286506506334686960457)
    ·
      refine ⟨6994714879879751015220343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9326286506506334686960457 6994714879879751015220343)
      ·
        refine ⟨10492072319819626522830515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6994714879879751015220343 10492072319819626522830515)
        ·
          refine ⟨15738108479729439784245773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10492072319819626522830515 15738108479729439784245773)
          ·
            refine ⟨5901790679898539919092165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15738108479729439784245773 5901790679898539919092165)
            ·
              refine ⟨1106585752480976234829781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5901790679898539919092165 1106585752480976234829781)
              ·
                refine ⟨25935603573772880503823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1106585752480976234829781 25935603573772880503823)
                ·
                  rfl

theorem cell22_681877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 7].length) (baseStart_681877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_681877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_681877 prefixEnd_681877 := by exact prefixLift 681877
  have htrace : WordTrace (prefixWord ++ tailWord_681877) baseStart_681877 baseEnd_681877 := by
    simpa [prefixWord, tailWord_681877, baseEnd_681877] using wordTrace_append hprefix tailTrace_681877
  have hstable : (prefixWord ++ tailWord_681877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681877).length < 2 ^ (prefixWord ++ tailWord_681877).sum := by decide
  have hdescent : baseEnd_681877 < baseStart_681877 := by decide
  rcases family_descends (prefixWord ++ tailWord_681877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681881 : List Nat := [1, 2, 1, 2, 1, 3, 6, 1, 2, 3]
def baseStart_681881 : Nat := 118140960795 + 681881 * 2 ^ 59
def prefixEnd_681881 : Nat := 4983230072969 + 3 ^ 40 * 681881 * 2
def baseEnd_681881 : Nat := 233421801445701247434395

theorem tailTrace_681881 : CollatzResearch.WordTrace tailWord_681881 prefixEnd_681881 233421801445701247434395 := by
  unfold tailWord_681881
  simp only [CollatzResearch.WordTrace]
  refine ⟨24870243242669067848373497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16580162161779378565582331 24870243242669067848373497)
  ·
    refine ⟨18652682432001800886280123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24870243242669067848373497 18652682432001800886280123)
    ·
      refine ⟨27979023648002701329420185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18652682432001800886280123 27979023648002701329420185)
      ·
        refine ⟨20984267736002025997065139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27979023648002701329420185 20984267736002025997065139)
        ·
          refine ⟨31476401604003038995597709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20984267736002025997065139 31476401604003038995597709)
          ·
            refine ⟨11803650601501139623349141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31476401604003038995597709 11803650601501139623349141)
            ·
              refine ⟨553296121945365919844491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11803650601501139623349141 553296121945365919844491)
              ·
                refine ⟨829944182918048879766737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 553296121945365919844491 829944182918048879766737)
                ·
                  refine ⟨622458137188536659825053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 829944182918048879766737 622458137188536659825053)
                  ·
                    refine ⟨233421801445701247434395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 622458137188536659825053 233421801445701247434395)
                    ·
                      rfl

theorem cell22_681881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 2, 3].length) (baseStart_681881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_681881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_681881 prefixEnd_681881 := by exact prefixLift 681881
  have htrace : WordTrace (prefixWord ++ tailWord_681881) baseStart_681881 baseEnd_681881 := by
    simpa [prefixWord, tailWord_681881, baseEnd_681881] using wordTrace_append hprefix tailTrace_681881
  have hstable : (prefixWord ++ tailWord_681881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681881).length < 2 ^ (prefixWord ++ tailWord_681881).sum := by decide
  have hdescent : baseEnd_681881 < baseStart_681881 := by decide
  rcases family_descends (prefixWord ++ tailWord_681881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681902 : List Nat := [4, 1, 5, 1, 1, 1, 3, 1, 1, 4]
def baseStart_681902 : Nat := 118140960795 + 681902 * 2 ^ 59
def prefixEnd_681902 : Nat := 4983230072969 + 3 ^ 40 * 681902 * 2
def baseEnd_681902 : Nat := 233428990174864192659331

theorem tailTrace_681902 : CollatzResearch.WordTrace tailWord_681902 prefixEnd_681902 233428990174864192659331 := by
  unfold tailWord_681902
  simp only [CollatzResearch.WordTrace]
  refine ⟨3108876146949123554360995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16580672783728658956591973 3108876146949123554360995)
  ·
    refine ⟨4663314220423685331541493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3108876146949123554360995 4663314220423685331541493)
    ·
      refine ⟨437185708164720499832015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4663314220423685331541493 437185708164720499832015)
      ·
        refine ⟨655778562247080749748023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437185708164720499832015 655778562247080749748023)
        ·
          refine ⟨983667843370621124622035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 655778562247080749748023 983667843370621124622035)
          ·
            refine ⟨1475501765055931686933053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 983667843370621124622035 1475501765055931686933053)
            ·
              refine ⟨553313161895974382599895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1475501765055931686933053 553313161895974382599895)
              ·
                refine ⟨829969742843961573899843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 553313161895974382599895 829969742843961573899843)
                ·
                  refine ⟨1244954614265942360849765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 829969742843961573899843 1244954614265942360849765)
                  ·
                    refine ⟨233428990174864192659331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1244954614265942360849765 233428990174864192659331)
                    ·
                      rfl

theorem cell22_681902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_681902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_681902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_681902 prefixEnd_681902 := by exact prefixLift 681902
  have htrace : WordTrace (prefixWord ++ tailWord_681902) baseStart_681902 baseEnd_681902 := by
    simpa [prefixWord, tailWord_681902, baseEnd_681902] using wordTrace_append hprefix tailTrace_681902
  have hstable : (prefixWord ++ tailWord_681902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681902).length < 2 ^ (prefixWord ++ tailWord_681902).sum := by decide
  have hdescent : baseEnd_681902 < baseStart_681902 := by decide
  rcases family_descends (prefixWord ++ tailWord_681902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681967 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 8]
def baseStart_681967 : Nat := 118140960795 + 681967 * 2 ^ 59
def prefixEnd_681967 : Nat := 4983230072969 + 3 ^ 40 * 681967 * 2
def baseEnd_681967 : Nat := 77817080334408563261377

theorem tailTrace_681967 : CollatzResearch.WordTrace tailWord_681967 prefixEnd_681967 77817080334408563261377 := by
  unfold tailWord_681967
  simp only [CollatzResearch.WordTrace]
  refine ⟨24873379920357504536004155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16582253280238336357336103 24873379920357504536004155)
  ·
    refine ⟨37310069880536256804006233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24873379920357504536004155 37310069880536256804006233)
    ·
      refine ⟨27982552410402192603004675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37310069880536256804006233 27982552410402192603004675)
      ·
        refine ⟨41973828615603288904507013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27982552410402192603004675 41973828615603288904507013)
        ·
          refine ⟨7870092865425616669595065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41973828615603288904507013 7870092865425616669595065)
          ·
            refine ⟨5902569649069212502196299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7870092865425616669595065 5902569649069212502196299)
            ·
              refine ⟨8853854473603818753294449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5902569649069212502196299 8853854473603818753294449)
              ·
                refine ⟨6640390855202864064970837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8853854473603818753294449 6640390855202864064970837)
                ·
                  refine ⟨77817080334408563261377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6640390855202864064970837 77817080334408563261377)
                  ·
                    rfl

theorem cell22_681967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 8].length) (baseStart_681967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_681967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_681967 prefixEnd_681967 := by exact prefixLift 681967
  have htrace : WordTrace (prefixWord ++ tailWord_681967) baseStart_681967 baseEnd_681967 := by
    simpa [prefixWord, tailWord_681967, baseEnd_681967] using wordTrace_append hprefix tailTrace_681967
  have hstable : (prefixWord ++ tailWord_681967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681967).length < 2 ^ (prefixWord ++ tailWord_681967).sum := by decide
  have hdescent : baseEnd_681967 < baseStart_681967 := by decide
  rcases family_descends (prefixWord ++ tailWord_681967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682089 : List Nat := [1, 2, 1, 1, 1, 5, 2, 2, 2, 5]
def baseStart_682089 : Nat := 118140960795 + 682089 * 2 ^ 59
def prefixEnd_682089 : Nat := 4983230072969 + 3 ^ 40 * 682089 * 2
def baseEnd_682089 : Nat := 233493004096458038233757

theorem tailTrace_682089 : CollatzResearch.WordTrace tailWord_682089 prefixEnd_682089 233493004096458038233757 := by
  unfold tailWord_682089
  simp only [CollatzResearch.WordTrace]
  refine ⟨24877829625915519371945321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16585219750610346247963547 24877829625915519371945321)
  ·
    refine ⟨18658372219436639528958991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24877829625915519371945321 18658372219436639528958991)
    ·
      refine ⟨27987558329154959293438487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18658372219436639528958991 27987558329154959293438487)
      ·
        refine ⟨41981337493732438940157731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27987558329154959293438487 41981337493732438940157731)
        ·
          refine ⟨62972006240598658410236597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41981337493732438940157731 62972006240598658410236597)
          ·
            refine ⟨5903625585056124225959681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62972006240598658410236597 5903625585056124225959681)
            ·
              refine ⟨4427719188792093169469761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5903625585056124225959681 4427719188792093169469761)
              ·
                refine ⟨3320789391594069877102321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4427719188792093169469761 3320789391594069877102321)
                ·
                  refine ⟨2490592043695552407826741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3320789391594069877102321 2490592043695552407826741)
                  ·
                    refine ⟨233493004096458038233757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2490592043695552407826741 233493004096458038233757)
                    ·
                      rfl

theorem cell22_682089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 5].length) (baseStart_682089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_682089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_682089 prefixEnd_682089 := by exact prefixLift 682089
  have htrace : WordTrace (prefixWord ++ tailWord_682089) baseStart_682089 baseEnd_682089 := by
    simpa [prefixWord, tailWord_682089, baseEnd_682089] using wordTrace_append hprefix tailTrace_682089
  have hstable : (prefixWord ++ tailWord_682089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682089).length < 2 ^ (prefixWord ++ tailWord_682089).sum := by decide
  have hdescent : baseEnd_682089 < baseStart_682089 := by decide
  rcases family_descends (prefixWord ++ tailWord_682089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682095 : List Nat := [1, 1, 2, 1, 3, 4, 4, 2, 1, 3]
def baseStart_682095 : Nat := 118140960795 + 682095 * 2 ^ 59
def prefixEnd_682095 : Nat := 4983230072969 + 3 ^ 40 * 682095 * 2
def baseEnd_682095 : Nat := 233495058019076022583739

theorem tailTrace_682095 : CollatzResearch.WordTrace tailWord_682095 prefixEnd_682095 233495058019076022583739 := by
  unfold tailWord_682095
  simp only [CollatzResearch.WordTrace]
  refine ⟨24878048463893782396663739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16585365642595854931109159 24878048463893782396663739)
  ·
    refine ⟨37317072695840673594995609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24878048463893782396663739 37317072695840673594995609)
    ·
      refine ⟨27987804521880505196246707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37317072695840673594995609 27987804521880505196246707)
      ·
        refine ⟨41981706782820757794370061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27987804521880505196246707 41981706782820757794370061)
        ·
          refine ⟨15743140043557784172888773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41981706782820757794370061 15743140043557784172888773)
          ·
            refine ⟨2951838758167084532416645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15743140043557784172888773 2951838758167084532416645)
            ·
              refine ⟨553469767156328349828121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2951838758167084532416645 553469767156328349828121)
              ·
                refine ⟨415102325367246262371091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 553469767156328349828121 415102325367246262371091)
                ·
                  refine ⟨622653488050869393556637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 415102325367246262371091 622653488050869393556637)
                  ·
                    refine ⟨233495058019076022583739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 622653488050869393556637 233495058019076022583739)
                    ·
                      rfl

theorem cell22_682095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 2, 1, 3].length) (baseStart_682095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_682095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_682095 prefixEnd_682095 := by exact prefixLift 682095
  have htrace : WordTrace (prefixWord ++ tailWord_682095) baseStart_682095 baseEnd_682095 := by
    simpa [prefixWord, tailWord_682095, baseEnd_682095] using wordTrace_append hprefix tailTrace_682095
  have hstable : (prefixWord ++ tailWord_682095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682095).length < 2 ^ (prefixWord ++ tailWord_682095).sum := by decide
  have hdescent : baseEnd_682095 < baseStart_682095 := by decide
  rcases family_descends (prefixWord ++ tailWord_682095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682119 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 8]
def baseStart_682119 : Nat := 118140960795 + 682119 * 2 ^ 59
def prefixEnd_682119 : Nat := 4983230072969 + 3 ^ 40 * 682119 * 2
def baseEnd_682119 : Nat := 77834424569849319994555

theorem tailTrace_682119 : CollatzResearch.WordTrace tailWord_682119 prefixEnd_682119 77834424569849319994555 := by
  unfold tailWord_682119
  simp only [CollatzResearch.WordTrace]
  refine ⟨24878923815806834495537411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16585949210537889663691607 24878923815806834495537411)
  ·
    refine ⟨37318385723710251743306117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24878923815806834495537411 37318385723710251743306117)
    ·
      refine ⟨6997197323195672201869897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37318385723710251743306117 6997197323195672201869897)
      ·
        refine ⟨5247897992396754151402423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6997197323195672201869897 5247897992396754151402423)
        ·
          refine ⟨7871846988595131227103635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5247897992396754151402423 7871846988595131227103635)
          ·
            refine ⟨11807770482892696840655453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7871846988595131227103635 11807770482892696840655453)
            ·
              refine ⟨4427913931084761315245795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11807770482892696840655453 4427913931084761315245795)
              ·
                refine ⟨6641870896627141972868693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4427913931084761315245795 6641870896627141972868693)
                ·
                  refine ⟨77834424569849319994555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6641870896627141972868693 77834424569849319994555)
                  ·
                    rfl

theorem cell22_682119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 8].length) (baseStart_682119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_682119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_682119 prefixEnd_682119 := by exact prefixLift 682119
  have htrace : WordTrace (prefixWord ++ tailWord_682119) baseStart_682119 baseEnd_682119 := by
    simpa [prefixWord, tailWord_682119, baseEnd_682119] using wordTrace_append hprefix tailTrace_682119
  have hstable : (prefixWord ++ tailWord_682119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682119).length < 2 ^ (prefixWord ++ tailWord_682119).sum := by decide
  have hdescent : baseEnd_682119 < baseStart_682119 := by decide
  rcases family_descends (prefixWord ++ tailWord_682119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682121 : List Nat := [1, 2, 1, 1, 4, 2, 2, 4, 1, 4]
def baseStart_682121 : Nat := 118140960795 + 682121 * 2 ^ 59
def prefixEnd_682121 : Nat := 4983230072969 + 3 ^ 40 * 682121 * 2
def baseEnd_682121 : Nat := 233503958350420621433659

theorem tailTrace_682121 : CollatzResearch.WordTrace tailWord_682121 prefixEnd_682121 233503958350420621433659 := by
  unfold tailWord_682121
  simp only [CollatzResearch.WordTrace]
  refine ⟨24878996761799588837110217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16585997841199725891406811 24878996761799588837110217)
  ·
    refine ⟨18659247571349691627832663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24878996761799588837110217 18659247571349691627832663)
    ·
      refine ⟨27988871357024537441748995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18659247571349691627832663 27988871357024537441748995)
      ·
        refine ⟨41983307035536806162623493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27988871357024537441748995 41983307035536806162623493)
        ·
          refine ⟨7871870069163151155491905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41983307035536806162623493 7871870069163151155491905)
          ·
            refine ⟨5903902551872363366618929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7871870069163151155491905 5903902551872363366618929)
            ·
              refine ⟨4427926913904272524964197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5903902551872363366618929 4427926913904272524964197)
              ·
                refine ⟨830236296357051098430787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4427926913904272524964197 830236296357051098430787)
                ·
                  refine ⟨1245354444535576647646181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 830236296357051098430787 1245354444535576647646181)
                  ·
                    refine ⟨233503958350420621433659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1245354444535576647646181 233503958350420621433659)
                    ·
                      rfl

theorem cell22_682121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 4].length) (baseStart_682121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_682121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_682121 prefixEnd_682121 := by exact prefixLift 682121
  have htrace : WordTrace (prefixWord ++ tailWord_682121) baseStart_682121 baseEnd_682121 := by
    simpa [prefixWord, tailWord_682121, baseEnd_682121] using wordTrace_append hprefix tailTrace_682121
  have hstable : (prefixWord ++ tailWord_682121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682121).length < 2 ^ (prefixWord ++ tailWord_682121).sum := by decide
  have hdescent : baseEnd_682121 < baseStart_682121 := by decide
  rcases family_descends (prefixWord ++ tailWord_682121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682142 : List Nat := [4, 3, 1, 1, 4, 1, 1, 2, 5]
def baseStart_682142 : Nat := 118140960795 + 682142 * 2 ^ 59
def prefixEnd_682142 : Nat := 4983230072969 + 3 ^ 40 * 682142 * 2
def baseEnd_682142 : Nat := 77837049026527855552865

theorem tailTrace_682142 : CollatzResearch.WordTrace tailWord_682142 prefixEnd_682142 77837049026527855552865 := by
  unfold tailWord_682142
  simp only [CollatzResearch.WordTrace]
  refine ⟨3109970336840438677953085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16586508463149006282416453 3109970336840438677953085)
  ·
    refine ⟨1166238876315164504232407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3109970336840438677953085 1166238876315164504232407)
    ·
      refine ⟨1749358314472746756348611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1166238876315164504232407 1749358314472746756348611)
      ·
        refine ⟨2624037471709120134522917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1749358314472746756348611 2624037471709120134522917)
        ·
          refine ⟨492007025945460025223047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2624037471709120134522917 492007025945460025223047)
          ·
            refine ⟨738010538918190037834571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492007025945460025223047 738010538918190037834571)
            ·
              refine ⟨1107015808377285056751857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 738010538918190037834571 1107015808377285056751857)
              ·
                refine ⟨830261856282963792563893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1107015808377285056751857 830261856282963792563893)
                ·
                  refine ⟨77837049026527855552865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 830261856282963792563893 77837049026527855552865)
                  ·
                    rfl

theorem cell22_682142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_682142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_682142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_682142 prefixEnd_682142 := by exact prefixLift 682142
  have htrace : WordTrace (prefixWord ++ tailWord_682142) baseStart_682142 baseEnd_682142 := by
    simpa [prefixWord, tailWord_682142, baseEnd_682142] using wordTrace_append hprefix tailTrace_682142
  have hstable : (prefixWord ++ tailWord_682142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682142).length < 2 ^ (prefixWord ++ tailWord_682142).sum := by decide
  have hdescent : baseEnd_682142 < baseStart_682142 := by decide
  rcases family_descends (prefixWord ++ tailWord_682142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682181 : List Nat := [1, 3, 1, 1, 1, 1, 8, 6]
def baseStart_682181 : Nat := 118140960795 + 682181 * 2 ^ 59
def prefixEnd_682181 : Nat := 4983230072969 + 3 ^ 40 * 682181 * 2
def baseEnd_682181 : Nat := 25947166397400051659275

theorem tailTrace_682181 : CollatzResearch.WordTrace tailWord_682181 prefixEnd_682181 25947166397400051659275 := by
  unfold tailWord_682181
  simp only [CollatzResearch.WordTrace]
  refine ⟨24881185141582219084294397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16587456761054812722862931 24881185141582219084294397)
  ·
    refine ⟨9330444428093332156610399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24881185141582219084294397 9330444428093332156610399)
    ·
      refine ⟨13995666642139998234915599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9330444428093332156610399 13995666642139998234915599)
      ·
        refine ⟨20993499963209997352373399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13995666642139998234915599 20993499963209997352373399)
        ·
          refine ⟨31490249944814996028560099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20993499963209997352373399 31490249944814996028560099)
          ·
            refine ⟨47235374917222494042840149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31490249944814996028560099 47235374917222494042840149)
            ·
              refine ⟨553539549811201102064533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 47235374917222494042840149 553539549811201102064533)
              ·
                refine ⟨25947166397400051659275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 553539549811201102064533 25947166397400051659275)
                ·
                  rfl

theorem cell22_682181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 6].length) (baseStart_682181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_682181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_682181 prefixEnd_682181 := by exact prefixLift 682181
  have htrace : WordTrace (prefixWord ++ tailWord_682181) baseStart_682181 baseEnd_682181 := by
    simpa [prefixWord, tailWord_682181, baseEnd_682181] using wordTrace_append hprefix tailTrace_682181
  have hstable : (prefixWord ++ tailWord_682181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682181).length < 2 ^ (prefixWord ++ tailWord_682181).sum := by decide
  have hdescent : baseEnd_682181 < baseStart_682181 := by decide
  rcases family_descends (prefixWord ++ tailWord_682181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682198 : List Nat := [5, 2, 1, 2, 1, 1, 10]
def baseStart_682198 : Nat := 118140960795 + 682198 * 2 ^ 59
def prefixEnd_682198 : Nat := 4983230072969 + 3 ^ 40 * 682198 * 2
def baseEnd_682198 : Nat := 8649271000889558787349

theorem tailTrace_682198 : CollatzResearch.WordTrace tailWord_682198 prefixEnd_682198 8649271000889558787349 := by
  unfold tailWord_682198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1555112823907539436728953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16587870121680420658442165 1555112823907539436728953)
  ·
    refine ⟨1166334617930654577546715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1555112823907539436728953 1166334617930654577546715)
    ·
      refine ⟨1749501926895981866320073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1166334617930654577546715 1749501926895981866320073)
      ·
        refine ⟨1312126445171986399740055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1749501926895981866320073 1312126445171986399740055)
        ·
          refine ⟨1968189667757979599610083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1312126445171986399740055 1968189667757979599610083)
          ·
            refine ⟨2952284501636969399415125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1968189667757979599610083 2952284501636969399415125)
            ·
              refine ⟨8649271000889558787349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2952284501636969399415125 8649271000889558787349)
              ·
                rfl

theorem cell22_682198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 10].length) (baseStart_682198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_682198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_682198 prefixEnd_682198 := by exact prefixLift 682198
  have htrace : WordTrace (prefixWord ++ tailWord_682198) baseStart_682198 baseEnd_682198 := by
    simpa [prefixWord, tailWord_682198, baseEnd_682198] using wordTrace_append hprefix tailTrace_682198
  have hstable : (prefixWord ++ tailWord_682198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682198).length < 2 ^ (prefixWord ++ tailWord_682198).sum := by decide
  have hdescent : baseEnd_682198 < baseStart_682198 := by decide
  rcases family_descends (prefixWord ++ tailWord_682198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682204 : List Nat := [2, 2, 5, 2, 1, 1, 3, 2, 4]
def baseStart_682204 : Nat := 118140960795 + 682204 * 2 ^ 59
def prefixEnd_682204 : Nat := 4983230072969 + 3 ^ 40 * 682204 * 2
def baseEnd_682204 : Nat := 77844123648878690536135

theorem tailTrace_682204 : CollatzResearch.WordTrace tailWord_682204 prefixEnd_682204 77844123648878690536135 := by
  unfold tailWord_682204
  simp only [CollatzResearch.WordTrace]
  refine ⟨12441012010249447006190833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16588016013665929341587777 12441012010249447006190833)
  ·
    refine ⟨9330759007687085254643125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12441012010249447006190833 9330759007687085254643125)
    ·
      refine ⟨874758656970664242622793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9330759007687085254643125 874758656970664242622793)
      ·
        refine ⟨656068992727998181967095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 874758656970664242622793 656068992727998181967095)
        ·
          refine ⟨984103489091997272950643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 656068992727998181967095 984103489091997272950643)
          ·
            refine ⟨1476155233637995909425965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 984103489091997272950643 1476155233637995909425965)
            ·
              refine ⟨553558212614248466034737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1476155233637995909425965 553558212614248466034737)
              ·
                refine ⟨415168659460686349526053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 553558212614248466034737 415168659460686349526053)
                ·
                  refine ⟨77844123648878690536135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 415168659460686349526053 77844123648878690536135)
                  ·
                    rfl

theorem cell22_682204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 2, 4].length) (baseStart_682204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_682204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_682204 prefixEnd_682204 := by exact prefixLift 682204
  have htrace : WordTrace (prefixWord ++ tailWord_682204) baseStart_682204 baseEnd_682204 := by
    simpa [prefixWord, tailWord_682204, baseEnd_682204] using wordTrace_append hprefix tailTrace_682204
  have hstable : (prefixWord ++ tailWord_682204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682204).length < 2 ^ (prefixWord ++ tailWord_682204).sum := by decide
  have hdescent : baseEnd_682204 < baseStart_682204 := by decide
  rcases family_descends (prefixWord ++ tailWord_682204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682303 : List Nat := [1, 1, 2, 2, 4, 1, 2, 2, 4, 3]
def baseStart_682303 : Nat := 118140960795 + 682303 * 2 ^ 59
def prefixEnd_682303 : Nat := 4983230072969 + 3 ^ 40 * 682303 * 2
def baseEnd_682303 : Nat := 233566260669832813383101

theorem tailTrace_682303 : CollatzResearch.WordTrace tailWord_682303 prefixEnd_682303 233566260669832813383101 := by
  unfold tailWord_682303
  simp only [CollatzResearch.WordTrace]
  refine ⟨24885634847140233920235563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16590423231426822613490375 24885634847140233920235563)
  ·
    refine ⟨37328452270710350880353345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24885634847140233920235563 37328452270710350880353345)
    ·
      refine ⟨27996339203032763160265009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37328452270710350880353345 27996339203032763160265009)
      ·
        refine ⟨20997254402274572370198757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27996339203032763160265009 20997254402274572370198757)
        ·
          refine ⟨3936985200426482319412267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20997254402274572370198757 3936985200426482319412267)
          ·
            refine ⟨5905477800639723479118401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3936985200426482319412267 5905477800639723479118401)
            ·
              refine ⟨4429108350479792609338801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5905477800639723479118401 4429108350479792609338801)
              ·
                refine ⟨3321831262859844457004101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4429108350479792609338801 3321831262859844457004101)
                ·
                  refine ⟨622843361786220835688269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3321831262859844457004101 622843361786220835688269)
                  ·
                    refine ⟨233566260669832813383101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 622843361786220835688269 233566260669832813383101)
                    ·
                      rfl

theorem cell22_682303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 4, 3].length) (baseStart_682303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_682303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_682303 prefixEnd_682303 := by exact prefixLift 682303
  have htrace : WordTrace (prefixWord ++ tailWord_682303) baseStart_682303 baseEnd_682303 := by
    simpa [prefixWord, tailWord_682303, baseEnd_682303] using wordTrace_append hprefix tailTrace_682303
  have hstable : (prefixWord ++ tailWord_682303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682303).length < 2 ^ (prefixWord ++ tailWord_682303).sum := by decide
  have hdescent : baseEnd_682303 < baseStart_682303 := by decide
  rcases family_descends (prefixWord ++ tailWord_682303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682316 : List Nat := [2, 2, 1, 3, 2, 1, 11]
def baseStart_682316 : Nat := 118140960795 + 682316 * 2 ^ 59
def prefixEnd_682316 : Nat := 4983230072969 + 3 ^ 40 * 682316 * 2
def baseEnd_682316 : Nat := 8650767067981670844743

theorem tailTrace_682316 : CollatzResearch.WordTrace tailWord_682316 prefixEnd_682316 8650767067981670844743 := by
  unfold tailWord_682316
  simp only [CollatzResearch.WordTrace]
  refine ⟨12443054498046568570229401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16590739330728758093639201 12443054498046568570229401)
  ·
    refine ⟨9332290873534926427672051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12443054498046568570229401 9332290873534926427672051)
    ·
      refine ⟨13998436310302389641508077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9332290873534926427672051 13998436310302389641508077)
      ·
        refine ⟨5249413616363396115565529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13998436310302389641508077 5249413616363396115565529)
        ·
          refine ⟨3937060212272547086674147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5249413616363396115565529 3937060212272547086674147)
          ·
            refine ⟨5905590318408820630011221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3937060212272547086674147 5905590318408820630011221)
            ·
              refine ⟨8650767067981670844743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5905590318408820630011221 8650767067981670844743)
              ·
                rfl

theorem cell22_682316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 11].length) (baseStart_682316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_682316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_682316 prefixEnd_682316 := by exact prefixLift 682316
  have htrace : WordTrace (prefixWord ++ tailWord_682316) baseStart_682316 baseEnd_682316 := by
    simpa [prefixWord, tailWord_682316, baseEnd_682316] using wordTrace_append hprefix tailTrace_682316
  have hstable : (prefixWord ++ tailWord_682316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682316).length < 2 ^ (prefixWord ++ tailWord_682316).sum := by decide
  have hdescent : baseEnd_682316 < baseStart_682316 := by decide
  rcases family_descends (prefixWord ++ tailWord_682316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682320 : List Nat := [2, 1, 1, 1, 1, 6, 3, 2, 2, 3]
def baseStart_682320 : Nat := 118140960795 + 682320 * 2 ^ 59
def prefixEnd_682320 : Nat := 4983230072969 + 3 ^ 40 * 682320 * 2
def baseEnd_682320 : Nat := 233572080117250435708049

theorem tailTrace_682320 : CollatzResearch.WordTrace tailWord_682320 prefixEnd_682320 233572080117250435708049 := by
  unfold tailWord_682320
  simp only [CollatzResearch.WordTrace]
  refine ⟨12443127444039322911802207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16590836592052430549069609 12443127444039322911802207)
  ·
    refine ⟨18664691166058984367703311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12443127444039322911802207 18664691166058984367703311)
    ·
      refine ⟨27997036749088476551554967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18664691166058984367703311 27997036749088476551554967)
      ·
        refine ⟨41995555123632714827332451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27997036749088476551554967 41995555123632714827332451)
        ·
          refine ⟨62993332685449072240998677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41995555123632714827332451 62993332685449072240998677)
          ·
            refine ⟨2952812469630425261296813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62993332685449072240998677 2952812469630425261296813)
            ·
              refine ⟨1107304676111409472986305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2952812469630425261296813 1107304676111409472986305)
              ·
                refine ⟨830478507083557104739729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1107304676111409472986305 830478507083557104739729)
                ·
                  refine ⟨622858880312667828554797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 830478507083557104739729 622858880312667828554797)
                  ·
                    refine ⟨233572080117250435708049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 622858880312667828554797 233572080117250435708049)
                    ·
                      rfl

theorem cell22_682320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 2, 3].length) (baseStart_682320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_682320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_682320 prefixEnd_682320 := by exact prefixLift 682320
  have htrace : WordTrace (prefixWord ++ tailWord_682320) baseStart_682320 baseEnd_682320 := by
    simpa [prefixWord, tailWord_682320, baseEnd_682320] using wordTrace_append hprefix tailTrace_682320
  have hstable : (prefixWord ++ tailWord_682320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682320).length < 2 ^ (prefixWord ++ tailWord_682320).sum := by decide
  have hdescent : baseEnd_682320 < baseStart_682320 := by decide
  rcases family_descends (prefixWord ++ tailWord_682320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682382 : List Nat := [4, 1, 1, 4, 1, 1, 3, 1, 3, 3]
def baseStart_682382 : Nat := 118140960795 + 682382 * 2 ^ 59
def prefixEnd_682382 : Nat := 4983230072969 + 3 ^ 40 * 682382 * 2
def baseEnd_682382 : Nat := 233593303984302940657859

theorem tailTrace_682382 : CollatzResearch.WordTrace tailWord_682382 prefixEnd_682382 233593303984302940657859 := by
  unfold tailWord_682382
  simp only [CollatzResearch.WordTrace]
  refine ⟨3111064526731753801545175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16592344142569353608240933 3111064526731753801545175)
  ·
    refine ⟨4666596790097630702317763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3111064526731753801545175 4666596790097630702317763)
    ·
      refine ⟨6999895185146446053476645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4666596790097630702317763 6999895185146446053476645)
      ·
        refine ⟨1312480347214958635026871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6999895185146446053476645 1312480347214958635026871)
        ·
          refine ⟨1968720520822437952540307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1312480347214958635026871 1968720520822437952540307)
          ·
            refine ⟨2953080781233656928810461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1968720520822437952540307 2953080781233656928810461)
            ·
              refine ⟨1107405292962621348303923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2953080781233656928810461 1107405292962621348303923)
              ·
                refine ⟨1661107939443932022455885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1107405292962621348303923 1661107939443932022455885)
                ·
                  refine ⟨622915477291474508420957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1661107939443932022455885 622915477291474508420957)
                  ·
                    refine ⟨233593303984302940657859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 622915477291474508420957 233593303984302940657859)
                    ·
                      rfl

theorem cell22_682382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_682382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_682382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_682382 prefixEnd_682382 := by exact prefixLift 682382
  have htrace : WordTrace (prefixWord ++ tailWord_682382) baseStart_682382 baseEnd_682382 := by
    simpa [prefixWord, tailWord_682382, baseEnd_682382] using wordTrace_append hprefix tailTrace_682382
  have hstable : (prefixWord ++ tailWord_682382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682382).length < 2 ^ (prefixWord ++ tailWord_682382).sum := by decide
  have hdescent : baseEnd_682382 < baseStart_682382 := by decide
  rcases family_descends (prefixWord ++ tailWord_682382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682433 : List Nat := [1, 2, 7, 1, 1, 1, 1, 4, 1, 3]
def baseStart_682433 : Nat := 118140960795 + 682433 * 2 ^ 59
def prefixEnd_682433 : Nat := 4983230072969 + 3 ^ 40 * 682433 * 2
def baseEnd_682433 : Nat := 233610762326555807632703

theorem tailTrace_682433 : CollatzResearch.WordTrace tailWord_682433 prefixEnd_682433 233610762326555807632703 := by
  unfold tailWord_682433
  simp only [CollatzResearch.WordTrace]
  refine ⟨24890376336669266122467953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16593584224446177414978635 24890376336669266122467953)
  ·
    refine ⟨18667782252501949591850965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24890376336669266122467953 18667782252501949591850965)
    ·
      refine ⟨437526146543014443559007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 18667782252501949591850965 437526146543014443559007)
      ·
        refine ⟨656289219814521665338511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437526146543014443559007 656289219814521665338511)
        ·
          refine ⟨984433829721782498007767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 656289219814521665338511 984433829721782498007767)
          ·
            refine ⟨1476650744582673747011651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 984433829721782498007767 1476650744582673747011651)
            ·
              refine ⟨2214976116874010620517477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1476650744582673747011651 2214976116874010620517477)
              ·
                refine ⟨415308021913876991347027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2214976116874010620517477 415308021913876991347027)
                ·
                  refine ⟨622962032870815487020541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 415308021913876991347027 622962032870815487020541)
                  ·
                    refine ⟨233610762326555807632703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 622962032870815487020541 233610762326555807632703)
                    ·
                      rfl

theorem cell22_682433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_682433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_682433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_682433 prefixEnd_682433 := by exact prefixLift 682433
  have htrace : WordTrace (prefixWord ++ tailWord_682433) baseStart_682433 baseEnd_682433 := by
    simpa [prefixWord, tailWord_682433, baseEnd_682433] using wordTrace_append hprefix tailTrace_682433
  have hstable : (prefixWord ++ tailWord_682433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682433).length < 2 ^ (prefixWord ++ tailWord_682433).sum := by decide
  have hdescent : baseEnd_682433 < baseStart_682433 := by decide
  rcases family_descends (prefixWord ++ tailWord_682433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682519 : List Nat := [1, 1, 3, 6, 1, 2, 2, 6]
def baseStart_682519 : Nat := 118140960795 + 682519 * 2 ^ 59
def prefixEnd_682519 : Nat := 4983230072969 + 3 ^ 40 * 682519 * 2
def baseEnd_682519 : Nat := 25960022431564472220271

theorem tailTrace_682519 : CollatzResearch.WordTrace tailWord_682519 prefixEnd_682519 25960022431564472220271 := by
  unfold tailWord_682519
  simp only [CollatzResearch.WordTrace]
  refine ⟨24893513014357702810098611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16595675342905135206732407 24893513014357702810098611)
  ·
    refine ⟨37340269521536554215147917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24893513014357702810098611 37340269521536554215147917)
    ·
      refine ⟨14002601070576207830680469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37340269521536554215147917 14002601070576207830680469)
      ·
        refine ⟨656371925183259742063147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14002601070576207830680469 656371925183259742063147)
        ·
          refine ⟨984557887774889613094721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 656371925183259742063147 984557887774889613094721)
          ·
            refine ⟨738418415831167209821041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 984557887774889613094721 738418415831167209821041)
            ·
              refine ⟨553813811873375407365781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 738418415831167209821041 553813811873375407365781)
              ·
                refine ⟨25960022431564472220271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 553813811873375407365781 25960022431564472220271)
                ·
                  rfl

theorem cell22_682519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 6].length) (baseStart_682519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_682519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_682519 prefixEnd_682519 := by exact prefixLift 682519
  have htrace : WordTrace (prefixWord ++ tailWord_682519) baseStart_682519 baseEnd_682519 := by
    simpa [prefixWord, tailWord_682519, baseEnd_682519] using wordTrace_append hprefix tailTrace_682519
  have hstable : (prefixWord ++ tailWord_682519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682519).length < 2 ^ (prefixWord ++ tailWord_682519).sum := by decide
  have hdescent : baseEnd_682519 < baseStart_682519 := by decide
  rcases family_descends (prefixWord ++ tailWord_682519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682577 : List Nat := [1, 2, 2, 1, 3, 3, 3, 2, 1, 4]
def baseStart_682577 : Nat := 118140960795 + 682577 * 2 ^ 59
def prefixEnd_682577 : Nat := 4983230072969 + 3 ^ 40 * 682577 * 2
def baseEnd_682577 : Nat := 233660056469387432032261

theorem tailTrace_682577 : CollatzResearch.WordTrace tailWord_682577 prefixEnd_682577 233660056469387432032261 := by
  unfold tailWord_682577
  simp only [CollatzResearch.WordTrace]
  refine ⟨24895628448147578715709985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16597085632098385810473323 24895628448147578715709985)
  ·
    refine ⟨18671721336110684036782489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24895628448147578715709985 18671721336110684036782489)
    ·
      refine ⟨14003791002083013027586867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18671721336110684036782489 14003791002083013027586867)
      ·
        refine ⟨21005686503124519541380301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14003791002083013027586867 21005686503124519541380301)
        ·
          refine ⟨7877132438671694828017613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21005686503124519541380301 7877132438671694828017613)
          ·
            refine ⟨2953924664501885560506605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7877132438671694828017613 2953924664501885560506605)
            ·
              refine ⟨1107721749188207085189977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2953924664501885560506605 1107721749188207085189977)
              ·
                refine ⟨830791311891155313892483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1107721749188207085189977 830791311891155313892483)
                ·
                  refine ⟨1246186967836732970838725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 830791311891155313892483 1246186967836732970838725)
                  ·
                    refine ⟨233660056469387432032261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1246186967836732970838725 233660056469387432032261)
                    ·
                      rfl

theorem cell22_682577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_682577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_682577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_682577 prefixEnd_682577 := by exact prefixLift 682577
  have htrace : WordTrace (prefixWord ++ tailWord_682577) baseStart_682577 baseEnd_682577 := by
    simpa [prefixWord, tailWord_682577, baseEnd_682577] using wordTrace_append hprefix tailTrace_682577
  have hstable : (prefixWord ++ tailWord_682577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682577).length < 2 ^ (prefixWord ++ tailWord_682577).sum := by decide
  have hdescent : baseEnd_682577 < baseStart_682577 := by decide
  rcases family_descends (prefixWord ++ tailWord_682577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682607 : List Nat := [1, 1, 2, 1, 3, 2, 3, 4, 2, 3]
def baseStart_682607 : Nat := 118140960795 + 682607 * 2 ^ 59
def prefixEnd_682607 : Nat := 4983230072969 + 3 ^ 40 * 682607 * 2
def baseEnd_682607 : Nat := 233670326082477353782169

theorem tailTrace_682607 : CollatzResearch.WordTrace tailWord_682607 prefixEnd_682607 233670326082477353782169 := by
  unfold tailWord_682607
  simp only [CollatzResearch.WordTrace]
  refine ⟨24896722638038893839302075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16597815092025929226201383 24896722638038893839302075)
  ·
    refine ⟨37345083957058340758953113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24896722638038893839302075 37345083957058340758953113)
    ·
      refine ⟨28008812967793755569214835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37345083957058340758953113 28008812967793755569214835)
      ·
        refine ⟨42013219451690633353822253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28008812967793755569214835 42013219451690633353822253)
        ·
          refine ⟨15754957294383987507683345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42013219451690633353822253 15754957294383987507683345)
          ·
            refine ⟨11816217970787990630762509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15754957294383987507683345 11816217970787990630762509)
            ·
              refine ⟨4431081739045496486535941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11816217970787990630762509 4431081739045496486535941)
              ·
                refine ⟨830827826071030591225489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4431081739045496486535941 830827826071030591225489)
                ·
                  refine ⟨623120869553272943419117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 830827826071030591225489 623120869553272943419117)
                  ·
                    refine ⟨233670326082477353782169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 623120869553272943419117 233670326082477353782169)
                    ·
                      rfl

theorem cell22_682607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 2, 3].length) (baseStart_682607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_682607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_682607 prefixEnd_682607 := by exact prefixLift 682607
  have htrace : WordTrace (prefixWord ++ tailWord_682607) baseStart_682607 baseEnd_682607 := by
    simpa [prefixWord, tailWord_682607, baseEnd_682607] using wordTrace_append hprefix tailTrace_682607
  have hstable : (prefixWord ++ tailWord_682607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682607).length < 2 ^ (prefixWord ++ tailWord_682607).sum := by decide
  have hdescent : baseEnd_682607 < baseStart_682607 := by decide
  rcases family_descends (prefixWord ++ tailWord_682607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682620 : List Nat := [2, 2, 2, 1, 1, 2, 5, 7]
def baseStart_682620 : Nat := 118140960795 + 682620 * 2 ^ 59
def prefixEnd_682620 : Nat := 4983230072969 + 3 ^ 40 * 682620 * 2
def baseEnd_682620 : Nat := 25963864027572183689681

theorem tailTrace_682620 : CollatzResearch.WordTrace tailWord_682620 prefixEnd_682620 25963864027572183689681 := by
  unfold tailWord_682620
  simp only [CollatzResearch.WordTrace]
  refine ⟨12448598393495898529762657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16598131191327864706350209 12448598393495898529762657)
  ·
    refine ⟨9336448795121923897321993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12448598393495898529762657 9336448795121923897321993)
    ·
      refine ⟨7002336596341442922991495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9336448795121923897321993 7002336596341442922991495)
      ·
        refine ⟨10503504894512164384487243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7002336596341442922991495 10503504894512164384487243)
        ·
          refine ⟨15755257341768246576730865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10503504894512164384487243 15755257341768246576730865)
          ·
            refine ⟨11816443006326184932548149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15755257341768246576730865 11816443006326184932548149)
            ·
              refine ⟨1107791531843079837426389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11816443006326184932548149 1107791531843079837426389)
              ·
                refine ⟨25963864027572183689681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1107791531843079837426389 25963864027572183689681)
                ·
                  rfl

theorem cell22_682620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 7].length) (baseStart_682620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_682620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_682620 prefixEnd_682620 := by exact prefixLift 682620
  have htrace : WordTrace (prefixWord ++ tailWord_682620) baseStart_682620 baseEnd_682620 := by
    simpa [prefixWord, tailWord_682620, baseEnd_682620] using wordTrace_append hprefix tailTrace_682620
  have hstable : (prefixWord ++ tailWord_682620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682620).length < 2 ^ (prefixWord ++ tailWord_682620).sum := by decide
  have hdescent : baseEnd_682620 < baseStart_682620 := by decide
  rcases family_descends (prefixWord ++ tailWord_682620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682669 : List Nat := [1, 5, 2, 1, 1, 2, 1, 3, 3, 3]
def baseStart_682669 : Nat := 118140960795 + 682669 * 2 ^ 59
def prefixEnd_682669 : Nat := 4983230072969 + 3 ^ 40 * 682669 * 2
def baseEnd_682669 : Nat := 233691549949529858731979

theorem tailTrace_682669 : CollatzResearch.WordTrace tailWord_682669 prefixEnd_682669 233691549949529858731979 := by
  unfold tailWord_682669
  simp only [CollatzResearch.WordTrace]
  refine ⟨24898983963814278428059061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16599322642542852285372707 24898983963814278428059061)
  ·
    refine ⟨2334279746607588602630537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24898983963814278428059061 2334279746607588602630537)
    ·
      refine ⟨1750709809955691451972903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2334279746607588602630537 1750709809955691451972903)
      ·
        refine ⟨2626064714933537177959355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1750709809955691451972903 2626064714933537177959355)
        ·
          refine ⟨3939097072400305766939033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2626064714933537177959355 3939097072400305766939033)
          ·
            refine ⟨2954322804300229325204275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3939097072400305766939033 2954322804300229325204275)
            ·
              refine ⟨4431484206450343987806413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2954322804300229325204275 4431484206450343987806413)
              ·
                refine ⟨1661806577418878995427405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4431484206450343987806413 1661806577418878995427405)
                ·
                  refine ⟨623177466532079623285277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1661806577418878995427405 623177466532079623285277)
                  ·
                    refine ⟨233691549949529858731979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 623177466532079623285277 233691549949529858731979)
                    ·
                      rfl

theorem cell22_682669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_682669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_682669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_682669 prefixEnd_682669 := by exact prefixLift 682669
  have htrace : WordTrace (prefixWord ++ tailWord_682669) baseStart_682669 baseEnd_682669 := by
    simpa [prefixWord, tailWord_682669, baseEnd_682669] using wordTrace_append hprefix tailTrace_682669
  have hstable : (prefixWord ++ tailWord_682669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682669).length < 2 ^ (prefixWord ++ tailWord_682669).sum := by decide
  have hdescent : baseEnd_682669 < baseStart_682669 := by decide
  rcases family_descends (prefixWord ++ tailWord_682669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682759 : List Nat := [1, 1, 4, 4, 1, 2, 1, 2, 1, 5]
def baseStart_682759 : Nat := 118140960795 + 682759 * 2 ^ 59
def prefixEnd_682759 : Nat := 4983230072969 + 3 ^ 40 * 682759 * 2
def baseEnd_682759 : Nat := 233722358788799623981703

theorem tailTrace_682759 : CollatzResearch.WordTrace tailWord_682759 prefixEnd_682759 233722358788799623981703 := by
  unfold tailWord_682759
  simp only [CollatzResearch.WordTrace]
  refine ⟨24902266533488223798835331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16601511022325482532556887 24902266533488223798835331)
  ·
    refine ⟨37353399800232335698252997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24902266533488223798835331 37353399800232335698252997)
    ·
      refine ⟨7003762462543562943422437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37353399800232335698252997 7003762462543562943422437)
      ·
        refine ⟨1313205461726918051891707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7003762462543562943422437 1313205461726918051891707)
        ·
          refine ⟨1969808192590377077837561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1313205461726918051891707 1969808192590377077837561)
          ·
            refine ⟨1477356144442782808378171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1969808192590377077837561 1477356144442782808378171)
            ·
              refine ⟨2216034216664174212567257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1477356144442782808378171 2216034216664174212567257)
              ·
                refine ⟨1662025662498130659425443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2216034216664174212567257 1662025662498130659425443)
                ·
                  refine ⟨2493038493747195989138165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1662025662498130659425443 2493038493747195989138165)
                  ·
                    refine ⟨233722358788799623981703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2493038493747195989138165 233722358788799623981703)
                    ·
                      rfl

theorem cell22_682759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_682759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_682759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_682759 prefixEnd_682759 := by exact prefixLift 682759
  have htrace : WordTrace (prefixWord ++ tailWord_682759) baseStart_682759 baseEnd_682759 := by
    simpa [prefixWord, tailWord_682759, baseEnd_682759] using wordTrace_append hprefix tailTrace_682759
  have hstable : (prefixWord ++ tailWord_682759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682759).length < 2 ^ (prefixWord ++ tailWord_682759).sum := by decide
  have hdescent : baseEnd_682759 < baseStart_682759 := by decide
  rcases family_descends (prefixWord ++ tailWord_682759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682802 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 2, 6]
def baseStart_682802 : Nat := 118140960795 + 682802 * 2 ^ 59
def prefixEnd_682802 : Nat := 4983230072969 + 3 ^ 40 * 682802 * 2
def baseEnd_682802 : Nat := 233737078567561845156571

theorem tailTrace_682802 : CollatzResearch.WordTrace tailWord_682802 prefixEnd_682802 233737078567561845156571 := by
  unfold tailWord_682802
  simp only [CollatzResearch.WordTrace]
  refine ⟨6225958718083110535662665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16602556581554961428433773 6225958718083110535662665)
  ·
    refine ⟨4669469038562332901746999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6225958718083110535662665 4669469038562332901746999)
    ·
      refine ⟨7004203557843499352620499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4669469038562332901746999 7004203557843499352620499)
      ·
        refine ⟨10506305336765249028930749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7004203557843499352620499 10506305336765249028930749)
        ·
          refine ⟨3939864501286968385849031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10506305336765249028930749 3939864501286968385849031)
          ·
            refine ⟨5909796751930452578773547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3939864501286968385849031 5909796751930452578773547)
            ·
              refine ⟨8864695127895678868160321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5909796751930452578773547 8864695127895678868160321)
              ·
                refine ⟨6648521345921759151120241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8864695127895678868160321 6648521345921759151120241)
                ·
                  refine ⟨4986391009441319363340181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6648521345921759151120241 4986391009441319363340181)
                  ·
                    refine ⟨233737078567561845156571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4986391009441319363340181 233737078567561845156571)
                    ·
                      rfl

theorem cell22_682802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_682802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_682802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_682802 prefixEnd_682802 := by exact prefixLift 682802
  have htrace : WordTrace (prefixWord ++ tailWord_682802) baseStart_682802 baseEnd_682802 := by
    simpa [prefixWord, tailWord_682802, baseEnd_682802] using wordTrace_append hprefix tailTrace_682802
  have hstable : (prefixWord ++ tailWord_682802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682802).length < 2 ^ (prefixWord ++ tailWord_682802).sum := by decide
  have hdescent : baseEnd_682802 < baseStart_682802 := by decide
  rcases family_descends (prefixWord ++ tailWord_682802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682832 : List Nat := [2, 1, 1, 1, 1, 4, 3, 2, 2, 5]
def baseStart_682832 : Nat := 118140960795 + 682832 * 2 ^ 59
def prefixEnd_682832 : Nat := 4983230072969 + 3 ^ 40 * 682832 * 2
def baseEnd_682832 : Nat := 233747348180651766906479

theorem tailTrace_682832 : CollatzResearch.WordTrace tailWord_682832 prefixEnd_682832 233747348180651766906479 := by
  unfold tailWord_682832
  simp only [CollatzResearch.WordTrace]
  refine ⟨12452464531111878633121375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16603286041482504844161833 12452464531111878633121375)
  ·
    refine ⟨18678696796667817949682063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12452464531111878633121375 18678696796667817949682063)
    ·
      refine ⟨28018045195001726924523095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18678696796667817949682063 28018045195001726924523095)
      ·
        refine ⟨42027067792502590386784643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28018045195001726924523095 42027067792502590386784643)
        ·
          refine ⟨63040601688753885580176965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42027067792502590386784643 63040601688753885580176965)
          ·
            refine ⟨11820112816641353546283181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63040601688753885580176965 11820112816641353546283181)
            ·
              refine ⟨4432542306240507579856193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11820112816641353546283181 4432542306240507579856193)
              ·
                refine ⟨3324406729680380684892145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4432542306240507579856193 3324406729680380684892145)
                ·
                  refine ⟨2493305047260285513669109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3324406729680380684892145 2493305047260285513669109)
                  ·
                    refine ⟨233747348180651766906479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2493305047260285513669109 233747348180651766906479)
                    ·
                      rfl

theorem cell22_682832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 2, 5].length) (baseStart_682832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_682832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_682832 prefixEnd_682832 := by exact prefixLift 682832
  have htrace : WordTrace (prefixWord ++ tailWord_682832) baseStart_682832 baseEnd_682832 := by
    simpa [prefixWord, tailWord_682832, baseEnd_682832] using wordTrace_append hprefix tailTrace_682832
  have hstable : (prefixWord ++ tailWord_682832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682832).length < 2 ^ (prefixWord ++ tailWord_682832).sum := by decide
  have hdescent : baseEnd_682832 < baseStart_682832 := by decide
  rcases family_descends (prefixWord ++ tailWord_682832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682851 : List Nat := [1, 1, 1, 5, 3, 2, 3, 1, 5]
def baseStart_682851 : Nat := 118140960795 + 682851 * 2 ^ 59
def prefixEnd_682851 : Nat := 4983230072969 + 3 ^ 40 * 682851 * 2
def baseEnd_682851 : Nat := 77917950756314016893807

theorem tailTrace_682851 : CollatzResearch.WordTrace tailWord_682851 prefixEnd_682851 77917950756314016893807 := by
  unfold tailWord_682851
  simp only [CollatzResearch.WordTrace]
  refine ⟨24905622049154923511184407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16603748032769949007456271 24905622049154923511184407)
  ·
    refine ⟨37358433073732385266776611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24905622049154923511184407 37358433073732385266776611)
    ·
      refine ⟨56037649610598577900164917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37358433073732385266776611 56037649610598577900164917)
      ·
        refine ⟨5253529650993616678140461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56037649610598577900164917 5253529650993616678140461)
        ·
          refine ⟨1970073619122606254302673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5253529650993616678140461 1970073619122606254302673)
          ·
            refine ⟨1477555214341954690727005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1970073619122606254302673 1477555214341954690727005)
            ·
              refine ⟨554083205378233009022627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1477555214341954690727005 554083205378233009022627)
              ·
                refine ⟨831124808067349513533941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 554083205378233009022627 831124808067349513533941)
                ·
                  refine ⟨77917950756314016893807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 831124808067349513533941 77917950756314016893807)
                  ·
                    rfl

theorem cell22_682851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 5].length) (baseStart_682851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_682851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_682851 prefixEnd_682851 := by exact prefixLift 682851
  have htrace : WordTrace (prefixWord ++ tailWord_682851) baseStart_682851 baseEnd_682851 := by
    simpa [prefixWord, tailWord_682851, baseEnd_682851] using wordTrace_append hprefix tailTrace_682851
  have hstable : (prefixWord ++ tailWord_682851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682851).length < 2 ^ (prefixWord ++ tailWord_682851).sum := by decide
  have hdescent : baseEnd_682851 < baseStart_682851 := by decide
  rcases family_descends (prefixWord ++ tailWord_682851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682864 : List Nat := [2, 1, 1, 1, 4, 1, 3, 4, 1, 4]
def baseStart_682864 : Nat := 118140960795 + 682864 * 2 ^ 59
def prefixEnd_682864 : Nat := 4983230072969 + 3 ^ 40 * 682864 * 2
def baseEnd_682864 : Nat := 233758302434614350106381

theorem tailTrace_682864 : CollatzResearch.WordTrace tailWord_682864 prefixEnd_682864 233758302434614350106381 := by
  unfold tailWord_682864
  simp only [CollatzResearch.WordTrace]
  refine ⟨12453048099053913365703823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16604064132071884487605097 12453048099053913365703823)
  ·
    refine ⟨18679572148580870048555735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12453048099053913365703823 18679572148580870048555735)
    ·
      refine ⟨28019358222871305072833603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18679572148580870048555735 28019358222871305072833603)
      ·
        refine ⟨42029037334306957609250405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28019358222871305072833603 42029037334306957609250405)
        ·
          refine ⟨7880444500182554551734451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42029037334306957609250405 7880444500182554551734451)
          ·
            refine ⟨11820666750273831827601677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7880444500182554551734451 11820666750273831827601677)
            ·
              refine ⟨4432750031352686935350629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11820666750273831827601677 4432750031352686935350629)
              ·
                refine ⟨831140630878628800378243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4432750031352686935350629 831140630878628800378243)
                ·
                  refine ⟨1246710946317943200567365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 831140630878628800378243 1246710946317943200567365)
                  ·
                    refine ⟨233758302434614350106381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1246710946317943200567365 233758302434614350106381)
                    ·
                      rfl

theorem cell22_682864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 1, 4].length) (baseStart_682864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_682864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_682864 prefixEnd_682864 := by exact prefixLift 682864
  have htrace : WordTrace (prefixWord ++ tailWord_682864) baseStart_682864 baseEnd_682864 := by
    simpa [prefixWord, tailWord_682864, baseEnd_682864] using wordTrace_append hprefix tailTrace_682864
  have hstable : (prefixWord ++ tailWord_682864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682864).length < 2 ^ (prefixWord ++ tailWord_682864).sum := by decide
  have hdescent : baseEnd_682864 < baseStart_682864 := by decide
  rcases family_descends (prefixWord ++ tailWord_682864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682902 : List Nat := [5, 3, 1, 1, 1, 3, 2, 1, 5]
def baseStart_682902 : Nat := 118140960795 + 682902 * 2 ^ 59
def prefixEnd_682902 : Nat := 4983230072969 + 3 ^ 40 * 682902 * 2
def baseEnd_682902 : Nat := 77923770203731639218755

theorem tailTrace_682902 : CollatzResearch.WordTrace tailWord_682902 prefixEnd_682902 77923770203731639218755 := by
  unfold tailWord_682902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1556717635748134951330685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16604988114646772814193973 1556717635748134951330685)
  ·
    refine ⟨583769113405550606749007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1556717635748134951330685 583769113405550606749007)
    ·
      refine ⟨875653670108325910123511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 583769113405550606749007 875653670108325910123511)
      ·
        refine ⟨1313480505162488865185267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 875653670108325910123511 1313480505162488865185267)
        ·
          refine ⟨1970220757743733297777901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1313480505162488865185267 1970220757743733297777901)
          ·
            refine ⟨738832784153899986666713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1970220757743733297777901 738832784153899986666713)
            ·
              refine ⟨554124588115424990000035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 738832784153899986666713 554124588115424990000035)
              ·
                refine ⟨831186882173137485000053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 554124588115424990000035 831186882173137485000053)
                ·
                  refine ⟨77923770203731639218755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 831186882173137485000053 77923770203731639218755)
                  ·
                    rfl

theorem cell22_682902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_682902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_682902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_682902 prefixEnd_682902 := by exact prefixLift 682902
  have htrace : WordTrace (prefixWord ++ tailWord_682902) baseStart_682902 baseEnd_682902 := by
    simpa [prefixWord, tailWord_682902, baseEnd_682902] using wordTrace_append hprefix tailTrace_682902
  have hstable : (prefixWord ++ tailWord_682902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682902).length < 2 ^ (prefixWord ++ tailWord_682902).sum := by decide
  have hdescent : baseEnd_682902 < baseStart_682902 := by decide
  rcases family_descends (prefixWord ++ tailWord_682902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682909 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 4, 4]
def baseStart_682909 : Nat := 118140960795 + 682909 * 2 ^ 59
def prefixEnd_682909 : Nat := 4983230072969 + 3 ^ 40 * 682909 * 2
def baseEnd_682909 : Nat := 233773706854249232731243

theorem tailTrace_682909 : CollatzResearch.WordTrace tailWord_682909 prefixEnd_682909 233773706854249232731243 := by
  unfold tailWord_682909
  simp only [CollatzResearch.WordTrace]
  refine ⟨24907737482944799416795781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16605158321963199611197187 24907737482944799416795781)
  ·
    refine ⟨4670200778052149890649209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24907737482944799416795781 4670200778052149890649209)
    ·
      refine ⟨3502650583539112417986907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4670200778052149890649209 3502650583539112417986907)
      ·
        refine ⟨5253975875308668626980361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3502650583539112417986907 5253975875308668626980361)
        ·
          refine ⟨3940481906481501470235271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5253975875308668626980361 3940481906481501470235271)
          ·
            refine ⟨5910722859722252205352907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3940481906481501470235271 5910722859722252205352907)
            ·
              refine ⟨8866084289583378308029361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5910722859722252205352907 8866084289583378308029361)
              ·
                refine ⟨6649563217187533731022021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8866084289583378308029361 6649563217187533731022021)
                ·
                  refine ⟨1246793103222662574566629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6649563217187533731022021 1246793103222662574566629)
                  ·
                    refine ⟨233773706854249232731243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1246793103222662574566629 233773706854249232731243)
                    ·
                      rfl

theorem cell22_682909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_682909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_682909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_682909 prefixEnd_682909 := by exact prefixLift 682909
  have htrace : WordTrace (prefixWord ++ tailWord_682909) baseStart_682909 baseEnd_682909 := by
    simpa [prefixWord, tailWord_682909, baseEnd_682909] using wordTrace_append hprefix tailTrace_682909
  have hstable : (prefixWord ++ tailWord_682909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682909).length < 2 ^ (prefixWord ++ tailWord_682909).sum := by decide
  have hdescent : baseEnd_682909 < baseStart_682909 := by decide
  rcases family_descends (prefixWord ++ tailWord_682909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682956 : List Nat := [2, 2, 1, 4, 1, 1, 2, 3, 3, 3]
def baseStart_682956 : Nat := 118140960795 + 682956 * 2 ^ 59
def prefixEnd_682956 : Nat := 4983230072969 + 3 ^ 40 * 682956 * 2
def baseEnd_682956 : Nat := 233789795914756776806099

theorem tailTrace_682956 : CollatzResearch.WordTrace tailWord_682956 prefixEnd_682956 233789795914756776806099 := by
  unfold tailWord_682956
  simp only [CollatzResearch.WordTrace]
  refine ⟨12454725856887263221878361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16606301142516350962504481 12454725856887263221878361)
  ·
    refine ⟨9341044392665447416408771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12454725856887263221878361 9341044392665447416408771)
    ·
      refine ⟨14011566588998171124613157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9341044392665447416408771 14011566588998171124613157)
      ·
        refine ⟨2627168735437157085864967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14011566588998171124613157 2627168735437157085864967)
        ·
          refine ⟨3940753103155735628797451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2627168735437157085864967 3940753103155735628797451)
          ·
            refine ⟨5911129654733603443196177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3940753103155735628797451 5911129654733603443196177)
            ·
              refine ⟨4433347241050202582397133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5911129654733603443196177 4433347241050202582397133)
              ·
                refine ⟨1662505215393825968398925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4433347241050202582397133 1662505215393825968398925)
                ·
                  refine ⟨623439455772684738149597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1662505215393825968398925 623439455772684738149597)
                  ·
                    refine ⟨233789795914756776806099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 623439455772684738149597 233789795914756776806099)
                    ·
                      rfl

theorem cell22_682956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 3, 3].length) (baseStart_682956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_682956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_682956 prefixEnd_682956 := by exact prefixLift 682956
  have htrace : WordTrace (prefixWord ++ tailWord_682956) baseStart_682956 baseEnd_682956 := by
    simpa [prefixWord, tailWord_682956, baseEnd_682956] using wordTrace_append hprefix tailTrace_682956
  have hstable : (prefixWord ++ tailWord_682956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682956).length < 2 ^ (prefixWord ++ tailWord_682956).sum := by decide
  have hdescent : baseEnd_682956 < baseStart_682956 := by decide
  rcases family_descends (prefixWord ++ tailWord_682956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682973 : List Nat := [1, 4, 3, 1, 2, 2, 1, 2, 3, 3]
def baseStart_682973 : Nat := 118140960795 + 682973 * 2 ^ 59
def prefixEnd_682973 : Nat := 4983230072969 + 3 ^ 40 * 682973 * 2
def baseEnd_682973 : Nat := 233795615362174399131047

theorem tailTrace_682973 : CollatzResearch.WordTrace tailWord_682973 prefixEnd_682973 233795615362174399131047 := by
  unfold tailWord_682973
  simp only [CollatzResearch.WordTrace]
  refine ⟨24910071754712938347125573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16606714503141958898083715 24910071754712938347125573)
  ·
    refine ⟨4670638454008675940086045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24910071754712938347125573 4670638454008675940086045)
    ·
      refine ⟨1751489420253253477532267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4670638454008675940086045 1751489420253253477532267)
      ·
        refine ⟨2627234130379880216298401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1751489420253253477532267 2627234130379880216298401)
        ·
          refine ⟨1970425597784910162223801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2627234130379880216298401 1970425597784910162223801)
          ·
            refine ⟨1477819198338682621667851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1970425597784910162223801 1477819198338682621667851)
            ·
              refine ⟨2216728797508023932501777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1477819198338682621667851 2216728797508023932501777)
              ·
                refine ⟨1662546598131017949376333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2216728797508023932501777 1662546598131017949376333)
                ·
                  refine ⟨623454974299131731016125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1662546598131017949376333 623454974299131731016125)
                  ·
                    refine ⟨233795615362174399131047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 623454974299131731016125 233795615362174399131047)
                    ·
                      rfl

theorem cell22_682973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_682973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_682973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_682973 prefixEnd_682973 := by exact prefixLift 682973
  have htrace : WordTrace (prefixWord ++ tailWord_682973) baseStart_682973 baseEnd_682973 := by
    simpa [prefixWord, tailWord_682973, baseEnd_682973] using wordTrace_append hprefix tailTrace_682973
  have hstable : (prefixWord ++ tailWord_682973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682973).length < 2 ^ (prefixWord ++ tailWord_682973).sum := by decide
  have hdescent : baseEnd_682973 < baseStart_682973 := by decide
  rcases family_descends (prefixWord ++ tailWord_682973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
