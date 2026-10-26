import V185TrunkScan23Chunk0638

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3779201 : List Nat := [1, 2, 4, 2, 1, 1, 1, 3, 2, 4, 2]
def baseStart_3779201 : Nat := 118140960795 + 3779201 * 2 ^ 59
def prefixEnd_3779201 : Nat := 4983230072969 + 3 ^ 40 * 3779201 * 2
def baseEnd_3779201 : Nat := 1940546602952373592407277

theorem tailTrace_3779201 : CollatzResearch.WordTrace tailWord_3779201 prefixEnd_3779201 1940546602952373592407277 := by
  unfold tailWord_3779201
  simp only [CollatzResearch.WordTrace]
  refine ⟨137838784381607687990113457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91892522921071791993408971 137838784381607687990113457)
  ·
    refine ⟨103379088286205765992585093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137838784381607687990113457 103379088286205765992585093)
    ·
      refine ⟨19383579053663581123609705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103379088286205765992585093 19383579053663581123609705)
      ·
        refine ⟨14537684290247685842707279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19383579053663581123609705 14537684290247685842707279)
        ·
          refine ⟨21806526435371528764060919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14537684290247685842707279 21806526435371528764060919)
          ·
            refine ⟨32709789653057293146091379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21806526435371528764060919 32709789653057293146091379)
            ·
              refine ⟨49064684479585939719137069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32709789653057293146091379 49064684479585939719137069)
              ·
                refine ⟨18399256679844727394676401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49064684479585939719137069 18399256679844727394676401)
                ·
                  refine ⟨13799442509883545546007301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18399256679844727394676401 13799442509883545546007301)
                  ·
                    refine ⟨2587395470603164789876369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13799442509883545546007301 2587395470603164789876369)
                    ·
                      refine ⟨1940546602952373592407277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2587395470603164789876369 1940546602952373592407277)
                      ·
                        rfl

theorem cell23_3779201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_3779201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779201 prefixEnd_3779201 := by exact prefixLift 3779201
  have htrace : WordTrace (prefixWord ++ tailWord_3779201) baseStart_3779201 baseEnd_3779201 := by
    simpa [prefixWord, tailWord_3779201, baseEnd_3779201] using wordTrace_append hprefix tailTrace_3779201
  have hstable : (prefixWord ++ tailWord_3779201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779201).length < 2 ^ (prefixWord ++ tailWord_3779201).sum := by decide
  have hdescent : baseEnd_3779201 < baseStart_3779201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779214 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4]
def baseStart_3779214 : Nat := 118140960795 + 3779214 * 2 ^ 59
def prefixEnd_3779214 : Nat := 4983230072969 + 3 ^ 40 * 3779214 * 2
def baseEnd_3779214 : Nat := 1940553278200882041544717

theorem tailTrace_3779214 : CollatzResearch.WordTrace tailWord_3779214 prefixEnd_3779214 1940553278200882041544717 := by
  unfold tailWord_3779214
  simp only [CollatzResearch.WordTrace]
  refine ⟨17229907316320073901292087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91892839020373727473557797 17229907316320073901292087)
  ·
    refine ⟨25844860974480110851938131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17229907316320073901292087 25844860974480110851938131)
    ·
      refine ⟨38767291461720166277907197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25844860974480110851938131 38767291461720166277907197)
      ·
        refine ⟨14537734298145062354215199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38767291461720166277907197 14537734298145062354215199)
        ·
          refine ⟨21806601447217593531322799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14537734298145062354215199 21806601447217593531322799)
          ·
            refine ⟨32709902170826390296984199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21806601447217593531322799 32709902170826390296984199)
            ·
              refine ⟨49064853256239585445476299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32709902170826390296984199 49064853256239585445476299)
              ·
                refine ⟨73597279884359378168214449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49064853256239585445476299 73597279884359378168214449)
                ·
                  refine ⟨55197959913269533626160837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73597279884359378168214449 55197959913269533626160837)
                  ·
                    refine ⟨10349617483738037554905157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55197959913269533626160837 10349617483738037554905157)
                    ·
                      refine ⟨1940553278200882041544717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10349617483738037554905157 1940553278200882041544717)
                      ·
                        rfl

theorem cell23_3779214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_3779214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779214 prefixEnd_3779214 := by exact prefixLift 3779214
  have htrace : WordTrace (prefixWord ++ tailWord_3779214) baseStart_3779214 baseEnd_3779214 := by
    simpa [prefixWord, tailWord_3779214, baseEnd_3779214] using wordTrace_append hprefix tailTrace_3779214
  have hstable : (prefixWord ++ tailWord_3779214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779214).length < 2 ^ (prefixWord ++ tailWord_3779214).sum := by decide
  have hdescent : baseEnd_3779214 < baseStart_3779214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779278 : List Nat := [4, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2]
def baseStart_3779278 : Nat := 118140960795 + 3779278 * 2 ^ 59
def prefixEnd_3779278 : Nat := 4983230072969 + 3 ^ 40 * 3779278 * 2
def baseEnd_3779278 : Nat := 1940586140962769791144423

theorem tailTrace_3779278 : CollatzResearch.WordTrace tailWord_3779278 prefixEnd_3779278 1940586140962769791144423 := by
  unfold tailWord_3779278
  simp only [CollatzResearch.WordTrace]
  refine ⟨17230199100291091267583311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91894395201552486760444325 17230199100291091267583311)
  ·
    refine ⟨25845298650436636901374967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17230199100291091267583311 25845298650436636901374967)
    ·
      refine ⟨38767947975654955352062451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25845298650436636901374967 38767947975654955352062451)
      ·
        refine ⟨58151921963482433028093677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38767947975654955352062451 58151921963482433028093677)
        ·
          refine ⟨21806970736305912385535129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58151921963482433028093677 21806970736305912385535129)
          ·
            refine ⟨16355228052229434289151347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21806970736305912385535129 16355228052229434289151347)
            ·
              refine ⟨24532842078344151433727021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16355228052229434289151347 24532842078344151433727021)
              ·
                refine ⟨9199815779379056787647633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24532842078344151433727021 9199815779379056787647633)
                ·
                  refine ⟨6899861834534292590735725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9199815779379056787647633 6899861834534292590735725)
                  ·
                    refine ⟨2587448187950359721525897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6899861834534292590735725 2587448187950359721525897)
                    ·
                      refine ⟨1940586140962769791144423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2587448187950359721525897 1940586140962769791144423)
                      ·
                        rfl

theorem cell23_3779278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2].length) (baseStart_3779278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779278 prefixEnd_3779278 := by exact prefixLift 3779278
  have htrace : WordTrace (prefixWord ++ tailWord_3779278) baseStart_3779278 baseEnd_3779278 := by
    simpa [prefixWord, tailWord_3779278, baseEnd_3779278] using wordTrace_append hprefix tailTrace_3779278
  have hstable : (prefixWord ++ tailWord_3779278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779278).length < 2 ^ (prefixWord ++ tailWord_3779278).sum := by decide
  have hdescent : baseEnd_3779278 < baseStart_3779278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779288 : List Nat := [2, 1, 2, 2, 3, 3, 3, 1, 1, 5]
def baseStart_3779288 : Nat := 118140960795 + 3779288 * 2 ^ 59
def prefixEnd_3779288 : Nat := 4983230072969 + 3 ^ 40 * 3779288 * 2
def baseEnd_3779288 : Nat := 646863758589771584006459

theorem tailTrace_3779288 : CollatzResearch.WordTrace tailWord_3779288 prefixEnd_3779288 646863758589771584006459 := by
  unfold tailWord_3779288
  simp only [CollatzResearch.WordTrace]
  refine ⟨68920978766146250924265259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91894638354861667899020345 68920978766146250924265259)
  ·
    refine ⟨103381468149219376386397889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68920978766146250924265259 103381468149219376386397889)
    ·
      refine ⟨77536101111914532289798417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103381468149219376386397889 77536101111914532289798417)
      ·
        refine ⟨58152075833935899217348813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77536101111914532289798417 58152075833935899217348813)
        ·
          refine ⟨21807028437725962206505805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58152075833935899217348813 21807028437725962206505805)
          ·
            refine ⟨8177635664147235827439677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21807028437725962206505805 8177635664147235827439677)
            ·
              refine ⟨3066613374055213435289879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8177635664147235827439677 3066613374055213435289879)
              ·
                refine ⟨4599920061082820152934819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3066613374055213435289879 4599920061082820152934819)
                ·
                  refine ⟨6899880091624230229402229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4599920061082820152934819 6899880091624230229402229)
                  ·
                    refine ⟨646863758589771584006459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6899880091624230229402229 646863758589771584006459)
                    ·
                      rfl

theorem cell23_3779288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 1, 5].length) (baseStart_3779288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779288 prefixEnd_3779288 := by exact prefixLift 3779288
  have htrace : WordTrace (prefixWord ++ tailWord_3779288) baseStart_3779288 baseEnd_3779288 := by
    simpa [prefixWord, tailWord_3779288, baseEnd_3779288] using wordTrace_append hprefix tailTrace_3779288
  have hstable : (prefixWord ++ tailWord_3779288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779288).length < 2 ^ (prefixWord ++ tailWord_3779288).sum := by decide
  have hdescent : baseEnd_3779288 < baseStart_3779288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779308 : List Nat := [2, 2, 1, 1, 2, 2, 1, 5, 3, 2, 2]
def baseStart_3779308 : Nat := 118140960795 + 3779308 * 2 ^ 59
def prefixEnd_3779308 : Nat := 4983230072969 + 3 ^ 40 * 3779308 * 2
def baseEnd_3779308 : Nat := 1940601545382404673769285

theorem tailTrace_3779308 : CollatzResearch.WordTrace tailWord_3779308 prefixEnd_3779308 1940601545382404673769285 := by
  unfold tailWord_3779308
  simp only [CollatzResearch.WordTrace]
  refine ⟨68921343496110022632129289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91895124661480030176172385 68921343496110022632129289)
  ·
    refine ⟨51691007622082516974096967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68921343496110022632129289 51691007622082516974096967)
    ·
      refine ⟨77536511433123775461145451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51691007622082516974096967 77536511433123775461145451)
      ·
        refine ⟨116304767149685663191718177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77536511433123775461145451 116304767149685663191718177)
        ·
          refine ⟨87228575362264247393788633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116304767149685663191718177 87228575362264247393788633)
          ·
            refine ⟨65421431521698185545341475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87228575362264247393788633 65421431521698185545341475)
            ·
              refine ⟨98132147282547278318012213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65421431521698185545341475 98132147282547278318012213)
              ·
                refine ⟨9199888807738807342313645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98132147282547278318012213 9199888807738807342313645)
                ·
                  refine ⟨3449958302902052753367617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9199888807738807342313645 3449958302902052753367617)
                  ·
                    refine ⟨2587468727176539565025713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3449958302902052753367617 2587468727176539565025713)
                    ·
                      refine ⟨1940601545382404673769285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2587468727176539565025713 1940601545382404673769285)
                      ·
                        rfl

theorem cell23_3779308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 2, 2].length) (baseStart_3779308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779308 prefixEnd_3779308 := by exact prefixLift 3779308
  have htrace : WordTrace (prefixWord ++ tailWord_3779308) baseStart_3779308 baseEnd_3779308 := by
    simpa [prefixWord, tailWord_3779308, baseEnd_3779308] using wordTrace_append hprefix tailTrace_3779308
  have hstable : (prefixWord ++ tailWord_3779308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779308).length < 2 ^ (prefixWord ++ tailWord_3779308).sum := by decide
  have hdescent : baseEnd_3779308 < baseStart_3779308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779311 : List Nat := [1, 1, 2, 1, 5, 2, 1, 2, 3, 2, 3]
def baseStart_3779311 : Nat := 118140960795 + 3779311 * 2 ^ 59
def prefixEnd_3779311 : Nat := 4983230072969 + 3 ^ 40 * 3779311 * 2
def baseEnd_3779311 : Nat := 1940603085824368162031771

theorem tailTrace_3779311 : CollatzResearch.WordTrace tailWord_3779311 prefixEnd_3779311 1940603085824368162031771 := by
  unfold tailWord_3779311
  simp only [CollatzResearch.WordTrace]
  refine ⟨137842796411209176776617787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91895197607472784517745191 137842796411209176776617787)
  ·
    refine ⟨206764194616813765164926681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137842796411209176776617787 206764194616813765164926681)
    ·
      refine ⟨155073145962610323873695011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206764194616813765164926681 155073145962610323873695011)
      ·
        refine ⟨232609718943915485810542517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155073145962610323873695011 232609718943915485810542517)
        ·
          refine ⟨21807161150992076794738361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 232609718943915485810542517 21807161150992076794738361)
          ·
            refine ⟨16355370863244057596053771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21807161150992076794738361 16355370863244057596053771)
            ·
              refine ⟨24533056294866086394080657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16355370863244057596053771 24533056294866086394080657)
              ·
                refine ⟨18399792221149564795560493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24533056294866086394080657 18399792221149564795560493)
                ·
                  refine ⟨6899922082931086798335185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18399792221149564795560493 6899922082931086798335185)
                  ·
                    refine ⟨5174941562198315098751389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6899922082931086798335185 5174941562198315098751389)
                    ·
                      refine ⟨1940603085824368162031771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5174941562198315098751389 1940603085824368162031771)
                      ·
                        rfl

theorem cell23_3779311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 2, 3].length) (baseStart_3779311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779311 prefixEnd_3779311 := by exact prefixLift 3779311
  have htrace : WordTrace (prefixWord ++ tailWord_3779311) baseStart_3779311 baseEnd_3779311 := by
    simpa [prefixWord, tailWord_3779311, baseEnd_3779311] using wordTrace_append hprefix tailTrace_3779311
  have hstable : (prefixWord ++ tailWord_3779311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779311).length < 2 ^ (prefixWord ++ tailWord_3779311).sum := by decide
  have hdescent : baseEnd_3779311 < baseStart_3779311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779318 : List Nat := [5, 1, 1, 1, 1, 2, 1, 5, 2, 4]
def baseStart_3779318 : Nat := 118140960795 + 3779318 * 2 ^ 59
def prefixEnd_3779318 : Nat := 4983230072969 + 3 ^ 40 * 3779318 * 2
def baseEnd_3779318 : Nat := 646868893396316544881413

theorem tailTrace_3779318 : CollatzResearch.WordTrace tailWord_3779318 prefixEnd_3779318 646868893396316544881413 := by
  unfold tailWord_3779318
  simp only [CollatzResearch.WordTrace]
  refine ⟨8615190732636488560757663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91895367814789211314748405 8615190732636488560757663)
  ·
    refine ⟨12922786098954732841136495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8615190732636488560757663 12922786098954732841136495)
    ·
      refine ⟨19384179148432099261704743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12922786098954732841136495 19384179148432099261704743)
      ·
        refine ⟨29076268722648148892557115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19384179148432099261704743 29076268722648148892557115)
        ·
          refine ⟨43614403083972223338835673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29076268722648148892557115 43614403083972223338835673)
          ·
            refine ⟨32710802312979167504126755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43614403083972223338835673 32710802312979167504126755)
            ·
              refine ⟨49066203469468751256190133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32710802312979167504126755 49066203469468751256190133)
              ·
                refine ⟨4599956575262695430267825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49066203469468751256190133 4599956575262695430267825)
                ·
                  refine ⟨3449967431447021572700869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4599956575262695430267825 3449967431447021572700869)
                  ·
                    refine ⟨646868893396316544881413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3449967431447021572700869 646868893396316544881413)
                    ·
                      rfl

theorem cell23_3779318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_3779318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779318 prefixEnd_3779318 := by exact prefixLift 3779318
  have htrace : WordTrace (prefixWord ++ tailWord_3779318) baseStart_3779318 baseEnd_3779318 := by
    simpa [prefixWord, tailWord_3779318, baseEnd_3779318] using wordTrace_append hprefix tailTrace_3779318
  have hstable : (prefixWord ++ tailWord_3779318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779318).length < 2 ^ (prefixWord ++ tailWord_3779318).sum := by decide
  have hdescent : baseEnd_3779318 < baseStart_3779318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779382 : List Nat := [5, 1, 2, 2, 3, 1, 2, 7]
def baseStart_3779382 : Nat := 118140960795 + 3779382 * 2 ^ 59
def prefixEnd_3779382 : Nat := 4983230072969 + 3 ^ 40 * 3779382 * 2
def baseEnd_3779382 : Nat := 71875538627808792009035

theorem tailTrace_3779382 : CollatzResearch.WordTrace tailWord_3779382 prefixEnd_3779382 71875538627808792009035 := by
  unfold tailWord_3779382
  simp only [CollatzResearch.WordTrace]
  refine ⟨8615336624621997243903275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91896923995967970601634933 8615336624621997243903275)
  ·
    refine ⟨12923004936932995865854913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8615336624621997243903275 12923004936932995865854913)
    ·
      refine ⟨9692253702699746899391185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12923004936932995865854913 9692253702699746899391185)
      ·
        refine ⟨7269190277024810174543389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9692253702699746899391185 7269190277024810174543389)
        ·
          refine ⟨2725946353884303815453771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7269190277024810174543389 2725946353884303815453771)
          ·
            refine ⟨4088919530826455723180657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2725946353884303815453771 4088919530826455723180657)
            ·
              refine ⟨3066689648119841792385493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4088919530826455723180657 3066689648119841792385493)
              ·
                refine ⟨71875538627808792009035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3066689648119841792385493 71875538627808792009035)
                ·
                  rfl

theorem cell23_3779382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 7].length) (baseStart_3779382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779382 prefixEnd_3779382 := by exact prefixLift 3779382
  have htrace : WordTrace (prefixWord ++ tailWord_3779382) baseStart_3779382 baseEnd_3779382 := by
    simpa [prefixWord, tailWord_3779382, baseEnd_3779382] using wordTrace_append hprefix tailTrace_3779382
  have hstable : (prefixWord ++ tailWord_3779382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779382).length < 2 ^ (prefixWord ++ tailWord_3779382).sum := by decide
  have hdescent : baseEnd_3779382 < baseStart_3779382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779393 : List Nat := [1, 2, 5, 3, 2, 1, 1, 3, 1, 2, 2]
def baseStart_3779393 : Nat := 118140960795 + 3779393 * 2 ^ 59
def prefixEnd_3779393 : Nat := 4983230072969 + 3 ^ 40 * 3779393 * 2
def baseEnd_3779393 : Nat := 1940645191238036841206395

theorem tailTrace_3779393 : CollatzResearch.WordTrace tailWord_3779393 prefixEnd_3779393 1940645191238036841206395 := by
  unfold tailWord_3779393
  simp only [CollatzResearch.WordTrace]
  refine ⟨137845787196912104781102833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91897191464608069854068555 137845787196912104781102833)
  ·
    refine ⟨103384340397684078585827125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137845787196912104781102833 103384340397684078585827125)
    ·
      refine ⟨9692281912282882367421293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103384340397684078585827125 9692281912282882367421293)
      ·
        refine ⟨3634605717106080887782985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9692281912282882367421293 3634605717106080887782985)
        ·
          refine ⟨2725954287829560665837239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3634605717106080887782985 2725954287829560665837239)
          ·
            refine ⟨4088931431744340998755859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2725954287829560665837239 4088931431744340998755859)
            ·
              refine ⟨6133397147616511498133789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4088931431744340998755859 6133397147616511498133789)
              ·
                refine ⟨2300023930356191811800171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6133397147616511498133789 2300023930356191811800171)
                ·
                  refine ⟨3450035895534287717700257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2300023930356191811800171 3450035895534287717700257)
                  ·
                    refine ⟨2587526921650715788275193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3450035895534287717700257 2587526921650715788275193)
                    ·
                      refine ⟨1940645191238036841206395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2587526921650715788275193 1940645191238036841206395)
                      ·
                        rfl

theorem cell23_3779393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_3779393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779393 prefixEnd_3779393 := by exact prefixLift 3779393
  have htrace : WordTrace (prefixWord ++ tailWord_3779393) baseStart_3779393 baseEnd_3779393 := by
    simpa [prefixWord, tailWord_3779393, baseEnd_3779393] using wordTrace_append hprefix tailTrace_3779393
  have hstable : (prefixWord ++ tailWord_3779393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779393).length < 2 ^ (prefixWord ++ tailWord_3779393).sum := by decide
  have hdescent : baseEnd_3779393 < baseStart_3779393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779401 : List Nat := [1, 2, 1, 1, 2, 6, 1, 1, 2, 1, 5]
def baseStart_3779401 : Nat := 118140960795 + 3779401 * 2 ^ 59
def prefixEnd_3779401 : Nat := 4983230072969 + 3 ^ 40 * 3779401 * 2
def baseEnd_3779401 : Nat := 1940649299083272809906357

theorem tailTrace_3779401 : CollatzResearch.WordTrace tailWord_3779401 prefixEnd_3779401 1940649299083272809906357 := by
  unfold tailWord_3779401
  simp only [CollatzResearch.WordTrace]
  refine ⟨137846078980883122147394057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91897385987255414764929371 137846078980883122147394057)
  ·
    refine ⟨103384559235662341610545543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137846078980883122147394057 103384559235662341610545543)
    ·
      refine ⟨155076838853493512415818315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103384559235662341610545543 155076838853493512415818315)
      ·
        refine ⟨232615258280240268623727473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155076838853493512415818315 232615258280240268623727473)
        ·
          refine ⟨174461443710180201467795605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232615258280240268623727473 174461443710180201467795605)
          ·
            refine ⟨8177880173914696943802919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 174461443710180201467795605 8177880173914696943802919)
            ·
              refine ⟨12266820260872045415704379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8177880173914696943802919 12266820260872045415704379)
              ·
                refine ⟨18400230391308068123556569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12266820260872045415704379 18400230391308068123556569)
                ·
                  refine ⟨13800172793481051092667427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18400230391308068123556569 13800172793481051092667427)
                  ·
                    refine ⟨20700259190221576639001141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13800172793481051092667427 20700259190221576639001141)
                    ·
                      refine ⟨1940649299083272809906357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20700259190221576639001141 1940649299083272809906357)
                      ·
                        rfl

theorem cell23_3779401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 1, 5].length) (baseStart_3779401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779401 prefixEnd_3779401 := by exact prefixLift 3779401
  have htrace : WordTrace (prefixWord ++ tailWord_3779401) baseStart_3779401 baseEnd_3779401 := by
    simpa [prefixWord, tailWord_3779401, baseEnd_3779401] using wordTrace_append hprefix tailTrace_3779401
  have hstable : (prefixWord ++ tailWord_3779401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779401).length < 2 ^ (prefixWord ++ tailWord_3779401).sum := by decide
  have hdescent : baseEnd_3779401 < baseStart_3779401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779415 : List Nat := [1, 1, 3, 2, 4, 1, 2, 1, 4, 2, 2]
def baseStart_3779415 : Nat := 118140960795 + 3779415 * 2 ^ 59
def prefixEnd_3779415 : Nat := 4983230072969 + 3 ^ 40 * 3779415 * 2
def baseEnd_3779415 : Nat := 1940656487812435755131293

theorem tailTrace_3779415 : CollatzResearch.WordTrace tailWord_3779415 prefixEnd_3779415 1940656487812435755131293 := by
  unfold tailWord_3779415
  simp only [CollatzResearch.WordTrace]
  refine ⟨137846589602832402538403699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91897726401888268358935799 137846589602832402538403699)
  ·
    refine ⟨206769884404248603807605549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137846589602832402538403699 206769884404248603807605549)
    ·
      refine ⟨77538706651593226427852081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206769884404248603807605549 77538706651593226427852081)
      ·
        refine ⟨58154029988694919820889061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77538706651593226427852081 58154029988694919820889061)
        ·
          refine ⟨10903880622880297466416699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58154029988694919820889061 10903880622880297466416699)
          ·
            refine ⟨16355820934320446199625049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10903880622880297466416699 16355820934320446199625049)
            ·
              refine ⟨12266865700740334649718787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16355820934320446199625049 12266865700740334649718787)
              ·
                refine ⟨18400298551110501974578181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12266865700740334649718787 18400298551110501974578181)
                ·
                  refine ⟨3450055978333219120233409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18400298551110501974578181 3450055978333219120233409)
                  ·
                    refine ⟨2587541983749914340175057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3450055978333219120233409 2587541983749914340175057)
                    ·
                      refine ⟨1940656487812435755131293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2587541983749914340175057 1940656487812435755131293)
                      ·
                        rfl

theorem cell23_3779415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 4, 2, 2].length) (baseStart_3779415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779415 prefixEnd_3779415 := by exact prefixLift 3779415
  have htrace : WordTrace (prefixWord ++ tailWord_3779415) baseStart_3779415 baseEnd_3779415 := by
    simpa [prefixWord, tailWord_3779415, baseEnd_3779415] using wordTrace_append hprefix tailTrace_3779415
  have hstable : (prefixWord ++ tailWord_3779415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779415).length < 2 ^ (prefixWord ++ tailWord_3779415).sum := by decide
  have hdescent : baseEnd_3779415 < baseStart_3779415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779426 : List Nat := [3, 3, 2, 1, 4, 1, 2, 1, 2, 1, 3]
def baseStart_3779426 : Nat := 118140960795 + 3779426 * 2 ^ 59
def prefixEnd_3779426 : Nat := 4983230072969 + 3 ^ 40 * 3779426 * 2
def baseEnd_3779426 : Nat := 1940662136099635212093743

theorem tailTrace_3779426 : CollatzResearch.WordTrace tailWord_3779426 prefixEnd_3779426 1940662136099635212093743 := by
  unfold tailWord_3779426
  simp only [CollatzResearch.WordTrace]
  refine ⟨34461747701448137854263533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91897993870528367611369421 34461747701448137854263533)
  ·
    refine ⟨12923155388043051695348825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34461747701448137854263533 12923155388043051695348825)
    ·
      refine ⟨9692366541032288771511619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12923155388043051695348825 9692366541032288771511619)
      ·
        refine ⟨14538549811548433157267429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9692366541032288771511619 14538549811548433157267429)
        ·
          refine ⟨2725978089665331216987643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14538549811548433157267429 2725978089665331216987643)
          ·
            refine ⟨4088967134497996825481465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2725978089665331216987643 4088967134497996825481465)
            ·
              refine ⟨3066725350873497619111099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4088967134497996825481465 3066725350873497619111099)
              ·
                refine ⟨4600088026310246428666649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3066725350873497619111099 4600088026310246428666649)
                ·
                  refine ⟨3450066019732684821499987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4600088026310246428666649 3450066019732684821499987)
                  ·
                    refine ⟨5175099029599027232249981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3450066019732684821499987 5175099029599027232249981)
                    ·
                      refine ⟨1940662136099635212093743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5175099029599027232249981 1940662136099635212093743)
                      ·
                        rfl

theorem cell23_3779426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_3779426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779426 prefixEnd_3779426 := by exact prefixLift 3779426
  have htrace : WordTrace (prefixWord ++ tailWord_3779426) baseStart_3779426 baseEnd_3779426 := by
    simpa [prefixWord, tailWord_3779426, baseEnd_3779426] using wordTrace_append hprefix tailTrace_3779426
  have hstable : (prefixWord ++ tailWord_3779426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779426).length < 2 ^ (prefixWord ++ tailWord_3779426).sum := by decide
  have hdescent : baseEnd_3779426 < baseStart_3779426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779432 : List Nat := [2, 1, 4, 2, 1, 3, 1, 3, 2, 2, 2]
def baseStart_3779432 : Nat := 118140960795 + 3779432 * 2 ^ 59
def prefixEnd_3779432 : Nat := 4983230072969 + 3 ^ 40 * 3779432 * 2
def baseEnd_3779432 : Nat := 1940665216983562188618715

theorem tailTrace_3779432 : CollatzResearch.WordTrace tailWord_3779432 prefixEnd_3779432 1940665216983562188618715 := by
  unfold tailWord_3779432
  simp only [CollatzResearch.WordTrace]
  refine ⟨68923604821885407220886275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91898139762513876294515033 68923604821885407220886275)
  ·
    refine ⟨103385407232828110831329413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68923604821885407220886275 103385407232828110831329413)
    ·
      refine ⟨19384763856155270780874265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103385407232828110831329413 19384763856155270780874265)
      ·
        refine ⟨14538572892116453085655699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19384763856155270780874265 14538572892116453085655699)
        ·
          refine ⟨21807859338174679628483549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14538572892116453085655699 21807859338174679628483549)
          ·
            refine ⟨8177947251815504860681331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21807859338174679628483549 8177947251815504860681331)
            ·
              refine ⟨12266920877723257291021997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8177947251815504860681331 12266920877723257291021997)
              ·
                refine ⟨4600095329146221484133249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12266920877723257291021997 4600095329146221484133249)
                ·
                  refine ⟨3450071496859666113099937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4600095329146221484133249 3450071496859666113099937)
                  ·
                    refine ⟨2587553622644749584824953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3450071496859666113099937 2587553622644749584824953)
                    ·
                      refine ⟨1940665216983562188618715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2587553622644749584824953 1940665216983562188618715)
                      ·
                        rfl

theorem cell23_3779432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_3779432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779432 prefixEnd_3779432 := by exact prefixLift 3779432
  have htrace : WordTrace (prefixWord ++ tailWord_3779432) baseStart_3779432 baseEnd_3779432 := by
    simpa [prefixWord, tailWord_3779432, baseEnd_3779432] using wordTrace_append hprefix tailTrace_3779432
  have hstable : (prefixWord ++ tailWord_3779432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779432).length < 2 ^ (prefixWord ++ tailWord_3779432).sum := by decide
  have hdescent : baseEnd_3779432 < baseStart_3779432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779451 : List Nat := [1, 1, 1, 1, 1, 5, 3, 3, 2, 5]
def baseStart_3779451 : Nat := 118140960795 + 3779451 * 2 ^ 59
def prefixEnd_3779451 : Nat := 4983230072969 + 3 ^ 40 * 3779451 * 2
def baseEnd_3779451 : Nat := 646891657705332538093709

theorem tailTrace_3779451 : CollatzResearch.WordTrace tailWord_3779451 prefixEnd_3779451 646891657705332538093709 := by
  unfold tailWord_3779451
  simp only [CollatzResearch.WordTrace]
  refine ⟨137847902630701980686714207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91898601753801320457809471 137847902630701980686714207)
  ·
    refine ⟨206771853946052971030071311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137847902630701980686714207 206771853946052971030071311)
    ·
      refine ⟨310157780919079456545106967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206771853946052971030071311 310157780919079456545106967)
      ·
        refine ⟨465236671378619184817660451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310157780919079456545106967 465236671378619184817660451)
        ·
          refine ⟨697855007067928777226490677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465236671378619184817660451 697855007067928777226490677)
          ·
            refine ⟨65423906912618322864983501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 697855007067928777226490677 65423906912618322864983501)
            ·
              refine ⟨24533965092231871074368813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65423906912618322864983501 24533965092231871074368813)
              ·
                refine ⟨9200236909586951652888305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24533965092231871074368813 9200236909586951652888305)
                ·
                  refine ⟨6900177682190213739666229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9200236909586951652888305 6900177682190213739666229)
                  ·
                    refine ⟨646891657705332538093709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6900177682190213739666229 646891657705332538093709)
                    ·
                      rfl

theorem cell23_3779451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 5].length) (baseStart_3779451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779451 prefixEnd_3779451 := by exact prefixLift 3779451
  have htrace : WordTrace (prefixWord ++ tailWord_3779451) baseStart_3779451 baseEnd_3779451 := by
    simpa [prefixWord, tailWord_3779451, baseEnd_3779451] using wordTrace_append hprefix tailTrace_3779451
  have hstable : (prefixWord ++ tailWord_3779451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779451).length < 2 ^ (prefixWord ++ tailWord_3779451).sum := by decide
  have hdescent : baseEnd_3779451 < baseStart_3779451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779461 : List Nat := [1, 3, 1, 1, 3, 3, 1, 2, 1, 2, 5]
def baseStart_3779461 : Nat := 118140960795 + 3779461 * 2 ^ 59
def prefixEnd_3779461 : Nat := 4983230072969 + 3 ^ 40 * 3779461 * 2
def baseEnd_3779461 : Nat := 1940680107922542575156081

theorem tailTrace_3779461 : CollatzResearch.WordTrace tailWord_3779461 prefixEnd_3779461 1940680107922542575156081 := by
  unfold tailWord_3779461
  simp only [CollatzResearch.WordTrace]
  refine ⟨137848267360665752394578237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91898844907110501596385491 137848267360665752394578237)
  ·
    refine ⟨51693100260249657147966839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137848267360665752394578237 51693100260249657147966839)
    ·
      refine ⟨77539650390374485721950259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51693100260249657147966839 77539650390374485721950259)
      ·
        refine ⟨116309475585561728582925389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77539650390374485721950259 116309475585561728582925389)
        ·
          refine ⟨43616053344585648218597021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116309475585561728582925389 43616053344585648218597021)
          ·
            refine ⟨16356020004219618081973883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43616053344585648218597021 16356020004219618081973883)
            ·
              refine ⟨24534030006329427122960825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16356020004219618081973883 24534030006329427122960825)
              ·
                refine ⟨18400522504747070342220619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24534030006329427122960825 18400522504747070342220619)
                ·
                  refine ⟨27600783757120605513330929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18400522504747070342220619 27600783757120605513330929)
                  ·
                    refine ⟨20700587817840454134998197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27600783757120605513330929 20700587817840454134998197)
                    ·
                      refine ⟨1940680107922542575156081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20700587817840454134998197 1940680107922542575156081)
                      ·
                        rfl

theorem cell23_3779461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_3779461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779461 prefixEnd_3779461 := by exact prefixLift 3779461
  have htrace : WordTrace (prefixWord ++ tailWord_3779461) baseStart_3779461 baseEnd_3779461 := by
    simpa [prefixWord, tailWord_3779461, baseEnd_3779461] using wordTrace_append hprefix tailTrace_3779461
  have hstable : (prefixWord ++ tailWord_3779461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779461).length < 2 ^ (prefixWord ++ tailWord_3779461).sum := by decide
  have hdescent : baseEnd_3779461 < baseStart_3779461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779488 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 1, 6, 2]
def baseStart_3779488 : Nat := 118140960795 + 3779488 * 2 ^ 59
def prefixEnd_3779488 : Nat := 4983230072969 + 3 ^ 40 * 3779488 * 2
def baseEnd_3779488 : Nat := 1940693971900213969518457

theorem tailTrace_3779488 : CollatzResearch.WordTrace tailWord_3779488 prefixEnd_3779488 1940693971900213969518457 := by
  unfold tailWord_3779488
  simp only [CollatzResearch.WordTrace]
  refine ⟨68924626065783968002905559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91899501421045290670540745 68924626065783968002905559)
  ·
    refine ⟨103386939098675952004358339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68924626065783968002905559 103386939098675952004358339)
    ·
      refine ⟨155080408648013928006537509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103386939098675952004358339 155080408648013928006537509)
      ·
        refine ⟨29077576621502611501225783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155080408648013928006537509 29077576621502611501225783)
        ·
          refine ⟨43616364932253917251838675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29077576621502611501225783 43616364932253917251838675)
          ·
            refine ⟨65424547398380875877758013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43616364932253917251838675 65424547398380875877758013)
            ·
              refine ⟨24534205274392828454159255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65424547398380875877758013 24534205274392828454159255)
              ·
                refine ⟨36801307911589242681238883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24534205274392828454159255 36801307911589242681238883)
                ·
                  refine ⟨55201961867383864021858325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36801307911589242681238883 55201961867383864021858325)
                  ·
                    refine ⟨2587591962533618626024609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55201961867383864021858325 2587591962533618626024609)
                    ·
                      refine ⟨1940693971900213969518457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2587591962533618626024609 1940693971900213969518457)
                      ·
                        rfl

theorem cell23_3779488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_3779488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779488 prefixEnd_3779488 := by exact prefixLift 3779488
  have htrace : WordTrace (prefixWord ++ tailWord_3779488) baseStart_3779488 baseEnd_3779488 := by
    simpa [prefixWord, tailWord_3779488, baseEnd_3779488] using wordTrace_append hprefix tailTrace_3779488
  have hstable : (prefixWord ++ tailWord_3779488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779488).length < 2 ^ (prefixWord ++ tailWord_3779488).sum := by decide
  have hdescent : baseEnd_3779488 < baseStart_3779488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779528 : List Nat := [2, 1, 3, 1, 5, 1, 1, 1, 8]
def baseStart_3779528 : Nat := 118140960795 + 3779528 * 2 ^ 59
def prefixEnd_3779528 : Nat := 4983230072969 + 3 ^ 40 * 3779528 * 2
def baseEnd_3779528 : Nat := 215634945680710423668697

theorem tailTrace_3779528 : CollatzResearch.WordTrace tailWord_3779528 prefixEnd_3779528 215634945680710423668697 := by
  unfold tailWord_3779528
  simp only [CollatzResearch.WordTrace]
  refine ⟨68925355525711511418633619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91900474034282015224844825 68925355525711511418633619)
  ·
    refine ⟨103388033288567267127950429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68925355525711511418633619 103388033288567267127950429)
    ·
      refine ⟨38770512483212725172981411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103388033288567267127950429 38770512483212725172981411)
      ·
        refine ⟨58155768724819087759472117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38770512483212725172981411 58155768724819087759472117)
        ·
          refine ⟨5452103317951789477450511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58155768724819087759472117 5452103317951789477450511)
          ·
            refine ⟨8178154976927684216175767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5452103317951789477450511 8178154976927684216175767)
            ·
              refine ⟨12267232465391526324263651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8178154976927684216175767 12267232465391526324263651)
              ·
                refine ⟨18400848698087289486395477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12267232465391526324263651 18400848698087289486395477)
                ·
                  refine ⟨215634945680710423668697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18400848698087289486395477 215634945680710423668697)
                  ·
                    rfl

theorem cell23_3779528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 8].length) (baseStart_3779528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779528 prefixEnd_3779528 := by exact prefixLift 3779528
  have htrace : WordTrace (prefixWord ++ tailWord_3779528) baseStart_3779528 baseEnd_3779528 := by
    simpa [prefixWord, tailWord_3779528, baseEnd_3779528] using wordTrace_append hprefix tailTrace_3779528
  have hstable : (prefixWord ++ tailWord_3779528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779528).length < 2 ^ (prefixWord ++ tailWord_3779528).sum := by decide
  have hdescent : baseEnd_3779528 < baseStart_3779528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779531 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 6]
def baseStart_3779531 : Nat := 118140960795 + 3779531 * 2 ^ 59
def prefixEnd_3779531 : Nat := 4983230072969 + 3 ^ 40 * 3779531 * 2
def baseEnd_3779531 : Nat := 1940716051568357301280759

theorem tailTrace_3779531 : CollatzResearch.WordTrace tailWord_3779531 prefixEnd_3779531 1940716051568357301280759 := by
  unfold tailWord_3779531
  simp only [CollatzResearch.WordTrace]
  refine ⟨137850820470412154349626447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91900546980274769566417631 137850820470412154349626447)
  ·
    refine ⟨206776230705618231524439671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137850820470412154349626447 206776230705618231524439671)
    ·
      refine ⟨310164346058427347286659507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206776230705618231524439671 310164346058427347286659507)
      ·
        refine ⟨465246519087641020929989261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310164346058427347286659507 465246519087641020929989261)
        ·
          refine ⟨174467444657865382848745973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 465246519087641020929989261 174467444657865382848745973)
          ·
            refine ⟨16356322936674879642069935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174467444657865382848745973 16356322936674879642069935)
            ·
              refine ⟨24534484405012319463104903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16356322936674879642069935 24534484405012319463104903)
              ·
                refine ⟨36801726607518479194657355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24534484405012319463104903 36801726607518479194657355)
                ·
                  refine ⟨55202589911277718791986033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36801726607518479194657355 55202589911277718791986033)
                  ·
                    refine ⟨41401942433458289093989525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55202589911277718791986033 41401942433458289093989525)
                    ·
                      refine ⟨1940716051568357301280759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41401942433458289093989525 1940716051568357301280759)
                      ·
                        rfl

theorem cell23_3779531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 6].length) (baseStart_3779531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779531 prefixEnd_3779531 := by exact prefixLift 3779531
  have htrace : WordTrace (prefixWord ++ tailWord_3779531) baseStart_3779531 baseEnd_3779531 := by
    simpa [prefixWord, tailWord_3779531, baseEnd_3779531] using wordTrace_append hprefix tailTrace_3779531
  have hstable : (prefixWord ++ tailWord_3779531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779531).length < 2 ^ (prefixWord ++ tailWord_3779531).sum := by decide
  have hdescent : baseEnd_3779531 < baseStart_3779531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779545 : List Nat := [1, 2, 1, 2, 5, 2, 3, 1, 6]
def baseStart_3779545 : Nat := 118140960795 + 3779545 * 2 ^ 59
def prefixEnd_3779545 : Nat := 4983230072969 + 3 ^ 40 * 3779545 * 2
def baseEnd_3779545 : Nat := 215635915588613360722855

theorem tailTrace_3779545 : CollatzResearch.WordTrace tailWord_3779545 prefixEnd_3779545 215635915588613360722855 := by
  unfold tailWord_3779545
  simp only [CollatzResearch.WordTrace]
  refine ⟨137851331092361434740636089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91900887394907623160424059 137851331092361434740636089)
  ·
    refine ⟨103388498319271076055477067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137851331092361434740636089 103388498319271076055477067)
    ·
      refine ⟨155082747478906614083215601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103388498319271076055477067 155082747478906614083215601)
      ·
        refine ⟨116312060609179960562411701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155082747478906614083215601 116312060609179960562411701)
        ·
          refine ⟨10904255682110621302726097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116312060609179960562411701 10904255682110621302726097)
          ·
            refine ⟨8178191761582965977044573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10904255682110621302726097 8178191761582965977044573)
            ·
              refine ⟨3066821910593612241391715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8178191761582965977044573 3066821910593612241391715)
              ·
                refine ⟨4600232865890418362087573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3066821910593612241391715 4600232865890418362087573)
                ·
                  refine ⟨215635915588613360722855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4600232865890418362087573 215635915588613360722855)
                  ·
                    rfl

theorem cell23_3779545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 6].length) (baseStart_3779545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779545 prefixEnd_3779545 := by exact prefixLift 3779545
  have htrace : WordTrace (prefixWord ++ tailWord_3779545) baseStart_3779545 baseEnd_3779545 := by
    simpa [prefixWord, tailWord_3779545, baseEnd_3779545] using wordTrace_append hprefix tailTrace_3779545
  have hstable : (prefixWord ++ tailWord_3779545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779545).length < 2 ^ (prefixWord ++ tailWord_3779545).sum := by decide
  have hdescent : baseEnd_3779545 < baseStart_3779545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779555 : List Nat := [1, 1, 1, 6, 1, 1, 1, 4, 3, 1, 3]
def baseStart_3779555 : Nat := 118140960795 + 3779555 * 2 ^ 59
def prefixEnd_3779555 : Nat := 4983230072969 + 3 ^ 40 * 3779555 * 2
def baseEnd_3779555 : Nat := 1940728375104065207380649

theorem tailTrace_3779555 : CollatzResearch.WordTrace tailWord_3779555 prefixEnd_3779555 1940728375104065207380649 := by
  unfold tailWord_3779555
  simp only [CollatzResearch.WordTrace]
  refine ⟨137851695822325206448500119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91901130548216804299000079 137851695822325206448500119)
  ·
    refine ⟨206777543733487809672750179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137851695822325206448500119 206777543733487809672750179)
    ·
      refine ⟨310166315600231714509125269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206777543733487809672750179 310166315600231714509125269)
      ·
        refine ⟨14539046043760861617615247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 310166315600231714509125269 14539046043760861617615247)
        ·
          refine ⟨21808569065641292426422871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14539046043760861617615247 21808569065641292426422871)
          ·
            refine ⟨32712853598461938639634307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21808569065641292426422871 32712853598461938639634307)
            ·
              refine ⟨49069280397692907959451461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32712853598461938639634307 49069280397692907959451461)
              ·
                refine ⟨9200490074567420242397149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49069280397692907959451461 9200490074567420242397149)
                ·
                  refine ⟨3450183777962782590898931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9200490074567420242397149 3450183777962782590898931)
                  ·
                    refine ⟨5175275666944173886348397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3450183777962782590898931 5175275666944173886348397)
                    ·
                      refine ⟨1940728375104065207380649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5175275666944173886348397 1940728375104065207380649)
                      ·
                        rfl

theorem cell23_3779555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_3779555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779555 prefixEnd_3779555 := by exact prefixLift 3779555
  have htrace : WordTrace (prefixWord ++ tailWord_3779555) baseStart_3779555 baseEnd_3779555 := by
    simpa [prefixWord, tailWord_3779555, baseEnd_3779555] using wordTrace_append hprefix tailTrace_3779555
  have hstable : (prefixWord ++ tailWord_3779555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779555).length < 2 ^ (prefixWord ++ tailWord_3779555).sum := by decide
  have hdescent : baseEnd_3779555 < baseStart_3779555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779561 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 4, 5, 4]
def baseStart_3779561 : Nat := 118140960795 + 3779561 * 2 ^ 59
def prefixEnd_3779561 : Nat := 4983230072969 + 3 ^ 40 * 3779561 * 2
def baseEnd_3779561 : Nat := 1940731455987992183905621

theorem tailTrace_3779561 : CollatzResearch.WordTrace tailWord_3779561 prefixEnd_3779561 1940731455987992183905621 := by
  unfold tailWord_3779561
  simp only [CollatzResearch.WordTrace]
  refine ⟨137851914660303469473218537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91901276440202312982145691 137851914660303469473218537)
  ·
    refine ⟨103388935995227602104913903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137851914660303469473218537 103388935995227602104913903)
    ·
      refine ⟨155083403992841403157370855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103388935995227602104913903 155083403992841403157370855)
      ·
        refine ⟨232625105989262104736056283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155083403992841403157370855 232625105989262104736056283)
        ·
          refine ⟨348937658983893157104084425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232625105989262104736056283 348937658983893157104084425)
          ·
            refine ⟨261703244237919867828063319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348937658983893157104084425 261703244237919867828063319)
            ·
              refine ⟨392554866356879801742094979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261703244237919867828063319 392554866356879801742094979)
              ·
                refine ⟨588832299535319702613142469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392554866356879801742094979 588832299535319702613142469)
                ·
                  refine ⟨110406056162872444239964213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 588832299535319702613142469 110406056162872444239964213)
                  ·
                    refine ⟨10350567765269291647496645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110406056162872444239964213 10350567765269291647496645)
                    ·
                      refine ⟨1940731455987992183905621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10350567765269291647496645 1940731455987992183905621)
                      ·
                        rfl

theorem cell23_3779561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 5, 4].length) (baseStart_3779561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779561 prefixEnd_3779561 := by exact prefixLift 3779561
  have htrace : WordTrace (prefixWord ++ tailWord_3779561) baseStart_3779561 baseEnd_3779561 := by
    simpa [prefixWord, tailWord_3779561, baseEnd_3779561] using wordTrace_append hprefix tailTrace_3779561
  have hstable : (prefixWord ++ tailWord_3779561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779561).length < 2 ^ (prefixWord ++ tailWord_3779561).sum := by decide
  have hdescent : baseEnd_3779561 < baseStart_3779561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779566 : List Nat := [4, 1, 2, 1, 5, 1, 1, 3, 1, 4]
def baseStart_3779566 : Nat := 118140960795 + 3779566 * 2 ^ 59
def prefixEnd_3779566 : Nat := 4983230072969 + 3 ^ 40 * 3779566 * 2
def baseEnd_3779566 : Nat := 646911341130421554781033

theorem tailTrace_3779566 : CollatzResearch.WordTrace tailWord_3779566 prefixEnd_3779566 646911341130421554781033 := by
  unfold tailWord_3779566
  simp only [CollatzResearch.WordTrace]
  refine ⟨17231512128160669415893819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91901398016856903551433701 17231512128160669415893819)
  ·
    refine ⟨25847268192241004123840729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17231512128160669415893819 25847268192241004123840729)
    ·
      refine ⟨19385451144180753092880547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25847268192241004123840729 19385451144180753092880547)
      ·
        refine ⟨29078176716271129639320821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19385451144180753092880547 29078176716271129639320821)
        ·
          refine ⟨2726079067150418403686327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29078176716271129639320821 2726079067150418403686327)
          ·
            refine ⟨4089118600725627605529491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2726079067150418403686327 4089118600725627605529491)
            ·
              refine ⟨6133677901088441408294237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4089118600725627605529491 6133677901088441408294237)
              ·
                refine ⟨2300129212908165528110339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6133677901088441408294237 2300129212908165528110339)
                ·
                  refine ⟨3450193819362248292165509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2300129212908165528110339 3450193819362248292165509)
                  ·
                    refine ⟨646911341130421554781033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3450193819362248292165509 646911341130421554781033)
                    ·
                      rfl

theorem cell23_3779566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_3779566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779566 prefixEnd_3779566 := by exact prefixLift 3779566
  have htrace : WordTrace (prefixWord ++ tailWord_3779566) baseStart_3779566 baseEnd_3779566 := by
    simpa [prefixWord, tailWord_3779566, baseEnd_3779566] using wordTrace_append hprefix tailTrace_3779566
  have hstable : (prefixWord ++ tailWord_3779566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779566).length < 2 ^ (prefixWord ++ tailWord_3779566).sum := by decide
  have hdescent : baseEnd_3779566 < baseStart_3779566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779589 : List Nat := [1, 3, 1, 1, 2, 3, 5, 2, 1, 1, 3]
def baseStart_3779589 : Nat := 118140960795 + 3779589 * 2 ^ 59
def prefixEnd_3779589 : Nat := 4983230072969 + 3 ^ 40 * 3779589 * 2
def baseEnd_3779589 : Nat := 1940745833446318074355493

theorem tailTrace_3779589 : CollatzResearch.WordTrace tailWord_3779589 prefixEnd_3779589 1940745833446318074355493 := by
  unfold tailWord_3779589
  simp only [CollatzResearch.WordTrace]
  refine ⟨137852935904202030255237821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91901957269468020170158547 137852935904202030255237821)
  ·
    refine ⟨51694850964075761345714183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137852935904202030255237821 51694850964075761345714183)
    ·
      refine ⟨77542276446113642018571275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51694850964075761345714183 77542276446113642018571275)
      ·
        refine ⟨116313414669170463027856913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77542276446113642018571275 116313414669170463027856913)
        ·
          refine ⟨87235061001877847270892685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116313414669170463027856913 87235061001877847270892685)
          ·
            refine ⟨32713147875704192726584757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87235061001877847270892685 32713147875704192726584757)
            ·
              refine ⟨3066857613347268068117321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32713147875704192726584757 3066857613347268068117321)
              ·
                refine ⟨2300143210010451051087991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3066857613347268068117321 2300143210010451051087991)
                ·
                  refine ⟨3450214815015676576631987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2300143210010451051087991 3450214815015676576631987)
                  ·
                    refine ⟨5175322222523514864947981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3450214815015676576631987 5175322222523514864947981)
                    ·
                      refine ⟨1940745833446318074355493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5175322222523514864947981 1940745833446318074355493)
                      ·
                        rfl

theorem cell23_3779589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 2, 1, 1, 3].length) (baseStart_3779589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779589 prefixEnd_3779589 := by exact prefixLift 3779589
  have htrace : WordTrace (prefixWord ++ tailWord_3779589) baseStart_3779589 baseEnd_3779589 := by
    simpa [prefixWord, tailWord_3779589, baseEnd_3779589] using wordTrace_append hprefix tailTrace_3779589
  have hstable : (prefixWord ++ tailWord_3779589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779589).length < 2 ^ (prefixWord ++ tailWord_3779589).sum := by decide
  have hdescent : baseEnd_3779589 < baseStart_3779589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779608 : List Nat := [2, 1, 2, 3, 2, 2, 2, 1, 1, 1, 6]
def baseStart_3779608 : Nat := 118140960795 + 3779608 * 2 ^ 59
def prefixEnd_3779608 : Nat := 4983230072969 + 3 ^ 40 * 3779608 * 2
def baseEnd_3779608 : Nat := 1940755589578753500017905

theorem tailTrace_3779608 : CollatzResearch.WordTrace tailWord_3779608 prefixEnd_3779608 1940755589578753500017905 := by
  unfold tailWord_3779608
  simp only [CollatzResearch.WordTrace]
  refine ⟨68926814445566598250089739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91902419260755464333452985 68926814445566598250089739)
  ·
    refine ⟨103390221668349897375134609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68926814445566598250089739 103390221668349897375134609)
    ·
      refine ⟨77542666251262423031350957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103390221668349897375134609 77542666251262423031350957)
      ·
        refine ⟨29078499844223408636756609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77542666251262423031350957 29078499844223408636756609)
        ·
          refine ⟨21808874883167556477567457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29078499844223408636756609 21808874883167556477567457)
          ·
            refine ⟨16356656162375667358175593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21808874883167556477567457 16356656162375667358175593)
            ·
              refine ⟨12267492121781750518631695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16356656162375667358175593 12267492121781750518631695)
              ·
                refine ⟨18401238182672625777947543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12267492121781750518631695 18401238182672625777947543)
                ·
                  refine ⟨27601857274008938666921315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18401238182672625777947543 27601857274008938666921315)
                  ·
                    refine ⟨41402785911013408000381973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27601857274008938666921315 41402785911013408000381973)
                    ·
                      refine ⟨1940755589578753500017905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41402785911013408000381973 1940755589578753500017905)
                      ·
                        rfl

theorem cell23_3779608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_3779608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779608 prefixEnd_3779608 := by exact prefixLift 3779608
  have htrace : WordTrace (prefixWord ++ tailWord_3779608) baseStart_3779608 baseEnd_3779608 := by
    simpa [prefixWord, tailWord_3779608, baseEnd_3779608] using wordTrace_append hprefix tailTrace_3779608
  have hstable : (prefixWord ++ tailWord_3779608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779608).length < 2 ^ (prefixWord ++ tailWord_3779608).sum := by decide
  have hdescent : baseEnd_3779608 < baseStart_3779608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779615 : List Nat := [1, 1, 2, 4, 1, 4, 1, 1, 3, 2, 3]
def baseStart_3779615 : Nat := 118140960795 + 3779615 * 2 ^ 59
def prefixEnd_3779615 : Nat := 4983230072969 + 3 ^ 40 * 3779615 * 2
def baseEnd_3779615 : Nat := 1940759183943334972630373

theorem tailTrace_3779615 : CollatzResearch.WordTrace tailWord_3779615 prefixEnd_3779615 1940759183943334972630373 := by
  unfold tailWord_3779615
  simp only [CollatzResearch.WordTrace]
  refine ⟨137853884202107836695684299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91902589468071891130456199 137853884202107836695684299)
  ·
    refine ⟨206780826303161755043526449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137853884202107836695684299 206780826303161755043526449)
    ·
      refine ⟨155085619727371316282644837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206780826303161755043526449 155085619727371316282644837)
      ·
        refine ⟨29078553698882121802995907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155085619727371316282644837 29078553698882121802995907)
        ·
          refine ⟨43617830548323182704493861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29078553698882121802995907 43617830548323182704493861)
          ·
            refine ⟨8178343227810596757092599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43617830548323182704493861 8178343227810596757092599)
            ·
              refine ⟨12267514841715895135638899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8178343227810596757092599 12267514841715895135638899)
              ·
                refine ⟨18401272262573842703458349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12267514841715895135638899 18401272262573842703458349)
                ·
                  refine ⟨6900477098465191013796881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18401272262573842703458349 6900477098465191013796881)
                  ·
                    refine ⟨5175357823848893260347661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6900477098465191013796881 5175357823848893260347661)
                    ·
                      refine ⟨1940759183943334972630373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5175357823848893260347661 1940759183943334972630373)
                      ·
                        rfl

theorem cell23_3779615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_3779615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779615 prefixEnd_3779615 := by exact prefixLift 3779615
  have htrace : WordTrace (prefixWord ++ tailWord_3779615) baseStart_3779615 baseEnd_3779615 := by
    simpa [prefixWord, tailWord_3779615, baseEnd_3779615] using wordTrace_append hprefix tailTrace_3779615
  have hstable : (prefixWord ++ tailWord_3779615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779615).length < 2 ^ (prefixWord ++ tailWord_3779615).sum := by decide
  have hdescent : baseEnd_3779615 < baseStart_3779615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779618 : List Nat := [3, 3, 1, 1, 1, 3, 2, 9]
def baseStart_3779618 : Nat := 118140960795 + 3779618 * 2 ^ 59
def prefixEnd_3779618 : Nat := 4983230072969 + 3 ^ 40 * 3779618 * 2
def baseEnd_3779618 : Nat := 71880026829085128181217

theorem tailTrace_3779618 : CollatzResearch.WordTrace tailWord_3779618 prefixEnd_3779618 71880026829085128181217 := by
  unfold tailWord_3779618
  simp only [CollatzResearch.WordTrace]
  refine ⟨34463498405274242052010877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91902662414064645472029005 34463498405274242052010877)
  ·
    refine ⟨12923811901977840769504079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34463498405274242052010877 12923811901977840769504079)
    ·
      refine ⟨19385717852966761154256119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12923811901977840769504079 19385717852966761154256119)
      ·
        refine ⟨29078576779450141731384179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19385717852966761154256119 29078576779450141731384179)
        ·
          refine ⟨43617865169175212597076269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29078576779450141731384179 43617865169175212597076269)
          ·
            refine ⟨16356699438440704723903601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43617865169175212597076269 16356699438440704723903601)
            ·
              refine ⟨12267524578830528542927701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16356699438440704723903601 12267524578830528542927701)
              ·
                refine ⟨71880026829085128181217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12267524578830528542927701 71880026829085128181217)
                ·
                  rfl

theorem cell23_3779618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 9].length) (baseStart_3779618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779618 prefixEnd_3779618 := by exact prefixLift 3779618
  have htrace : WordTrace (prefixWord ++ tailWord_3779618) baseStart_3779618 baseEnd_3779618 := by
    simpa [prefixWord, tailWord_3779618, baseEnd_3779618] using wordTrace_append hprefix tailTrace_3779618
  have hstable : (prefixWord ++ tailWord_3779618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779618).length < 2 ^ (prefixWord ++ tailWord_3779618).sum := by decide
  have hdescent : baseEnd_3779618 < baseStart_3779618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779632 : List Nat := [2, 1, 1, 1, 2, 4, 5, 1, 1, 2, 3]
def baseStart_3779632 : Nat := 118140960795 + 3779632 * 2 ^ 59
def prefixEnd_3779632 : Nat := 4983230072969 + 3 ^ 40 * 3779632 * 2
def baseEnd_3779632 : Nat := 1940767913114461406117795

theorem tailTrace_3779632 : CollatzResearch.WordTrace tailWord_3779632 prefixEnd_3779632 1940767913114461406117795 := by
  unfold tailWord_3779632
  simp only [CollatzResearch.WordTrace]
  refine ⟨68927252121523124299526575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91903002828697499066035433 68927252121523124299526575)
  ·
    refine ⟨103390878182284686449289863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68927252121523124299526575 103390878182284686449289863)
    ·
      refine ⟨155086317273427029673934795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103390878182284686449289863 155086317273427029673934795)
      ·
        refine ⟨232629475910140544510902193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155086317273427029673934795 232629475910140544510902193)
        ·
          refine ⟨174472106932605408383176645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232629475910140544510902193 174472106932605408383176645)
          ·
            refine ⟨32713520049863514071845621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174472106932605408383176645 32713520049863514071845621)
            ·
              refine ⟨3066892504674704444235527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32713520049863514071845621 3066892504674704444235527)
              ·
                refine ⟨4600338757012056666353291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3066892504674704444235527 4600338757012056666353291)
                ·
                  refine ⟨6900508135518084999529937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4600338757012056666353291 6900508135518084999529937)
                  ·
                    refine ⟨5175381101638563749647453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6900508135518084999529937 5175381101638563749647453)
                    ·
                      refine ⟨1940767913114461406117795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5175381101638563749647453 1940767913114461406117795)
                      ·
                        rfl

theorem cell23_3779632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 1, 2, 3].length) (baseStart_3779632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779632 prefixEnd_3779632 := by exact prefixLift 3779632
  have htrace : WordTrace (prefixWord ++ tailWord_3779632) baseStart_3779632 baseEnd_3779632 := by
    simpa [prefixWord, tailWord_3779632, baseEnd_3779632] using wordTrace_append hprefix tailTrace_3779632
  have hstable : (prefixWord ++ tailWord_3779632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779632).length < 2 ^ (prefixWord ++ tailWord_3779632).sum := by decide
  have hdescent : baseEnd_3779632 < baseStart_3779632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779662 : List Nat := [4, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3]
def baseStart_3779662 : Nat := 118140960795 + 3779662 * 2 ^ 59
def prefixEnd_3779662 : Nat := 4983230072969 + 3 ^ 40 * 3779662 * 2
def baseEnd_3779662 : Nat := 1940783317534096288742657

theorem tailTrace_3779662 : CollatzResearch.WordTrace tailWord_3779662 prefixEnd_3779662 1940783317534096288742657 := by
  unfold tailWord_3779662
  simp only [CollatzResearch.WordTrace]
  refine ⟨17231949804117195465330655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91903732288625042481763493 17231949804117195465330655)
  ·
    refine ⟨25847924706175793197995983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17231949804117195465330655 25847924706175793197995983)
    ·
      refine ⟨38771887059263689796993975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25847924706175793197995983 38771887059263689796993975)
      ·
        refine ⟨58157830588895534695490963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38771887059263689796993975 58157830588895534695490963)
        ·
          refine ⟨87236745883343302043236445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58157830588895534695490963 87236745883343302043236445)
          ·
            refine ⟨32713779706253738266213667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87236745883343302043236445 32713779706253738266213667)
            ·
              refine ⟨49070669559380607399320501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32713779706253738266213667 49070669559380607399320501)
              ·
                refine ⟨4600375271191931943686297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49070669559380607399320501 4600375271191931943686297)
                ·
                  refine ⟨3450281453393948957764723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4600375271191931943686297 3450281453393948957764723)
                  ·
                    refine ⟨5175422180090923436647085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3450281453393948957764723 5175422180090923436647085)
                    ·
                      refine ⟨1940783317534096288742657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5175422180090923436647085 1940783317534096288742657)
                      ·
                        rfl

theorem cell23_3779662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_3779662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779662 prefixEnd_3779662 := by exact prefixLift 3779662
  have htrace : WordTrace (prefixWord ++ tailWord_3779662) baseStart_3779662 baseEnd_3779662 := by
    simpa [prefixWord, tailWord_3779662, baseEnd_3779662] using wordTrace_append hprefix tailTrace_3779662
  have hstable : (prefixWord ++ tailWord_3779662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779662).length < 2 ^ (prefixWord ++ tailWord_3779662).sum := by decide
  have hdescent : baseEnd_3779662 < baseStart_3779662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779672 : List Nat := [2, 1, 2, 2, 1, 3, 2, 4, 1, 3, 2]
def baseStart_3779672 : Nat := 118140960795 + 3779672 * 2 ^ 59
def prefixEnd_3779672 : Nat := 4983230072969 + 3 ^ 40 * 3779672 * 2
def baseEnd_3779672 : Nat := 1940788452340641249617611

theorem tailTrace_3779672 : CollatzResearch.WordTrace tailWord_3779672 prefixEnd_3779672 1940788452340641249617611 := by
  unfold tailWord_3779672
  simp only [CollatzResearch.WordTrace]
  refine ⟨68927981581450667715254635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91903975441934223620339513 68927981581450667715254635)
  ·
    refine ⟨103391972372176001572881953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68927981581450667715254635 103391972372176001572881953)
    ·
      refine ⟨77543979279132001179661465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103391972372176001572881953 77543979279132001179661465)
      ·
        refine ⟨58157984459349000884746099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77543979279132001179661465 58157984459349000884746099)
        ·
          refine ⟨87236976689023501327119149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58157984459349000884746099 87236976689023501327119149)
          ·
            refine ⟨32713866258383812997669681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87236976689023501327119149 32713866258383812997669681)
            ·
              refine ⟨24535399693787859748252261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32713866258383812997669681 24535399693787859748252261)
              ·
                refine ⟨4600387442585223702797299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24535399693787859748252261 4600387442585223702797299)
                ·
                  refine ⟨6900581163877835554195949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4600387442585223702797299 6900581163877835554195949)
                  ·
                    refine ⟨2587717936454188332823481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6900581163877835554195949 2587717936454188332823481)
                    ·
                      refine ⟨1940788452340641249617611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2587717936454188332823481 1940788452340641249617611)
                      ·
                        rfl

theorem cell23_3779672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 1, 3, 2].length) (baseStart_3779672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779672 prefixEnd_3779672 := by exact prefixLift 3779672
  have htrace : WordTrace (prefixWord ++ tailWord_3779672) baseStart_3779672 baseEnd_3779672 := by
    simpa [prefixWord, tailWord_3779672, baseEnd_3779672] using wordTrace_append hprefix tailTrace_3779672
  have hstable : (prefixWord ++ tailWord_3779672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779672).length < 2 ^ (prefixWord ++ tailWord_3779672).sum := by decide
  have hdescent : baseEnd_3779672 < baseStart_3779672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779689 : List Nat := [1, 2, 1, 1, 1, 6, 4, 1, 1, 3, 2]
def baseStart_3779689 : Nat := 118140960795 + 3779689 * 2 ^ 59
def prefixEnd_3779689 : Nat := 4983230072969 + 3 ^ 40 * 3779689 * 2
def baseEnd_3779689 : Nat := 1940797181511767683105033

theorem tailTrace_3779689 : CollatzResearch.WordTrace tailWord_3779689 prefixEnd_3779689 1940797181511767683105033 := by
  unfold tailWord_3779689
  simp only [CollatzResearch.WordTrace]
  refine ⟨137856583203839747333878121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91904388802559831555918747 137856583203839747333878121)
  ·
    refine ⟨103392437402879810500408591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137856583203839747333878121 103392437402879810500408591)
    ·
      refine ⟨155088656104319715750612887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103392437402879810500408591 155088656104319715750612887)
      ·
        refine ⟨232632984156479573625919331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155088656104319715750612887 232632984156479573625919331)
        ·
          refine ⟨348949476234719360438878997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232632984156479573625919331 348949476234719360438878997)
          ·
            refine ⟨16357006698502470020572453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 348949476234719360438878997 16357006698502470020572453)
            ·
              refine ⟨3066938755969213128857335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16357006698502470020572453 3066938755969213128857335)
              ·
                refine ⟨4600408133953819693286003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3066938755969213128857335 4600408133953819693286003)
                ·
                  refine ⟨6900612200930729539929005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4600408133953819693286003 6900612200930729539929005)
                  ·
                    refine ⟨2587729575349023577473377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6900612200930729539929005 2587729575349023577473377)
                    ·
                      refine ⟨1940797181511767683105033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2587729575349023577473377 1940797181511767683105033)
                      ·
                        rfl

theorem cell23_3779689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 1, 3, 2].length) (baseStart_3779689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779689 prefixEnd_3779689 := by exact prefixLift 3779689
  have htrace : WordTrace (prefixWord ++ tailWord_3779689) baseStart_3779689 baseEnd_3779689 := by
    simpa [prefixWord, tailWord_3779689, baseEnd_3779689] using wordTrace_append hprefix tailTrace_3779689
  have hstable : (prefixWord ++ tailWord_3779689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779689).length < 2 ^ (prefixWord ++ tailWord_3779689).sum := by decide
  have hdescent : baseEnd_3779689 < baseStart_3779689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779768 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 2, 8]
def baseStart_3779768 : Nat := 118140960795 + 3779768 * 2 ^ 59
def prefixEnd_3779768 : Nat := 4983230072969 + 3 ^ 40 * 3779768 * 2
def baseEnd_3779768 : Nat := 646945915494490958005723

theorem tailTrace_3779768 : CollatzResearch.WordTrace tailWord_3779768 prefixEnd_3779768 646945915494490958005723 := by
  unfold tailWord_3779768
  simp only [CollatzResearch.WordTrace]
  refine ⟨68929732285276771913001979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91906309713702362550669305 68929732285276771913001979)
  ·
    refine ⟨103394598427915157869502969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68929732285276771913001979 103394598427915157869502969)
    ·
      refine ⟨77545948820936368402127227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103394598427915157869502969 77545948820936368402127227)
      ·
        refine ⟨116318923231404552603190841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77545948820936368402127227 116318923231404552603190841)
        ·
          refine ⟨87239192423553414452393131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116318923231404552603190841 87239192423553414452393131)
          ·
            refine ⟨130858788635330121678589697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87239192423553414452393131 130858788635330121678589697)
            ·
              refine ⟨98144091476497591258942273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130858788635330121678589697 98144091476497591258942273)
              ·
                refine ⟨73608068607373193444206705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98144091476497591258942273 73608068607373193444206705)
                ·
                  refine ⟨55206051455529895083155029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73608068607373193444206705 55206051455529895083155029)
                  ·
                    refine ⟨646945915494490958005723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55206051455529895083155029 646945915494490958005723)
                    ·
                      rfl

theorem cell23_3779768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 8].length) (baseStart_3779768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779768 prefixEnd_3779768 := by exact prefixLift 3779768
  have htrace : WordTrace (prefixWord ++ tailWord_3779768) baseStart_3779768 baseEnd_3779768 := by
    simpa [prefixWord, tailWord_3779768, baseEnd_3779768] using wordTrace_append hprefix tailTrace_3779768
  have hstable : (prefixWord ++ tailWord_3779768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779768).length < 2 ^ (prefixWord ++ tailWord_3779768).sum := by decide
  have hdescent : baseEnd_3779768 < baseStart_3779768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779795 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 6, 2, 3]
def baseStart_3779795 : Nat := 118140960795 + 3779795 * 2 ^ 59
def prefixEnd_3779795 : Nat := 4983230072969 + 3 ^ 40 * 3779795 * 2
def baseEnd_3779795 : Nat := 1940851610461144268379545

theorem tailTrace_3779795 : CollatzResearch.WordTrace tailWord_3779795 prefixEnd_3779795 1940851610461144268379545 := by
  unfold tailWord_3779795
  simp only [CollatzResearch.WordTrace]
  refine ⟨137860449341455727437236839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91906966227637151624824559 137860449341455727437236839)
  ·
    refine ⟨206790674012183591155855259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137860449341455727437236839 206790674012183591155855259)
    ·
      refine ⟨310186011018275386733782889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206790674012183591155855259 310186011018275386733782889)
      ·
        refine ⟨232639508263706540050337167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310186011018275386733782889 232639508263706540050337167)
        ·
          refine ⟨348959262395559810075505751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232639508263706540050337167 348959262395559810075505751)
          ·
            refine ⟨523438893593339715113258627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348959262395559810075505751 523438893593339715113258627)
            ·
              refine ⟨785158340390009572669887941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523438893593339715113258627 785158340390009572669887941)
              ·
                refine ⟨147217188823126794875603989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 785158340390009572669887941 147217188823126794875603989)
                ·
                  refine ⟨6900805726084068509793937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147217188823126794875603989 6900805726084068509793937)
                  ·
                    refine ⟨5175604294563051382345453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6900805726084068509793937 5175604294563051382345453)
                    ·
                      refine ⟨1940851610461144268379545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5175604294563051382345453 1940851610461144268379545)
                      ·
                        rfl

theorem cell23_3779795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 2, 3].length) (baseStart_3779795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779795 prefixEnd_3779795 := by exact prefixLift 3779795
  have htrace : WordTrace (prefixWord ++ tailWord_3779795) baseStart_3779795 baseEnd_3779795 := by
    simpa [prefixWord, tailWord_3779795, baseEnd_3779795] using wordTrace_append hprefix tailTrace_3779795
  have hstable : (prefixWord ++ tailWord_3779795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779795).length < 2 ^ (prefixWord ++ tailWord_3779795).sum := by decide
  have hdescent : baseEnd_3779795 < baseStart_3779795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779812 : List Nat := [2, 3, 1, 1, 1, 2, 4, 2, 2, 2, 3]
def baseStart_3779812 : Nat := 118140960795 + 3779812 * 2 ^ 59
def prefixEnd_3779812 : Nat := 4983230072969 + 3 ^ 40 * 3779812 * 2
def baseEnd_3779812 : Nat := 1940860339632270701866967

theorem tailTrace_3779812 : CollatzResearch.WordTrace tailWord_3779812 prefixEnd_3779812 1940860339632270701866967 := by
  unfold tailWord_3779812
  simp only [CollatzResearch.WordTrace]
  refine ⟨68930534691197069670302845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91907379588262759560403793 68930534691197069670302845)
  ·
    refine ⟨25848950509198901126363567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68930534691197069670302845 25848950509198901126363567)
    ·
      refine ⟨38773425763798351689545351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25848950509198901126363567 38773425763798351689545351)
      ·
        refine ⟨58160138645697527534318027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38773425763798351689545351 58160138645697527534318027)
        ·
          refine ⟨87240207968546291301477041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58160138645697527534318027 87240207968546291301477041)
          ·
            refine ⟨65430155976409718476107781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87240207968546291301477041 65430155976409718476107781)
            ·
              refine ⟨12268154245576822214270209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65430155976409718476107781 12268154245576822214270209)
              ·
                refine ⟨9201115684182616660702657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12268154245576822214270209 9201115684182616660702657)
                ·
                  refine ⟨6900836763136962495526993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9201115684182616660702657 6900836763136962495526993)
                  ·
                    refine ⟨5175627572352721871645245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6900836763136962495526993 5175627572352721871645245)
                    ·
                      refine ⟨1940860339632270701866967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5175627572352721871645245 1940860339632270701866967)
                      ·
                        rfl

theorem cell23_3779812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_3779812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779812 prefixEnd_3779812 := by exact prefixLift 3779812
  have htrace : WordTrace (prefixWord ++ tailWord_3779812) baseStart_3779812 baseEnd_3779812 := by
    simpa [prefixWord, tailWord_3779812, baseEnd_3779812] using wordTrace_append hprefix tailTrace_3779812
  have hstable : (prefixWord ++ tailWord_3779812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779812).length < 2 ^ (prefixWord ++ tailWord_3779812).sum := by decide
  have hdescent : baseEnd_3779812 < baseStart_3779812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779819 : List Nat := [1, 1, 1, 1, 2, 7, 1, 4, 1, 4]
def baseStart_3779819 : Nat := 118140960795 + 3779819 * 2 ^ 59
def prefixEnd_3779819 : Nat := 4983230072969 + 3 ^ 40 * 3779819 * 2
def baseEnd_3779819 : Nat := 646954644665617391493145

theorem tailTrace_3779819 : CollatzResearch.WordTrace tailWord_3779819 prefixEnd_3779819 646954644665617391493145 := by
  unfold tailWord_3779819
  simp only [CollatzResearch.WordTrace]
  refine ⟨137861324693368779536110511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91907549795579186357407007 137861324693368779536110511)
  ·
    refine ⟨206791987040053169304165767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137861324693368779536110511 206791987040053169304165767)
    ·
      refine ⟨310187980560079753956248651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206791987040053169304165767 310187980560079753956248651)
      ·
        refine ⟨465281970840119630934372977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310187980560079753956248651 465281970840119630934372977)
        ·
          refine ⟨348961478130089723200779733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465281970840119630934372977 348961478130089723200779733)
          ·
            refine ⟨8178784643673977887518275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 348961478130089723200779733 8178784643673977887518275)
            ·
              refine ⟨12268176965510966831277413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8178784643673977887518275 12268176965510966831277413)
              ·
                refine ⟨2300283181033306280864515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12268176965510966831277413 2300283181033306280864515)
                ·
                  refine ⟨3450424771549959421296773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2300283181033306280864515 3450424771549959421296773)
                  ·
                    refine ⟨646954644665617391493145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3450424771549959421296773 646954644665617391493145)
                    ·
                      rfl

theorem cell23_3779819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 4, 1, 4].length) (baseStart_3779819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779819 prefixEnd_3779819 := by exact prefixLift 3779819
  have htrace : WordTrace (prefixWord ++ tailWord_3779819) baseStart_3779819 baseEnd_3779819 := by
    simpa [prefixWord, tailWord_3779819, baseEnd_3779819] using wordTrace_append hprefix tailTrace_3779819
  have hstable : (prefixWord ++ tailWord_3779819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779819).length < 2 ^ (prefixWord ++ tailWord_3779819).sum := by decide
  have hdescent : baseEnd_3779819 < baseStart_3779819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779825 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 2, 5, 3]
def baseStart_3779825 : Nat := 118140960795 + 3779825 * 2 ^ 59
def prefixEnd_3779825 : Nat := 4983230072969 + 3 ^ 40 * 3779825 * 2
def baseEnd_3779825 : Nat := 1940867014880779151004407

theorem tailTrace_3779825 : CollatzResearch.WordTrace tailWord_3779825 prefixEnd_3779825 1940867014880779151004407 := by
  unfold tailWord_3779825
  simp only [CollatzResearch.WordTrace]
  refine ⟨137861543531347042560828929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91907695687564695040552619 137861543531347042560828929)
  ·
    refine ⟨103396157648510281920621697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137861543531347042560828929 103396157648510281920621697)
    ·
      refine ⟨77547118236382711440466273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103396157648510281920621697 77547118236382711440466273)
      ·
        refine ⟨58160338677287033580349705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77547118236382711440466273 58160338677287033580349705)
        ·
          refine ⟨43620254007965275185262279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58160338677287033580349705 43620254007965275185262279)
          ·
            refine ⟨65430381011947912777893419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43620254007965275185262279 65430381011947912777893419)
            ·
              refine ⟨98145571517921869166840129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65430381011947912777893419 98145571517921869166840129)
              ·
                refine ⟨73609178638441401875130097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98145571517921869166840129 73609178638441401875130097)
                ·
                  refine ⟨55206883978831051406347573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73609178638441401875130097 55206883978831051406347573)
                  ·
                    refine ⟨5175645373015411069345085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55206883978831051406347573 5175645373015411069345085)
                    ·
                      refine ⟨1940867014880779151004407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5175645373015411069345085 1940867014880779151004407)
                      ·
                        rfl

theorem cell23_3779825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_3779825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779825 prefixEnd_3779825 := by exact prefixLift 3779825
  have htrace : WordTrace (prefixWord ++ tailWord_3779825) baseStart_3779825 baseEnd_3779825 := by
    simpa [prefixWord, tailWord_3779825, baseEnd_3779825] using wordTrace_append hprefix tailTrace_3779825
  have hstable : (prefixWord ++ tailWord_3779825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779825).length < 2 ^ (prefixWord ++ tailWord_3779825).sum := by decide
  have hdescent : baseEnd_3779825 < baseStart_3779825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779845 : List Nat := [1, 3, 1, 1, 2, 1, 3, 3, 3, 5]
def baseStart_3779845 : Nat := 118140960795 + 3779845 * 2 ^ 59
def prefixEnd_3779845 : Nat := 4983230072969 + 3 ^ 40 * 3779845 * 2
def baseEnd_3779845 : Nat := 646959094831289690918105

theorem tailTrace_3779845 : CollatzResearch.WordTrace tailWord_3779845 prefixEnd_3779845 646959094831289690918105 := by
  unfold tailWord_3779845
  simp only [CollatzResearch.WordTrace]
  refine ⟨137862272991274585976556989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91908181994183057317704659 137862272991274585976556989)
  ·
    refine ⟨51698352371727969741208871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137862272991274585976556989 51698352371727969741208871)
    ·
      refine ⟨77547528557591954611813307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51698352371727969741208871 77547528557591954611813307)
      ·
        refine ⟨116321292836387931917719961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77547528557591954611813307 116321292836387931917719961)
        ·
          refine ⟨87240969627290948938289971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116321292836387931917719961 87240969627290948938289971)
          ·
            refine ⟨130861454440936423407434957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87240969627290948938289971 130861454440936423407434957)
            ·
              refine ⟨49073045415351158777788109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130861454440936423407434957 49073045415351158777788109)
              ·
                refine ⟨18402392030756684541670541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49073045415351158777788109 18402392030756684541670541)
                ·
                  refine ⟨6900897011533756703126453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18402392030756684541670541 6900897011533756703126453)
                  ·
                    refine ⟨646959094831289690918105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6900897011533756703126453 646959094831289690918105)
                    ·
                      rfl

theorem cell23_3779845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 5].length) (baseStart_3779845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779845 prefixEnd_3779845 := by exact prefixLift 3779845
  have htrace : WordTrace (prefixWord ++ tailWord_3779845) baseStart_3779845 baseEnd_3779845 := by
    simpa [prefixWord, tailWord_3779845, baseEnd_3779845] using wordTrace_append hprefix tailTrace_3779845
  have hstable : (prefixWord ++ tailWord_3779845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779845).length < 2 ^ (prefixWord ++ tailWord_3779845).sum := by decide
  have hdescent : baseEnd_3779845 < baseStart_3779845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779876 : List Nat := [2, 3, 1, 3, 1, 1, 1, 6, 1, 1, 3]
def baseStart_3779876 : Nat := 118140960795 + 3779876 * 2 ^ 59
def prefixEnd_3779876 : Nat := 4983230072969 + 3 ^ 40 * 3779876 * 2
def baseEnd_3779876 : Nat := 1940893202394158451466673

theorem tailTrace_3779876 : CollatzResearch.WordTrace tailWord_3779876 prefixEnd_3779876 1940893202394158451466673 := by
  unfold tailWord_3779876
  simp only [CollatzResearch.WordTrace]
  refine ⟨68931701827081139135467741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91908935769441518847290321 68931701827081139135467741)
  ·
    refine ⟨25849388185155427175800403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68931701827081139135467741 25849388185155427175800403)
    ·
      refine ⟨38774082277733140763700605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25849388185155427175800403 38774082277733140763700605)
      ·
        refine ⟨14540280854149927786387727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38774082277733140763700605 14540280854149927786387727)
        ·
          refine ⟨21810421281224891679581591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14540280854149927786387727 21810421281224891679581591)
          ·
            refine ⟨32715631921837337519372387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21810421281224891679581591 32715631921837337519372387)
            ·
              refine ⟨49073447882756006279058581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32715631921837337519372387 49073447882756006279058581)
              ·
                refine ⟨2300317869504187794330871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49073447882756006279058581 2300317869504187794330871)
                ·
                  refine ⟨3450476804256281691496307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2300317869504187794330871 3450476804256281691496307)
                  ·
                    refine ⟨5175715206384422537244461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3450476804256281691496307 5175715206384422537244461)
                    ·
                      refine ⟨1940893202394158451466673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5175715206384422537244461 1940893202394158451466673)
                      ·
                        rfl

theorem cell23_3779876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_3779876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779876 prefixEnd_3779876 := by exact prefixLift 3779876
  have htrace : WordTrace (prefixWord ++ tailWord_3779876) baseStart_3779876 baseEnd_3779876 := by
    simpa [prefixWord, tailWord_3779876, baseEnd_3779876] using wordTrace_append hprefix tailTrace_3779876
  have hstable : (prefixWord ++ tailWord_3779876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779876).length < 2 ^ (prefixWord ++ tailWord_3779876).sum := by decide
  have hdescent : baseEnd_3779876 < baseStart_3779876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779902 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 3, 1, 5]
def baseStart_3779902 : Nat := 118140960795 + 3779902 * 2 ^ 59
def prefixEnd_3779902 : Nat := 4983230072969 + 3 ^ 40 * 3779902 * 2
def baseEnd_3779902 : Nat := 1940906552891175349741553

theorem tailTrace_3779902 : CollatzResearch.WordTrace tailWord_3779902 prefixEnd_3779902 1940906552891175349741553 := by
  unfold tailWord_3779902
  simp only [CollatzResearch.WordTrace]
  refine ⟨17233043994008510588922745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91909567968045389807587973 17233043994008510588922745)
  ·
    refine ⟨12924782995506382941692059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17233043994008510588922745 12924782995506382941692059)
    ·
      refine ⟨19387174493259574412538089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12924782995506382941692059 19387174493259574412538089)
      ·
        refine ⟨14540380869944680809403567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19387174493259574412538089 14540380869944680809403567)
        ·
          refine ⟨21810571304917021214105351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14540380869944680809403567 21810571304917021214105351)
          ·
            refine ⟨32715856957375531821158027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21810571304917021214105351 32715856957375531821158027)
            ·
              refine ⟨49073785436063297731737041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32715856957375531821158027 49073785436063297731737041)
              ·
                refine ⟨36805339077047473298802781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49073785436063297731737041 36805339077047473298802781)
                ·
                  refine ⟨13802002153892802487051043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36805339077047473298802781 13802002153892802487051043)
                  ·
                    refine ⟨20703003230839203730576565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13802002153892802487051043 20703003230839203730576565)
                    ·
                      refine ⟨1940906552891175349741553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20703003230839203730576565 1940906552891175349741553)
                      ·
                        rfl

theorem cell23_3779902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_3779902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779902 prefixEnd_3779902 := by exact prefixLift 3779902
  have htrace : WordTrace (prefixWord ++ tailWord_3779902) baseStart_3779902 baseEnd_3779902 := by
    simpa [prefixWord, tailWord_3779902, baseEnd_3779902] using wordTrace_append hprefix tailTrace_3779902
  have hstable : (prefixWord ++ tailWord_3779902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779902).length < 2 ^ (prefixWord ++ tailWord_3779902).sum := by decide
  have hdescent : baseEnd_3779902 < baseStart_3779902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779935 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 2, 7]
def baseStart_3779935 : Nat := 118140960795 + 3779935 * 2 ^ 59
def prefixEnd_3779935 : Nat := 4983230072969 + 3 ^ 40 * 3779935 * 2
def baseEnd_3779935 : Nat := 646974499250924573542967

theorem tailTrace_3779935 : CollatzResearch.WordTrace tailWord_3779935 prefixEnd_3779935 646974499250924573542967 := by
  unfold tailWord_3779935
  simp only [CollatzResearch.WordTrace]
  refine ⟨137865555560948531347333259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91910370373965687564888839 137865555560948531347333259)
  ·
    refine ⟨206798333341422797020999889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137865555560948531347333259 206798333341422797020999889)
    ·
      refine ⟨155098750006067097765749917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206798333341422797020999889 155098750006067097765749917)
      ·
        refine ⟨58162031252275161662156219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155098750006067097765749917 58162031252275161662156219)
        ·
          refine ⟨87243046878412742493234329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58162031252275161662156219 87243046878412742493234329)
          ·
            refine ⟨65432285158809556869925747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87243046878412742493234329 65432285158809556869925747)
            ·
              refine ⟨98148427738214335304888621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65432285158809556869925747 98148427738214335304888621)
              ·
                refine ⟨36805660401830375739333233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98148427738214335304888621 36805660401830375739333233)
                ·
                  refine ⟨27604245301372781804499925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36805660401830375739333233 27604245301372781804499925)
                  ·
                    refine ⟨646974499250924573542967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27604245301372781804499925 646974499250924573542967)
                    ·
                      rfl

theorem cell23_3779935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 7].length) (baseStart_3779935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779935 prefixEnd_3779935 := by exact prefixLift 3779935
  have htrace : WordTrace (prefixWord ++ tailWord_3779935) baseStart_3779935 baseEnd_3779935 := by
    simpa [prefixWord, tailWord_3779935, baseEnd_3779935] using wordTrace_append hprefix tailTrace_3779935
  have hstable : (prefixWord ++ tailWord_3779935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779935).length < 2 ^ (prefixWord ++ tailWord_3779935).sum := by decide
  have hdescent : baseEnd_3779935 < baseStart_3779935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779943 : List Nat := [1, 1, 5, 1, 4, 2, 2, 1, 2, 4]
def baseStart_3779943 : Nat := 118140960795 + 3779943 * 2 ^ 59
def prefixEnd_3779943 : Nat := 4983230072969 + 3 ^ 40 * 3779943 * 2
def baseEnd_3779943 : Nat := 646975868532669896442955

theorem tailTrace_3779943 : CollatzResearch.WordTrace tailWord_3779943 prefixEnd_3779943 646975868532669896442955 := by
  unfold tailWord_3779943
  simp only [CollatzResearch.WordTrace]
  refine ⟨137865847344919548713624483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91910564896613032475749655 137865847344919548713624483)
  ·
    refine ⟨206798771017379323070436725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137865847344919548713624483 206798771017379323070436725)
    ·
      refine ⟨19387384782879311537853443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 206798771017379323070436725 19387384782879311537853443)
      ·
        refine ⟨29081077174318967306780165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19387384782879311537853443 29081077174318967306780165)
        ·
          refine ⟨5452701970184806370021281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29081077174318967306780165 5452701970184806370021281)
          ·
            refine ⟨4089526477638604777515961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5452701970184806370021281 4089526477638604777515961)
            ·
              refine ⟨3067144858228953583136971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4089526477638604777515961 3067144858228953583136971)
              ·
                refine ⟨4600717287343430374705457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3067144858228953583136971 4600717287343430374705457)
                ·
                  refine ⟨3450537965507572781029093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4600717287343430374705457 3450537965507572781029093)
                  ·
                    refine ⟨646975868532669896442955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3450537965507572781029093 646975868532669896442955)
                    ·
                      rfl

theorem cell23_3779943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_3779943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779943 prefixEnd_3779943 := by exact prefixLift 3779943
  have htrace : WordTrace (prefixWord ++ tailWord_3779943) baseStart_3779943 baseEnd_3779943 := by
    simpa [prefixWord, tailWord_3779943, baseEnd_3779943] using wordTrace_append hprefix tailTrace_3779943
  have hstable : (prefixWord ++ tailWord_3779943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779943).length < 2 ^ (prefixWord ++ tailWord_3779943).sum := by decide
  have hdescent : baseEnd_3779943 < baseStart_3779943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779945 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 1, 4, 5]
def baseStart_3779945 : Nat := 118140960795 + 3779945 * 2 ^ 59
def prefixEnd_3779945 : Nat := 4983230072969 + 3 ^ 40 * 3779945 * 2
def baseEnd_3779945 : Nat := 1940928632559318681503855

theorem tailTrace_3779945 : CollatzResearch.WordTrace tailWord_3779945 prefixEnd_3779945 1940928632559318681503855 := by
  unfold tailWord_3779945
  simp only [CollatzResearch.WordTrace]
  refine ⟨137865920290912303055197289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91910613527274868703464859 137865920290912303055197289)
  ·
    refine ⟨103399440218184227291397967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137865920290912303055197289 103399440218184227291397967)
    ·
      refine ⟨155099160327276340937096951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103399440218184227291397967 155099160327276340937096951)
      ·
        refine ⟨232648740490914511405645427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155099160327276340937096951 232648740490914511405645427)
        ·
          refine ⟨348973110736371767108468141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232648740490914511405645427 348973110736371767108468141)
          ·
            refine ⟨130864916526139412665675553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 348973110736371767108468141 130864916526139412665675553)
            ·
              refine ⟨98148687394604559499256665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130864916526139412665675553 98148687394604559499256665)
              ·
                refine ⟨73611515545953419624442499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98148687394604559499256665 73611515545953419624442499)
                ·
                  refine ⟨110417273318930129436663749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73611515545953419624442499 110417273318930129436663749)
                  ·
                    refine ⟨20703238747299399269374453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110417273318930129436663749 20703238747299399269374453)
                    ·
                      refine ⟨1940928632559318681503855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20703238747299399269374453 1940928632559318681503855)
                      ·
                        rfl

theorem cell23_3779945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 4, 5].length) (baseStart_3779945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779945 prefixEnd_3779945 := by exact prefixLift 3779945
  have htrace : WordTrace (prefixWord ++ tailWord_3779945) baseStart_3779945 baseEnd_3779945 := by
    simpa [prefixWord, tailWord_3779945, baseEnd_3779945] using wordTrace_append hprefix tailTrace_3779945
  have hstable : (prefixWord ++ tailWord_3779945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779945).length < 2 ^ (prefixWord ++ tailWord_3779945).sum := by decide
  have hdescent : baseEnd_3779945 < baseStart_3779945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779950 : List Nat := [4, 1, 2, 4, 2, 1, 1, 2, 1, 1, 4]
def baseStart_3779950 : Nat := 118140960795 + 3779950 * 2 ^ 59
def prefixEnd_3779950 : Nat := 4983230072969 + 3 ^ 40 * 3779950 * 2
def baseEnd_3779950 : Nat := 1940931199962591161941333

theorem tailTrace_3779950 : CollatzResearch.WordTrace tailWord_3779950 prefixEnd_3779950 1940931199962591161941333 := by
  unfold tailWord_3779950
  simp only [CollatzResearch.WordTrace]
  refine ⟨17233262831986773613641163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91910735103929459272752869 17233262831986773613641163)
  ·
    refine ⟨25849894247980160420461745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17233262831986773613641163 25849894247980160420461745)
    ·
      refine ⟨19387420685985120315346309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25849894247980160420461745 19387420685985120315346309)
      ·
        refine ⟨3635141378622210059127433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19387420685985120315346309 3635141378622210059127433)
        ·
          refine ⟨2726356033966657544345575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3635141378622210059127433 2726356033966657544345575)
          ·
            refine ⟨4089534050949986316518363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2726356033966657544345575 4089534050949986316518363)
            ·
              refine ⟨6134301076424979474777545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4089534050949986316518363 6134301076424979474777545)
              ·
                refine ⟨4600725807318734606083159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6134301076424979474777545 4600725807318734606083159)
                ·
                  refine ⟨6901088710978101909124739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4600725807318734606083159 6901088710978101909124739)
                  ·
                    refine ⟨10351633066467152863687109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6901088710978101909124739 10351633066467152863687109)
                    ·
                      refine ⟨1940931199962591161941333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10351633066467152863687109 1940931199962591161941333)
                      ·
                        rfl

theorem cell23_3779950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_3779950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779950 prefixEnd_3779950 := by exact prefixLift 3779950
  have htrace : WordTrace (prefixWord ++ tailWord_3779950) baseStart_3779950 baseEnd_3779950 := by
    simpa [prefixWord, tailWord_3779950, baseEnd_3779950] using wordTrace_append hprefix tailTrace_3779950
  have hstable : (prefixWord ++ tailWord_3779950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779950).length < 2 ^ (prefixWord ++ tailWord_3779950).sum := by decide
  have hdescent : baseEnd_3779950 < baseStart_3779950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779959 : List Nat := [1, 1, 3, 1, 1, 2, 5, 1, 3, 3, 2]
def baseStart_3779959 : Nat := 118140960795 + 3779959 * 2 ^ 59
def prefixEnd_3779959 : Nat := 4983230072969 + 3 ^ 40 * 3779959 * 2
def baseEnd_3779959 : Nat := 1940935821288481626728791

theorem tailTrace_3779959 : CollatzResearch.WordTrace tailWord_3779959 prefixEnd_3779959 1940935821288481626728791 := by
  unfold tailWord_3779959
  simp only [CollatzResearch.WordTrace]
  refine ⟨137866430912861583446206931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91910953941907722297471287 137866430912861583446206931)
  ·
    refine ⟨206799646369292375169310397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137866430912861583446206931 206799646369292375169310397)
    ·
      refine ⟨77549867388484640688491399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206799646369292375169310397 77549867388484640688491399)
      ·
        refine ⟨116324801082726961032737099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77549867388484640688491399 116324801082726961032737099)
        ·
          refine ⟨174487201624090441549105649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116324801082726961032737099 174487201624090441549105649)
          ·
            refine ⟨130865401218067831161829237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174487201624090441549105649 130865401218067831161829237)
            ·
              refine ⟨12268631364193859171421491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130865401218067831161829237 12268631364193859171421491)
              ·
                refine ⟨18402947046290788757132237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12268631364193859171421491 18402947046290788757132237)
                ·
                  refine ⟨6901105142359045783924589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18402947046290788757132237 6901105142359045783924589)
                  ·
                    refine ⟨2587914428384642168971721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6901105142359045783924589 2587914428384642168971721)
                    ·
                      refine ⟨1940935821288481626728791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2587914428384642168971721 1940935821288481626728791)
                      ·
                        rfl

theorem cell23_3779959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 3, 2].length) (baseStart_3779959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779959 prefixEnd_3779959 := by exact prefixLift 3779959
  have htrace : WordTrace (prefixWord ++ tailWord_3779959) baseStart_3779959 baseEnd_3779959 := by
    simpa [prefixWord, tailWord_3779959, baseEnd_3779959] using wordTrace_append hprefix tailTrace_3779959
  have hstable : (prefixWord ++ tailWord_3779959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779959).length < 2 ^ (prefixWord ++ tailWord_3779959).sum := by decide
  have hdescent : baseEnd_3779959 < baseStart_3779959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779970 : List Nat := [3, 4, 2, 1, 1, 2, 3, 1, 1, 2, 3]
def baseStart_3779970 : Nat := 118140960795 + 3779970 * 2 ^ 59
def prefixEnd_3779970 : Nat := 4983230072969 + 3 ^ 40 * 3779970 * 2
def baseEnd_3779970 : Nat := 1940941469575681083691241

theorem tailTrace_3779970 : CollatzResearch.WordTrace tailWord_3779970 prefixEnd_3779970 1940941469575681083691241 := by
  unfold tailWord_3779970
  simp only [CollatzResearch.WordTrace]
  refine ⟨34466708028955433081214341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91911221410547821549904909 34466708028955433081214341)
  ·
    refine ⟨6462507755429143702727689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34466708028955433081214341 6462507755429143702727689)
    ·
      refine ⟨4846880816571857777045767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6462507755429143702727689 4846880816571857777045767)
      ·
        refine ⟨7270321224857786665568651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4846880816571857777045767 7270321224857786665568651)
        ·
          refine ⟨10905481837286679998352977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7270321224857786665568651 10905481837286679998352977)
          ·
            refine ⟨8179111377965009998764733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10905481837286679998352977 8179111377965009998764733)
            ·
              refine ⟨3067166766736878749536775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8179111377965009998764733 3067166766736878749536775)
              ·
                refine ⟨4600750150105318124305163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3067166766736878749536775 4600750150105318124305163)
                ·
                  refine ⟨6901125225157977186457745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4600750150105318124305163 6901125225157977186457745)
                  ·
                    refine ⟨5175843918868482889843309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6901125225157977186457745 5175843918868482889843309)
                    ·
                      refine ⟨1940941469575681083691241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5175843918868482889843309 1940941469575681083691241)
                      ·
                        rfl

theorem cell23_3779970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_3779970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779970 prefixEnd_3779970 := by exact prefixLift 3779970
  have htrace : WordTrace (prefixWord ++ tailWord_3779970) baseStart_3779970 baseEnd_3779970 := by
    simpa [prefixWord, tailWord_3779970, baseEnd_3779970] using wordTrace_append hprefix tailTrace_3779970
  have hstable : (prefixWord ++ tailWord_3779970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779970).length < 2 ^ (prefixWord ++ tailWord_3779970).sum := by decide
  have hdescent : baseEnd_3779970 < baseStart_3779970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780072 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 2, 8]
def baseStart_3780072 : Nat := 118140960795 + 3780072 * 2 ^ 59
def prefixEnd_3780072 : Nat := 4983230072969 + 3 ^ 40 * 3780072 * 2
def baseEnd_3780072 : Nat := 646997948200813228205257

theorem tailTrace_3780072 : CollatzResearch.WordTrace tailWord_3780072 prefixEnd_3780072 646997948200813228205257 := by
  unfold tailWord_3780072
  simp only [CollatzResearch.WordTrace]
  refine ⟨68935276180726101872535235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91913701574301469163380313 68935276180726101872535235)
  ·
    refine ⟨103402914271089152808802853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68935276180726101872535235 103402914271089152808802853)
    ·
      refine ⟨19388046425829216151650535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103402914271089152808802853 19388046425829216151650535)
      ·
        refine ⟨29082069638743824227475803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19388046425829216151650535 29082069638743824227475803)
        ·
          refine ⟨43623104458115736341213705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29082069638743824227475803 43623104458115736341213705)
          ·
            refine ⟨32717328343586802255910279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43623104458115736341213705 32717328343586802255910279)
            ·
              refine ⟨49075992515380203383865419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32717328343586802255910279 49075992515380203383865419)
              ·
                refine ⟨73613988773070305075798129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49075992515380203383865419 73613988773070305075798129)
                ·
                  refine ⟨55210491579802728806848597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73613988773070305075798129 55210491579802728806848597)
                  ·
                    refine ⟨646997948200813228205257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55210491579802728806848597 646997948200813228205257)
                    ·
                      rfl

theorem cell23_3780072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_3780072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780072 prefixEnd_3780072 := by exact prefixLift 3780072
  have htrace : WordTrace (prefixWord ++ tailWord_3780072) baseStart_3780072 baseEnd_3780072 := by
    simpa [prefixWord, tailWord_3780072, baseEnd_3780072] using wordTrace_append hprefix tailTrace_3780072
  have hstable : (prefixWord ++ tailWord_3780072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780072).length < 2 ^ (prefixWord ++ tailWord_3780072).sum := by decide
  have hdescent : baseEnd_3780072 < baseStart_3780072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780079 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 1, 6, 2]
def baseStart_3780079 : Nat := 118140960795 + 3780079 * 2 ^ 59
def prefixEnd_3780079 : Nat := 4983230072969 + 3 ^ 40 * 3780079 * 2
def baseEnd_3780079 : Nat := 1940997438967021157228239

theorem tailTrace_3780079 : CollatzResearch.WordTrace tailWord_3780079 prefixEnd_3780079 1940997438967021157228239 := by
  unfold tailWord_3780079
  simp only [CollatzResearch.WordTrace]
  refine ⟨137870807672426843940575291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91913871781617895960383527 137870807672426843940575291)
  ·
    refine ⟨206806211508640265910862937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137870807672426843940575291 206806211508640265910862937)
    ·
      refine ⟨155104658631480199433147203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206806211508640265910862937 155104658631480199433147203)
      ·
        refine ⟨232656987947220299149720805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155104658631480199433147203 232656987947220299149720805)
        ·
          refine ⟨43623185240103806090572651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232656987947220299149720805 43623185240103806090572651)
          ·
            refine ⟨65434777860155709135858977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43623185240103806090572651 65434777860155709135858977)
            ·
              refine ⟨49076083395116781851894233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65434777860155709135858977 49076083395116781851894233)
              ·
                refine ⟨36807062546337586388920675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49076083395116781851894233 36807062546337586388920675)
                ·
                  refine ⟨55210593819506379583381013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36807062546337586388920675 55210593819506379583381013)
                  ·
                    refine ⟨2587996585289361542970985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55210593819506379583381013 2587996585289361542970985)
                    ·
                      refine ⟨1940997438967021157228239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2587996585289361542970985 1940997438967021157228239)
                      ·
                        rfl

theorem cell23_3780079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 6, 2].length) (baseStart_3780079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780079 prefixEnd_3780079 := by exact prefixLift 3780079
  have htrace : WordTrace (prefixWord ++ tailWord_3780079) baseStart_3780079 baseEnd_3780079 := by
    simpa [prefixWord, tailWord_3780079, baseEnd_3780079] using wordTrace_append hprefix tailTrace_3780079
  have hstable : (prefixWord ++ tailWord_3780079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780079).length < 2 ^ (prefixWord ++ tailWord_3780079).sum := by decide
  have hdescent : baseEnd_3780079 < baseStart_3780079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780092 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 1, 3, 6]
def baseStart_3780092 : Nat := 118140960795 + 3780092 * 2 ^ 59
def prefixEnd_3780092 : Nat := 4983230072969 + 3 ^ 40 * 3780092 * 2
def baseEnd_3780092 : Nat := 1941004114215529606365679

theorem tailTrace_3780092 : CollatzResearch.WordTrace tailWord_3780092 prefixEnd_3780092 1941004114215529606365679 := by
  unfold tailWord_3780092
  simp only [CollatzResearch.WordTrace]
  refine ⟨68935640910689873580399265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91914187880919831440532353 68935640910689873580399265)
  ·
    refine ⟨51701730683017405185299449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68935640910689873580399265 51701730683017405185299449)
    ·
      refine ⟨38776298012263053888974587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51701730683017405185299449 38776298012263053888974587)
      ·
        refine ⟨58164447018394580833461881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38776298012263053888974587 58164447018394580833461881)
        ·
          refine ⟨43623335263795935625096411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58164447018394580833461881 43623335263795935625096411)
          ·
            refine ⟨65435002895693903437644617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43623335263795935625096411 65435002895693903437644617)
            ·
              refine ⟨49076252171770427578233463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65435002895693903437644617 49076252171770427578233463)
              ·
                refine ⟨73614378257655641367350195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49076252171770427578233463 73614378257655641367350195)
                ·
                  refine ⟨110421567386483462051025293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73614378257655641367350195 110421567386483462051025293)
                  ·
                    refine ⟨41408087769931298269134485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110421567386483462051025293 41408087769931298269134485)
                    ·
                      refine ⟨1941004114215529606365679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41408087769931298269134485 1941004114215529606365679)
                      ·
                        rfl

theorem cell23_3780092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_3780092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780092 prefixEnd_3780092 := by exact prefixLift 3780092
  have htrace : WordTrace (prefixWord ++ tailWord_3780092) baseStart_3780092 baseEnd_3780092 := by
    simpa [prefixWord, tailWord_3780092, baseEnd_3780092] using wordTrace_append hprefix tailTrace_3780092
  have hstable : (prefixWord ++ tailWord_3780092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780092).length < 2 ^ (prefixWord ++ tailWord_3780092).sum := by decide
  have hdescent : baseEnd_3780092 < baseStart_3780092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780106 : List Nat := [3, 1, 2, 2, 2, 2, 3, 1, 3, 4]
def baseStart_3780106 : Nat := 118140960795 + 3780106 * 2 ^ 59
def prefixEnd_3780106 : Nat := 4983230072969 + 3 ^ 40 * 3780106 * 2
def baseEnd_3780106 : Nat := 647003767648230850530205

theorem tailTrace_3780106 : CollatzResearch.WordTrace tailWord_3780106 prefixEnd_3780106 647003767648230850530205 := by
  unfold tailWord_3780106
  simp only [CollatzResearch.WordTrace]
  refine ⟨34467948110832256887952043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91914528295552685034538781 34467948110832256887952043)
  ·
    refine ⟨51701922166248385331928065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34467948110832256887952043 51701922166248385331928065)
    ·
      refine ⟨38776441624686288998946049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51701922166248385331928065 38776441624686288998946049)
      ·
        refine ⟨29082331218514716749209537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38776441624686288998946049 29082331218514716749209537)
        ·
          refine ⟨21811748413886037561907153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29082331218514716749209537 21811748413886037561907153)
          ·
            refine ⟨16358811310414528171430365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21811748413886037561907153 16358811310414528171430365)
            ·
              refine ⟨6134554241405448064286387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16358811310414528171430365 6134554241405448064286387)
              ·
                refine ⟨9201831362108172096429581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6134554241405448064286387 9201831362108172096429581)
                ·
                  refine ⟨3450686760790564536161093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9201831362108172096429581 3450686760790564536161093)
                  ·
                    refine ⟨647003767648230850530205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3450686760790564536161093 647003767648230850530205)
                    ·
                      rfl

theorem cell23_3780106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_3780106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780106 prefixEnd_3780106 := by exact prefixLift 3780106
  have htrace : WordTrace (prefixWord ++ tailWord_3780106) baseStart_3780106 baseEnd_3780106 := by
    simpa [prefixWord, tailWord_3780106, baseEnd_3780106] using wordTrace_append hprefix tailTrace_3780106
  have hstable : (prefixWord ++ tailWord_3780106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780106).length < 2 ^ (prefixWord ++ tailWord_3780106).sum := by decide
  have hdescent : baseEnd_3780106 < baseStart_3780106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780157 : List Nat := [1, 4, 1, 3, 3, 2, 2, 2, 1, 4]
def baseStart_3780157 : Nat := 118140960795 + 3780157 * 2 ^ 59
def prefixEnd_3780157 : Nat := 4983230072969 + 3 ^ 40 * 3780157 * 2
def baseEnd_3780157 : Nat := 647012496819357284017627

theorem tailTrace_3780157 : CollatzResearch.WordTrace tailWord_3780157 prefixEnd_3780157 647012496819357284017627 := by
  unfold tailWord_3780157
  simp only [CollatzResearch.WordTrace]
  refine ⟨137873652566144263261914725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91915768377429508841276483 137873652566144263261914725)
  ·
    refine ⟨25851309856152049361609011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137873652566144263261914725 25851309856152049361609011)
    ·
      refine ⟨38776964784228074042413517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25851309856152049361609011 38776964784228074042413517)
      ·
        refine ⟨14541361794085527765905069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38776964784228074042413517 14541361794085527765905069)
        ·
          refine ⟨5453010672782072912214401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14541361794085527765905069 5453010672782072912214401)
          ·
            refine ⟨4089758004586554684160801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5453010672782072912214401 4089758004586554684160801)
            ·
              refine ⟨3067318503439916013120601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4089758004586554684160801 3067318503439916013120601)
              ·
                refine ⟨2300488877579937009840451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3067318503439916013120601 2300488877579937009840451)
                ·
                  refine ⟨3450733316369905514760677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2300488877579937009840451 3450733316369905514760677)
                  ·
                    refine ⟨647012496819357284017627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3450733316369905514760677 647012496819357284017627)
                    ·
                      rfl

theorem cell23_3780157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_3780157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780157 prefixEnd_3780157 := by exact prefixLift 3780157
  have htrace : WordTrace (prefixWord ++ tailWord_3780157) baseStart_3780157 baseEnd_3780157 := by
    simpa [prefixWord, tailWord_3780157, baseEnd_3780157] using wordTrace_append hprefix tailTrace_3780157
  have hstable : (prefixWord ++ tailWord_3780157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780157).length < 2 ^ (prefixWord ++ tailWord_3780157).sum := by decide
  have hdescent : baseEnd_3780157 < baseStart_3780157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780200 : List Nat := [2, 1, 4, 3, 1, 3, 2, 1, 1, 5]
def baseStart_3780200 : Nat := 118140960795 + 3780200 * 2 ^ 59
def prefixEnd_3780200 : Nat := 4983230072969 + 3 ^ 40 * 3780200 * 2
def baseEnd_3780200 : Nat := 647019856708738394605061

theorem tailTrace_3780200 : CollatzResearch.WordTrace tailWord_3780200 prefixEnd_3780200 647019856708738394605061 := by
  unfold tailWord_3780200
  simp only [CollatzResearch.WordTrace]
  refine ⟨68937610452494240802865027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91916813936658987737153369 68937610452494240802865027)
  ·
    refine ⟨103406415678741361204297541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68937610452494240802865027 103406415678741361204297541)
    ·
      refine ⟨19388702939764005225805789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103406415678741361204297541 19388702939764005225805789)
      ·
        refine ⟨7270763602411501959677171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19388702939764005225805789 7270763602411501959677171)
        ·
          refine ⟨10906145403617252939515757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7270763602411501959677171 10906145403617252939515757)
          ·
            refine ⟨4089804526356469852318409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10906145403617252939515757 4089804526356469852318409)
            ·
              refine ⟨3067353394767352389238807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4089804526356469852318409 3067353394767352389238807)
              ·
                refine ⟨4601030092151028583858211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3067353394767352389238807 4601030092151028583858211)
                ·
                  refine ⟨6901545138226542875787317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4601030092151028583858211 6901545138226542875787317)
                  ·
                    refine ⟨647019856708738394605061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6901545138226542875787317 647019856708738394605061)
                    ·
                      rfl

theorem cell23_3780200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_3780200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780200 prefixEnd_3780200 := by exact prefixLift 3780200
  have htrace : WordTrace (prefixWord ++ tailWord_3780200) baseStart_3780200 baseEnd_3780200 := by
    simpa [prefixWord, tailWord_3780200, baseEnd_3780200] using wordTrace_append hprefix tailTrace_3780200
  have hstable : (prefixWord ++ tailWord_3780200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780200).length < 2 ^ (prefixWord ++ tailWord_3780200).sum := by decide
  have hdescent : baseEnd_3780200 < baseStart_3780200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780213 : List Nat := [1, 3, 4, 2, 1, 2, 1, 1, 4, 4]
def baseStart_3780213 : Nat := 118140960795 + 3780213 * 2 ^ 59
def prefixEnd_3780213 : Nat := 4983230072969 + 3 ^ 40 * 3780213 * 2
def baseEnd_3780213 : Nat := 647022081791574544317541

theorem tailTrace_3780213 : CollatzResearch.WordTrace tailWord_3780213 prefixEnd_3780213 647022081791574544317541 := by
  unfold tailWord_3780213
  simp only [CollatzResearch.WordTrace]
  refine ⟨137875695053941384825953293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91917130035960923217302195 137875695053941384825953293)
  ·
    refine ⟨51703385645228019309732485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137875695053941384825953293 51703385645228019309732485)
    ·
      refine ⟨9694384808480253620574841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51703385645228019309732485 9694384808480253620574841)
      ·
        refine ⟨7270788606360190215431131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9694384808480253620574841 7270788606360190215431131)
        ·
          refine ⟨10906182909540285323146697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7270788606360190215431131 10906182909540285323146697)
          ·
            refine ⟨8179637182155213992360023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10906182909540285323146697 8179637182155213992360023)
            ·
              refine ⟨12269455773232820988540035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8179637182155213992360023 12269455773232820988540035)
              ·
                refine ⟨18404183659849231482810053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12269455773232820988540035 18404183659849231482810053)
                ·
                  refine ⟨3450784436221730903026885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18404183659849231482810053 3450784436221730903026885)
                  ·
                    refine ⟨647022081791574544317541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3450784436221730903026885 647022081791574544317541)
                    ·
                      rfl

theorem cell23_3780213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_3780213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780213 prefixEnd_3780213 := by exact prefixLift 3780213
  have htrace : WordTrace (prefixWord ++ tailWord_3780213) baseStart_3780213 baseEnd_3780213 := by
    simpa [prefixWord, tailWord_3780213, baseEnd_3780213] using wordTrace_append hprefix tailTrace_3780213
  have hstable : (prefixWord ++ tailWord_3780213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780213).length < 2 ^ (prefixWord ++ tailWord_3780213).sum := by decide
  have hdescent : baseEnd_3780213 < baseStart_3780213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780254 : List Nat := [4, 3, 1, 1, 1, 2, 3, 3, 1, 2, 2]
def baseStart_3780254 : Nat := 118140960795 + 3780254 * 2 ^ 59
def prefixEnd_3780254 : Nat := 4983230072969 + 3 ^ 40 * 3780254 * 2
def baseEnd_3780254 : Nat := 1941087298081557972539935

theorem tailTrace_3780254 : CollatzResearch.WordTrace tailWord_3780254 prefixEnd_3780254 1941087298081557972539935 := by
  unfold tailWord_3780254
  simp only [CollatzResearch.WordTrace]
  refine ⟨17234648805849106103524477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91918126964528565885463877 17234648805849106103524477)
  ·
    refine ⟨6462993302193414788821679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17234648805849106103524477 6462993302193414788821679)
    ·
      refine ⟨9694489953290122183232519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6462993302193414788821679 9694489953290122183232519)
      ·
        refine ⟨14541734929935183274848779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9694489953290122183232519 14541734929935183274848779)
        ·
          refine ⟨21812602394902774912273169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14541734929935183274848779 21812602394902774912273169)
          ·
            refine ⟨16359451796177081184204877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21812602394902774912273169 16359451796177081184204877)
            ·
              refine ⟨6134794423566405444076829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16359451796177081184204877 6134794423566405444076829)
              ·
                refine ⟨2300547908837402041528811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6134794423566405444076829 2300547908837402041528811)
                ·
                  refine ⟨3450821863256103062293217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2300547908837402041528811 3450821863256103062293217)
                  ·
                    refine ⟨2588116397442077296719913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3450821863256103062293217 2588116397442077296719913)
                    ·
                      refine ⟨1941087298081557972539935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2588116397442077296719913 1941087298081557972539935)
                      ·
                        rfl

theorem cell23_3780254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_3780254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780254 prefixEnd_3780254 := by exact prefixLift 3780254
  have htrace : WordTrace (prefixWord ++ tailWord_3780254) baseStart_3780254 baseEnd_3780254 := by
    simpa [prefixWord, tailWord_3780254, baseEnd_3780254] using wordTrace_append hprefix tailTrace_3780254
  have hstable : (prefixWord ++ tailWord_3780254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780254).length < 2 ^ (prefixWord ++ tailWord_3780254).sum := by decide
  have hdescent : baseEnd_3780254 < baseStart_3780254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780299 : List Nat := [1, 1, 1, 1, 3, 2, 1, 6, 7]
def baseStart_3780299 : Nat := 118140960795 + 3780299 * 2 ^ 59
def prefixEnd_3780299 : Nat := 4983230072969 + 3 ^ 40 * 3780299 * 2
def baseEnd_3780299 : Nat := 215678933856778921830803

theorem tailTrace_3780299 : CollatzResearch.WordTrace tailWord_3780299 prefixEnd_3780299 215678933856778921830803 := by
  unfold tailWord_3780299
  simp only [CollatzResearch.WordTrace]
  refine ⟨137878831731629821513583951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91919221154419881009055967 137878831731629821513583951)
  ·
    refine ⟨206818247597444732270375927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137878831731629821513583951 206818247597444732270375927)
    ·
      refine ⟨310227371396167098405563891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206818247597444732270375927 310227371396167098405563891)
      ·
        refine ⟨465341057094250647608345837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310227371396167098405563891 465341057094250647608345837)
        ·
          refine ⟨174502896410343992853129689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 465341057094250647608345837 174502896410343992853129689)
          ·
            refine ⟨130877172307757994639847267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174502896410343992853129689 130877172307757994639847267)
            ·
              refine ⟨196315758461636991959770901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130877172307757994639847267 196315758461636991959770901)
              ·
                refine ⟨9202301177889233998114261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 196315758461636991959770901 9202301177889233998114261)
                ·
                  refine ⟨215678933856778921830803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9202301177889233998114261 215678933856778921830803)
                  ·
                    rfl

theorem cell23_3780299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 7].length) (baseStart_3780299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780299 prefixEnd_3780299 := by exact prefixLift 3780299
  have htrace : WordTrace (prefixWord ++ tailWord_3780299) baseStart_3780299 baseEnd_3780299 := by
    simpa [prefixWord, tailWord_3780299, baseEnd_3780299] using wordTrace_append hprefix tailTrace_3780299
  have hstable : (prefixWord ++ tailWord_3780299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780299).length < 2 ^ (prefixWord ++ tailWord_3780299).sum := by decide
  have hdescent : baseEnd_3780299 < baseStart_3780299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780329 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 3, 7]
def baseStart_3780329 : Nat := 118140960795 + 3780329 * 2 ^ 59
def prefixEnd_3780329 : Nat := 4983230072969 + 3 ^ 40 * 3780329 * 2
def baseEnd_3780329 : Nat := 647041936376881726367363

theorem tailTrace_3780329 : CollatzResearch.WordTrace tailWord_3780329 prefixEnd_3780329 647041936376881726367363 := by
  unfold tailWord_3780329
  simp only [CollatzResearch.WordTrace]
  refine ⟨137879925921521136637176041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91919950614347424424784027 137879925921521136637176041)
  ·
    refine ⟨103409944441140852477882031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137879925921521136637176041 103409944441140852477882031)
    ·
      refine ⟨155114916661711278716823047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103409944441140852477882031 155114916661711278716823047)
      ·
        refine ⟨232672374992566918075234571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155114916661711278716823047 232672374992566918075234571)
        ·
          refine ⟨349008562488850377112851857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232672374992566918075234571 349008562488850377112851857)
          ·
            refine ⟨261756421866637782834638893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349008562488850377112851857 261756421866637782834638893)
            ·
              refine ⟨98158658199989168562989585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261756421866637782834638893 98158658199989168562989585)
              ·
                refine ⟨73618993649991876422242189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98158658199989168562989585 73618993649991876422242189)
                ·
                  refine ⟨27607122618746953658340821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73618993649991876422242189 27607122618746953658340821)
                  ·
                    refine ⟨647041936376881726367363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27607122618746953658340821 647041936376881726367363)
                    ·
                      rfl

theorem cell23_3780329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 7].length) (baseStart_3780329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780329 prefixEnd_3780329 := by exact prefixLift 3780329
  have htrace : WordTrace (prefixWord ++ tailWord_3780329) baseStart_3780329 baseEnd_3780329 := by
    simpa [prefixWord, tailWord_3780329, baseEnd_3780329] using wordTrace_append hprefix tailTrace_3780329
  have hstable : (prefixWord ++ tailWord_3780329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780329).length < 2 ^ (prefixWord ++ tailWord_3780329).sum := by decide
  have hdescent : baseEnd_3780329 < baseStart_3780329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780340 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_3780340 : Nat := 118140960795 + 3780340 * 2 ^ 59
def prefixEnd_3780340 : Nat := 4983230072969 + 3 ^ 40 * 3780340 * 2
def baseEnd_3780340 : Nat := 1941131457417844636064539

theorem tailTrace_3780340 : CollatzResearch.WordTrace tailWord_3780340 prefixEnd_3780340 1941131457417844636064539 := by
  unfold tailWord_3780340
  simp only [CollatzResearch.WordTrace]
  refine ⟨68940163562240642757913237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91920218082987523677217649 68940163562240642757913237)
  ·
    refine ⟨3231570166980030129277183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 68940163562240642757913237 3231570166980030129277183)
    ·
      refine ⟨4847355250470045193915775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3231570166980030129277183 4847355250470045193915775)
      ·
        refine ⟨7271032875705067790873663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4847355250470045193915775 7271032875705067790873663)
        ·
          refine ⟨10906549313557601686310495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7271032875705067790873663 10906549313557601686310495)
          ·
            refine ⟨16359823970336402529465743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10906549313557601686310495 16359823970336402529465743)
            ·
              refine ⟨24539735955504603794198615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16359823970336402529465743 24539735955504603794198615)
              ·
                refine ⟨36809603933256905691297923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24539735955504603794198615 36809603933256905691297923)
                ·
                  refine ⟨55214405899885358536946885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36809603933256905691297923 55214405899885358536946885)
                  ·
                    refine ⟨10352701106228504725677541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55214405899885358536946885 10352701106228504725677541)
                    ·
                      refine ⟨1941131457417844636064539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10352701106228504725677541 1941131457417844636064539)
                      ·
                        rfl

theorem cell23_3780340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_3780340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780340 prefixEnd_3780340 := by exact prefixLift 3780340
  have htrace : WordTrace (prefixWord ++ tailWord_3780340) baseStart_3780340 baseEnd_3780340 := by
    simpa [prefixWord, tailWord_3780340, baseEnd_3780340] using wordTrace_append hprefix tailTrace_3780340
  have hstable : (prefixWord ++ tailWord_3780340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780340).length < 2 ^ (prefixWord ++ tailWord_3780340).sum := by decide
  have hdescent : baseEnd_3780340 < baseStart_3780340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780365 : List Nat := [1, 7, 2, 1, 1, 2, 2, 1, 1, 3, 2]
def baseStart_3780365 : Nat := 118140960795 + 3780365 * 2 ^ 59
def prefixEnd_3780365 : Nat := 4983230072969 + 3 ^ 40 * 3780365 * 2
def baseEnd_3780365 : Nat := 1941144294434207038251925

theorem tailTrace_3780365 : CollatzResearch.WordTrace tailWord_3780365 prefixEnd_3780365 1941144294434207038251925 := by
  unfold tailWord_3780365
  simp only [CollatzResearch.WordTrace]
  refine ⟨137881238949390714785486549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91920825966260476523657699 137881238949390714785486549)
  ·
    refine ⟨3231591537876344877784841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 137881238949390714785486549 3231591537876344877784841)
    ·
      refine ⟨2423693653407258658338631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3231591537876344877784841 2423693653407258658338631)
      ·
        refine ⟨3635540480110887987507947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2423693653407258658338631 3635540480110887987507947)
        ·
          refine ⟨5453310720166331981261921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3635540480110887987507947 5453310720166331981261921)
          ·
            refine ⟨4089983040124748985946441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5453310720166331981261921 4089983040124748985946441)
            ·
              refine ⟨3067487280093561739459831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4089983040124748985946441 3067487280093561739459831)
              ·
                refine ⟨4601230920140342609189747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3067487280093561739459831 4601230920140342609189747)
                ·
                  refine ⟨6901846380210513913784621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4601230920140342609189747 6901846380210513913784621)
                  ·
                    refine ⟨2588192392578942717669233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6901846380210513913784621 2588192392578942717669233)
                    ·
                      refine ⟨1941144294434207038251925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2588192392578942717669233 1941144294434207038251925)
                      ·
                        rfl

theorem cell23_3780365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_3780365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780365 prefixEnd_3780365 := by exact prefixLift 3780365
  have htrace : WordTrace (prefixWord ++ tailWord_3780365) baseStart_3780365 baseEnd_3780365 := by
    simpa [prefixWord, tailWord_3780365, baseEnd_3780365] using wordTrace_append hprefix tailTrace_3780365
  have hstable : (prefixWord ++ tailWord_3780365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780365).length < 2 ^ (prefixWord ++ tailWord_3780365).sum := by decide
  have hdescent : baseEnd_3780365 < baseStart_3780365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780383 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 4, 4, 2]
def baseStart_3780383 : Nat := 118140960795 + 3780383 * 2 ^ 59
def prefixEnd_3780383 : Nat := 4983230072969 + 3 ^ 40 * 3780383 * 2
def baseEnd_3780383 : Nat := 1941153537085987967826841

theorem tailTrace_3780383 : CollatzResearch.WordTrace tailWord_3780383 prefixEnd_3780383 1941153537085987967826841 := by
  unfold tailWord_3780383
  simp only [CollatzResearch.WordTrace]
  refine ⟨137881895463325503859641803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91921263642217002573094535 137881895463325503859641803)
  ·
    refine ⟨206822843194988255789462705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137881895463325503859641803 206822843194988255789462705)
    ·
      refine ⟨155117132396241191842097029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206822843194988255789462705 155117132396241191842097029)
      ·
        refine ⟨29084462324295223470393193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155117132396241191842097029 29084462324295223470393193)
        ·
          refine ⟨21813346743221417602794895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29084462324295223470393193 21813346743221417602794895)
          ·
            refine ⟨32720020114832126404192343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21813346743221417602794895 32720020114832126404192343)
            ·
              refine ⟨49080030172248189606288515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32720020114832126404192343 49080030172248189606288515)
              ·
                refine ⟨73620045258372284409432773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49080030172248189606288515 73620045258372284409432773)
                ·
                  refine ⟨13803758485944803326768645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73620045258372284409432773 13803758485944803326768645)
                  ·
                    refine ⟨2588204716114650623769121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13803758485944803326768645 2588204716114650623769121)
                    ·
                      refine ⟨1941153537085987967826841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2588204716114650623769121 1941153537085987967826841)
                      ·
                        rfl

theorem cell23_3780383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_3780383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780383 prefixEnd_3780383 := by exact prefixLift 3780383
  have htrace : WordTrace (prefixWord ++ tailWord_3780383) baseStart_3780383 baseEnd_3780383 := by
    simpa [prefixWord, tailWord_3780383, baseEnd_3780383] using wordTrace_append hprefix tailTrace_3780383
  have hstable : (prefixWord ++ tailWord_3780383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780383).length < 2 ^ (prefixWord ++ tailWord_3780383).sum := by decide
  have hdescent : baseEnd_3780383 < baseStart_3780383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780444 : List Nat := [2, 2, 4, 2, 3, 1, 1, 1, 3, 4]
def baseStart_3780444 : Nat := 118140960795 + 3780444 * 2 ^ 59
def prefixEnd_3780444 : Nat := 4983230072969 + 3 ^ 40 * 3780444 * 2
def baseEnd_3780444 : Nat := 647061619801970743054687

theorem tailTrace_3780444 : CollatzResearch.WordTrace tailWord_3780444 prefixEnd_3780444 647061619801970743054687 := by
  unfold tailWord_3780444
  simp only [CollatzResearch.WordTrace]
  refine ⟨68942060158052255638806193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91922746877403007518408257 68942060158052255638806193)
  ·
    refine ⟨51706545118539191729104645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68942060158052255638806193 51706545118539191729104645)
    ·
      refine ⟨9694977209726098449207121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51706545118539191729104645 9694977209726098449207121)
      ·
        refine ⟨7271232907294573836905341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9694977209726098449207121 7271232907294573836905341)
        ·
          refine ⟨2726712340235465188839503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7271232907294573836905341 2726712340235465188839503)
          ·
            refine ⟨4090068510353197783259255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2726712340235465188839503 4090068510353197783259255)
            ·
              refine ⟨6135102765529796674888883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4090068510353197783259255 6135102765529796674888883)
              ·
                refine ⟨9202654148294695012333325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6135102765529796674888883 9202654148294695012333325)
                ·
                  refine ⟨3450995305610510629624997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9202654148294695012333325 3450995305610510629624997)
                  ·
                    refine ⟨647061619801970743054687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3450995305610510629624997 647061619801970743054687)
                    ·
                      rfl

theorem cell23_3780444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_3780444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780444 prefixEnd_3780444 := by exact prefixLift 3780444
  have htrace : WordTrace (prefixWord ++ tailWord_3780444) baseStart_3780444 baseEnd_3780444 := by
    simpa [prefixWord, tailWord_3780444, baseEnd_3780444] using wordTrace_append hprefix tailTrace_3780444
  have hstable : (prefixWord ++ tailWord_3780444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780444).length < 2 ^ (prefixWord ++ tailWord_3780444).sum := by decide
  have hdescent : baseEnd_3780444 < baseStart_3780444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780473 : List Nat := [1, 2, 1, 3, 2, 2, 3, 1, 3, 1, 4]
def baseStart_3780473 : Nat := 118140960795 + 3780473 * 2 ^ 59
def prefixEnd_3780473 : Nat := 4983230072969 + 3 ^ 40 * 3780473 * 2
def baseEnd_3780473 : Nat := 1941199750344892615701427

theorem tailTrace_3780473 : CollatzResearch.WordTrace tailWord_3780473 prefixEnd_3780473 1941199750344892615701427 := by
  unfold tailWord_3780473
  simp only [CollatzResearch.WordTrace]
  refine ⟨137885178032999449230418073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91923452021999632820278715 137885178032999449230418073)
  ·
    refine ⟨103413883524749586922813555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137885178032999449230418073 103413883524749586922813555)
    ·
      refine ⟨155120825287124380384220333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103413883524749586922813555 155120825287124380384220333)
      ·
        refine ⟨58170309482671642644082625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155120825287124380384220333 58170309482671642644082625)
        ·
          refine ⟨43627732112003731983061969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58170309482671642644082625 43627732112003731983061969)
          ·
            refine ⟨32720799084002798987296477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43627732112003731983061969 32720799084002798987296477)
            ·
              refine ⟨12270299656501049620236179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32720799084002798987296477 12270299656501049620236179)
              ·
                refine ⟨18405449484751574430354269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12270299656501049620236179 18405449484751574430354269)
                ·
                  refine ⟨6902043556781840411382851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18405449484751574430354269 6902043556781840411382851)
                  ·
                    refine ⟨10353065335172760617074277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6902043556781840411382851 10353065335172760617074277)
                    ·
                      refine ⟨1941199750344892615701427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10353065335172760617074277 1941199750344892615701427)
                      ·
                        rfl

theorem cell23_3780473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_3780473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780473 prefixEnd_3780473 := by exact prefixLift 3780473
  have htrace : WordTrace (prefixWord ++ tailWord_3780473) baseStart_3780473 baseEnd_3780473 := by
    simpa [prefixWord, tailWord_3780473, baseEnd_3780473] using wordTrace_append hprefix tailTrace_3780473
  have hstable : (prefixWord ++ tailWord_3780473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780473).length < 2 ^ (prefixWord ++ tailWord_3780473).sum := by decide
  have hdescent : baseEnd_3780473 < baseStart_3780473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780476 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 2, 5, 5]
def baseStart_3780476 : Nat := 118140960795 + 3780476 * 2 ^ 59
def prefixEnd_3780476 : Nat := 4983230072969 + 3 ^ 40 * 3780476 * 2
def baseEnd_3780476 : Nat := 1941201290786856103963913

theorem tailTrace_3780476 : CollatzResearch.WordTrace tailWord_3780476 prefixEnd_3780476 1941201290786856103963913 := by
  unfold tailWord_3780476
  simp only [CollatzResearch.WordTrace]
  refine ⟨68942643725994290371388641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91923524967992387161851521 68942643725994290371388641)
  ·
    refine ⟨51706982794495717778541481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68942643725994290371388641 51706982794495717778541481)
    ·
      refine ⟨38780237095871788333906111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51706982794495717778541481 38780237095871788333906111)
      ·
        refine ⟨58170355643807682500859167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38780237095871788333906111 58170355643807682500859167)
        ·
          refine ⟨87255533465711523751288751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58170355643807682500859167 87255533465711523751288751)
          ·
            refine ⟨130883300198567285626933127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87255533465711523751288751 130883300198567285626933127)
            ·
              refine ⟨196324950297850928440399691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130883300198567285626933127 196324950297850928440399691)
              ·
                refine ⟨294487425446776392660599537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196324950297850928440399691 294487425446776392660599537)
                ·
                  refine ⟨220865569085082294495449653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294487425446776392660599537 220865569085082294495449653)
                  ·
                    refine ⟨20706147101726465108948405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 220865569085082294495449653 20706147101726465108948405)
                    ·
                      refine ⟨1941201290786856103963913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20706147101726465108948405 1941201290786856103963913)
                      ·
                        rfl

theorem cell23_3780476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_3780476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780476 prefixEnd_3780476 := by exact prefixLift 3780476
  have htrace : WordTrace (prefixWord ++ tailWord_3780476) baseStart_3780476 baseEnd_3780476 := by
    simpa [prefixWord, tailWord_3780476, baseEnd_3780476] using wordTrace_append hprefix tailTrace_3780476
  have hstable : (prefixWord ++ tailWord_3780476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780476).length < 2 ^ (prefixWord ++ tailWord_3780476).sum := by decide
  have hdescent : baseEnd_3780476 < baseStart_3780476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780483 : List Nat := [1, 1, 1, 3, 4, 3, 1, 2, 1, 6]
def baseStart_3780483 : Nat := 118140960795 + 3780483 * 2 ^ 59
def prefixEnd_3780483 : Nat := 4983230072969 + 3 ^ 40 * 3780483 * 2
def baseEnd_3780483 : Nat := 647068295050479192192127

theorem tailTrace_3780483 : CollatzResearch.WordTrace tailWord_3780483 prefixEnd_3780483 647068295050479192192127 := by
  unfold tailWord_3780483
  simp only [CollatzResearch.WordTrace]
  refine ⟨137885542762963220938282103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91923695175308813958854735 137885542762963220938282103)
  ·
    refine ⟨206828314144444831407423155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137885542762963220938282103 206828314144444831407423155)
    ·
      refine ⟨310242471216667247111134733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206828314144444831407423155 310242471216667247111134733)
      ·
        refine ⟨116340926706250217666675525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310242471216667247111134733 116340926706250217666675525)
        ·
          refine ⟨21813923757421915812501661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116340926706250217666675525 21813923757421915812501661)
          ·
            refine ⟨8180221409033218429688123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21813923757421915812501661 8180221409033218429688123)
            ·
              refine ⟨12270332113549827644532185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8180221409033218429688123 12270332113549827644532185)
              ·
                refine ⟨9202749085162370733399139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12270332113549827644532185 9202749085162370733399139)
                ·
                  refine ⟨13804123627743556100098709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9202749085162370733399139 13804123627743556100098709)
                  ·
                    refine ⟨647068295050479192192127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13804123627743556100098709 647068295050479192192127)
                    ·
                      rfl

theorem cell23_3780483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 6].length) (baseStart_3780483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780483 prefixEnd_3780483 := by exact prefixLift 3780483
  have htrace : WordTrace (prefixWord ++ tailWord_3780483) baseStart_3780483 baseEnd_3780483 := by
    simpa [prefixWord, tailWord_3780483, baseEnd_3780483] using wordTrace_append hprefix tailTrace_3780483
  have hstable : (prefixWord ++ tailWord_3780483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780483).length < 2 ^ (prefixWord ++ tailWord_3780483).sum := by decide
  have hdescent : baseEnd_3780483 < baseStart_3780483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780487 : List Nat := [1, 1, 4, 2, 4, 1, 3, 1, 1, 5]
def baseStart_3780487 : Nat := 118140960795 + 3780487 * 2 ^ 59
def prefixEnd_3780487 : Nat := 4983230072969 + 3 ^ 40 * 3780487 * 2
def baseEnd_3780487 : Nat := 647068979691351853642121

theorem tailTrace_3780487 : CollatzResearch.WordTrace tailWord_3780487 prefixEnd_3780487 647068979691351853642121 := by
  unfold tailWord_3780487
  simp only [CollatzResearch.WordTrace]
  refine ⟨137885688654948729621427715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91923792436632486414285143 137885688654948729621427715)
  ·
    refine ⟨206828532982423094432141573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137885688654948729621427715 206828532982423094432141573)
    ·
      refine ⟨38780349934204330206026545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206828532982423094432141573 38780349934204330206026545)
      ·
        refine ⟨29085262450653247654519909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38780349934204330206026545 29085262450653247654519909)
        ·
          refine ⟨5453486709497483935222483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29085262450653247654519909 5453486709497483935222483)
          ·
            refine ⟨8180230064246225902833725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5453486709497483935222483 8180230064246225902833725)
            ·
              refine ⟨3067586274092334713562647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8180230064246225902833725 3067586274092334713562647)
              ·
                refine ⟨4601379411138502070343971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3067586274092334713562647 4601379411138502070343971)
                ·
                  refine ⟨6902069116707753105515957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4601379411138502070343971 6902069116707753105515957)
                  ·
                    refine ⟨647068979691351853642121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6902069116707753105515957 647068979691351853642121)
                    ·
                      rfl

theorem cell23_3780487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_3780487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780487 prefixEnd_3780487 := by exact prefixLift 3780487
  have htrace : WordTrace (prefixWord ++ tailWord_3780487) baseStart_3780487 baseEnd_3780487 := by
    simpa [prefixWord, tailWord_3780487, baseEnd_3780487] using wordTrace_append hprefix tailTrace_3780487
  have hstable : (prefixWord ++ tailWord_3780487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780487).length < 2 ^ (prefixWord ++ tailWord_3780487).sum := by decide
  have hdescent : baseEnd_3780487 < baseStart_3780487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780541 : List Nat := [1, 4, 1, 2, 3, 2, 2, 3, 1, 2, 2]
def baseStart_3780541 : Nat := 118140960795 + 3780541 * 2 ^ 59
def prefixEnd_3780541 : Nat := 4983230072969 + 3 ^ 40 * 3780541 * 2
def baseEnd_3780541 : Nat := 1941234667029398349651115

theorem tailTrace_3780541 : CollatzResearch.WordTrace tailWord_3780541 prefixEnd_3780541 1941234667029398349651115 := by
  unfold tailWord_3780541
  simp only [CollatzResearch.WordTrace]
  refine ⟨137887658196753096843893477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91925105464502064562595651 137887658196753096843893477)
  ·
    refine ⟨25853935911891205658230027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137887658196753096843893477 25853935911891205658230027)
    ·
      refine ⟨38780903867836808487345041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25853935911891205658230027 38780903867836808487345041)
      ·
        refine ⟨29085677900877606365508781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38780903867836808487345041 29085677900877606365508781)
        ·
          refine ⟨10907129212829102387065793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29085677900877606365508781 10907129212829102387065793)
          ·
            refine ⟨8180346909621826790299345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10907129212829102387065793 8180346909621826790299345)
            ·
              refine ⟨6135260182216370092724509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8180346909621826790299345 6135260182216370092724509)
              ·
                refine ⟨2300722568331138784771691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6135260182216370092724509 2300722568331138784771691)
                ·
                  refine ⟨3451083852496708177157537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2300722568331138784771691 3451083852496708177157537)
                  ·
                    refine ⟨2588312889372531132868153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3451083852496708177157537 2588312889372531132868153)
                    ·
                      refine ⟨1941234667029398349651115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2588312889372531132868153 1941234667029398349651115)
                      ·
                        rfl

theorem cell23_3780541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_3780541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780541 prefixEnd_3780541 := by exact prefixLift 3780541
  have htrace : WordTrace (prefixWord ++ tailWord_3780541) baseStart_3780541 baseEnd_3780541 := by
    simpa [prefixWord, tailWord_3780541, baseEnd_3780541] using wordTrace_append hprefix tailTrace_3780541
  have hstable : (prefixWord ++ tailWord_3780541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780541).length < 2 ^ (prefixWord ++ tailWord_3780541).sum := by decide
  have hdescent : baseEnd_3780541 < baseStart_3780541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780631 : List Nat := [1, 1, 3, 5, 2, 1, 1, 3, 2, 2, 2]
def baseStart_3780631 : Nat := 118140960795 + 3780631 * 2 ^ 59
def prefixEnd_3780631 : Nat := 4983230072969 + 3 ^ 40 * 3780631 * 2
def baseEnd_3780631 : Nat := 1941280880288302997525701

theorem tailTrace_3780631 : CollatzResearch.WordTrace tailWord_3780631 prefixEnd_3780631 1941280880288302997525701 := by
  unfold tailWord_3780631
  simp only [CollatzResearch.WordTrace]
  refine ⟨137890940766427042214669747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91927293844284694809779831 137890940766427042214669747)
  ·
    refine ⟨206836411149640563322004621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137890940766427042214669747 206836411149640563322004621)
    ·
      refine ⟨77563654181115211245751733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206836411149640563322004621 77563654181115211245751733)
      ·
        refine ⟨7271592579479551054289225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77563654181115211245751733 7271592579479551054289225)
        ·
          refine ⟨5453694434609663290716919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7271592579479551054289225 5453694434609663290716919)
          ·
            refine ⟨8180541651914494936075379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5453694434609663290716919 8180541651914494936075379)
            ·
              refine ⟨12270812477871742404113069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8180541651914494936075379 12270812477871742404113069)
              ·
                refine ⟨4601554679201903401542401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12270812477871742404113069 4601554679201903401542401)
                ·
                  refine ⟨3451166009401427551156801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4601554679201903401542401 3451166009401427551156801)
                  ·
                    refine ⟨2588374507051070663367601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3451166009401427551156801 2588374507051070663367601)
                    ·
                      refine ⟨1941280880288302997525701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2588374507051070663367601 1941280880288302997525701)
                      ·
                        rfl

theorem cell23_3780631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_3780631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780631 prefixEnd_3780631 := by exact prefixLift 3780631
  have htrace : WordTrace (prefixWord ++ tailWord_3780631) baseStart_3780631 baseEnd_3780631 := by
    simpa [prefixWord, tailWord_3780631, baseEnd_3780631] using wordTrace_append hprefix tailTrace_3780631
  have hstable : (prefixWord ++ tailWord_3780631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780631).length < 2 ^ (prefixWord ++ tailWord_3780631).sum := by decide
  have hdescent : baseEnd_3780631 < baseStart_3780631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780633 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 6, 5]
def baseStart_3780633 : Nat := 118140960795 + 3780633 * 2 ^ 59
def prefixEnd_3780633 : Nat := 4983230072969 + 3 ^ 40 * 3780633 * 2
def baseEnd_3780633 : Nat := 647093969083203996566897

theorem tailTrace_3780633 : CollatzResearch.WordTrace tailWord_3780633 prefixEnd_3780633 647093969083203996566897 := by
  unfold tailWord_3780633
  simp only [CollatzResearch.WordTrace]
  refine ⟨137891013712419796556242553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91927342474946531037495035 137891013712419796556242553)
  ·
    refine ⟨103418260284314847417181915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137891013712419796556242553 103418260284314847417181915)
    ·
      refine ⟨155127390426472271125772873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103418260284314847417181915 155127390426472271125772873)
      ·
        refine ⟨116345542819854203344329655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155127390426472271125772873 116345542819854203344329655)
        ·
          refine ⟨174518314229781305016494483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116345542819854203344329655 174518314229781305016494483)
          ·
            refine ⟨261777471344671957524741725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174518314229781305016494483 261777471344671957524741725)
            ·
              refine ⟨98166551754251984071778147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261777471344671957524741725 98166551754251984071778147)
              ·
                refine ⟨147249827631377976107667221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98166551754251984071778147 147249827631377976107667221)
                ·
                  refine ⟨6902335670220842630046901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147249827631377976107667221 6902335670220842630046901)
                  ·
                    refine ⟨647093969083203996566897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6902335670220842630046901 647093969083203996566897)
                    ·
                      rfl

theorem cell23_3780633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 5].length) (baseStart_3780633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780633 prefixEnd_3780633 := by exact prefixLift 3780633
  have htrace : WordTrace (prefixWord ++ tailWord_3780633) baseStart_3780633 baseEnd_3780633 := by
    simpa [prefixWord, tailWord_3780633, baseEnd_3780633] using wordTrace_append hprefix tailTrace_3780633
  have hstable : (prefixWord ++ tailWord_3780633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780633).length < 2 ^ (prefixWord ++ tailWord_3780633).sum := by decide
  have hdescent : baseEnd_3780633 < baseStart_3780633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780643 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 7]
def baseStart_3780643 : Nat := 118140960795 + 3780643 * 2 ^ 59
def prefixEnd_3780643 : Nat := 4983230072969 + 3 ^ 40 * 3780643 * 2
def baseEnd_3780643 : Nat := 1941287042056156950575645

theorem tailTrace_3780643 : CollatzResearch.WordTrace tailWord_3780643 prefixEnd_3780643 1941287042056156950575645 := by
  unfold tailWord_3780643
  simp only [CollatzResearch.WordTrace]
  refine ⟨137891378442383568264106583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91927585628255712176071055 137891378442383568264106583)
  ·
    refine ⟨206837067663575352396159875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137891378442383568264106583 206837067663575352396159875)
    ·
      refine ⟨310255601495363028594239813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206837067663575352396159875 310255601495363028594239813)
      ·
        refine ⟨58172925280380567861419965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 310255601495363028594239813 58172925280380567861419965)
        ·
          refine ⟨21814846980142712948032487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58172925280380567861419965 21814846980142712948032487)
          ·
            refine ⟨32722270470214069422048731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21814846980142712948032487 32722270470214069422048731)
            ·
              refine ⟨49083405705321104133073097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32722270470214069422048731 49083405705321104133073097)
              ·
                refine ⟨36812554278990828099804823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49083405705321104133073097 36812554278990828099804823)
                ·
                  refine ⟨55218831418486242149707235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36812554278990828099804823 55218831418486242149707235)
                  ·
                    refine ⟨82828247127729363224560853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55218831418486242149707235 82828247127729363224560853)
                    ·
                      refine ⟨1941287042056156950575645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 82828247127729363224560853 1941287042056156950575645)
                      ·
                        rfl

theorem cell23_3780643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_3780643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780643 prefixEnd_3780643 := by exact prefixLift 3780643
  have htrace : WordTrace (prefixWord ++ tailWord_3780643) baseStart_3780643 baseEnd_3780643 := by
    simpa [prefixWord, tailWord_3780643, baseEnd_3780643] using wordTrace_append hprefix tailTrace_3780643
  have hstable : (prefixWord ++ tailWord_3780643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780643).length < 2 ^ (prefixWord ++ tailWord_3780643).sum := by decide
  have hdescent : baseEnd_3780643 < baseStart_3780643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780683 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 6]
def baseStart_3780683 : Nat := 118140960795 + 3780683 * 2 ^ 59
def prefixEnd_3780683 : Nat := 4983230072969 + 3 ^ 40 * 3780683 * 2
def baseEnd_3780683 : Nat := 1941307581282336794075461

theorem tailTrace_3780683 : CollatzResearch.WordTrace tailWord_3780683 prefixEnd_3780683 1941307581282336794075461 := by
  unfold tailWord_3780683
  simp only [CollatzResearch.WordTrace]
  refine ⟨137892837362238655095562703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91928558241492436730375135 137892837362238655095562703)
  ·
    refine ⟨206839256043357982643344055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137892837362238655095562703 206839256043357982643344055)
    ·
      refine ⟨310258884065036973965016083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206839256043357982643344055 310258884065036973965016083)
      ·
        refine ⟨465388326097555460947524125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310258884065036973965016083 465388326097555460947524125)
        ·
          refine ⟨174520622286583297855321547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 465388326097555460947524125 174520622286583297855321547)
          ·
            refine ⟨261780933429874946782982321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174520622286583297855321547 261780933429874946782982321)
            ·
              refine ⟨196335700072406210087236741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261780933429874946782982321 196335700072406210087236741)
              ·
                refine ⟨36812943763576164391356889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 196335700072406210087236741 36812943763576164391356889)
                ·
                  refine ⟨27609707822682123293517667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36812943763576164391356889 27609707822682123293517667)
                  ·
                    refine ⟨41414561734023184940276501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27609707822682123293517667 41414561734023184940276501)
                    ·
                      refine ⟨1941307581282336794075461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41414561734023184940276501 1941307581282336794075461)
                      ·
                        rfl

theorem cell23_3780683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 6].length) (baseStart_3780683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780683 prefixEnd_3780683 := by exact prefixLift 3780683
  have htrace : WordTrace (prefixWord ++ tailWord_3780683) baseStart_3780683 baseEnd_3780683 := by
    simpa [prefixWord, tailWord_3780683, baseEnd_3780683] using wordTrace_append hprefix tailTrace_3780683
  have hstable : (prefixWord ++ tailWord_3780683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780683).length < 2 ^ (prefixWord ++ tailWord_3780683).sum := by decide
  have hdescent : baseEnd_3780683 < baseStart_3780683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780707 : List Nat := [1, 1, 1, 5, 1, 1, 5, 1, 2, 2, 3]
def baseStart_3780707 : Nat := 118140960795 + 3780707 * 2 ^ 59
def prefixEnd_3780707 : Nat := 4983230072969 + 3 ^ 40 * 3780707 * 2
def baseEnd_3780707 : Nat := 1941319904818044700175351

theorem tailTrace_3780707 : CollatzResearch.WordTrace tailWord_3780707 prefixEnd_3780707 1941319904818044700175351 := by
  unfold tailWord_3780707
  simp only [CollatzResearch.WordTrace]
  refine ⟨137893712714151707194436375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91929141809434471462957583 137893712714151707194436375)
  ·
    refine ⟨206840569071227560791654563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137893712714151707194436375 206840569071227560791654563)
    ·
      refine ⟨310260853606841341187481845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206840569071227560791654563 310260853606841341187481845)
      ·
        refine ⟨29086955025641375736326423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 310260853606841341187481845 29086955025641375736326423)
        ·
          refine ⟨43630432538462063604489635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29086955025641375736326423 43630432538462063604489635)
          ·
            refine ⟨65445648807693095406734453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43630432538462063604489635 65445648807693095406734453)
            ·
              refine ⟨6135529575721227694381355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65445648807693095406734453 6135529575721227694381355)
              ·
                refine ⟨9203294363581841541572033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6135529575721227694381355 9203294363581841541572033)
                ·
                  refine ⟨6902470772686381156179025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9203294363581841541572033 6902470772686381156179025)
                  ·
                    refine ⟨5176853079514785867134269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6902470772686381156179025 5176853079514785867134269)
                    ·
                      refine ⟨1941319904818044700175351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5176853079514785867134269 1941319904818044700175351)
                      ·
                        rfl

theorem cell23_3780707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_3780707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780707 prefixEnd_3780707 := by exact prefixLift 3780707
  have htrace : WordTrace (prefixWord ++ tailWord_3780707) baseStart_3780707 baseEnd_3780707 := by
    simpa [prefixWord, tailWord_3780707, baseEnd_3780707] using wordTrace_append hprefix tailTrace_3780707
  have hstable : (prefixWord ++ tailWord_3780707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780707).length < 2 ^ (prefixWord ++ tailWord_3780707).sum := by decide
  have hdescent : baseEnd_3780707 < baseStart_3780707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780727 : List Nat := [1, 1, 3, 1, 1, 7, 1, 2, 6]
def baseStart_3780727 : Nat := 118140960795 + 3780727 * 2 ^ 59
def prefixEnd_3780727 : Nat := 4983230072969 + 3 ^ 40 * 3780727 * 2
def baseEnd_3780727 : Nat := 215703352714570513547251

theorem tailTrace_3780727 : CollatzResearch.WordTrace tailWord_3780727 prefixEnd_3780727 215703352714570513547251 := by
  unfold tailWord_3780727
  simp only [CollatzResearch.WordTrace]
  refine ⟨137894442174079250610164435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91929628116052833740109623 137894442174079250610164435)
  ·
    refine ⟨206841663261118875915246653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137894442174079250610164435 206841663261118875915246653)
    ·
      refine ⟨77565623722919578468217495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206841663261118875915246653 77565623722919578468217495)
      ·
        refine ⟨116348435584379367702326243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77565623722919578468217495 116348435584379367702326243)
        ·
          refine ⟨174522653376569051553489365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116348435584379367702326243 174522653376569051553489365)
          ·
            refine ⟨4090374688513337145784907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 174522653376569051553489365 4090374688513337145784907)
            ·
              refine ⟨6135562032770005718677361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4090374688513337145784907 6135562032770005718677361)
              ·
                refine ⟨4601671524577504289008021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6135562032770005718677361 4601671524577504289008021)
                ·
                  refine ⟨215703352714570513547251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4601671524577504289008021 215703352714570513547251)
                  ·
                    rfl

theorem cell23_3780727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 6].length) (baseStart_3780727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780727 prefixEnd_3780727 := by exact prefixLift 3780727
  have htrace : WordTrace (prefixWord ++ tailWord_3780727) baseStart_3780727 baseEnd_3780727 := by
    simpa [prefixWord, tailWord_3780727, baseEnd_3780727] using wordTrace_append hprefix tailTrace_3780727
  have hstable : (prefixWord ++ tailWord_3780727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780727).length < 2 ^ (prefixWord ++ tailWord_3780727).sum := by decide
  have hdescent : baseEnd_3780727 < baseStart_3780727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780744 : List Nat := [2, 1, 3, 4, 1, 2, 3, 1, 6]
def baseStart_3780744 : Nat := 118140960795 + 3780744 * 2 ^ 59
def prefixEnd_3780744 : Nat := 4983230072969 + 3 ^ 40 * 3780744 * 2
def baseEnd_3780744 : Nat := 215704322622473450601409

theorem tailTrace_3780744 : CollatzResearch.WordTrace tailWord_3780744 prefixEnd_3780744 215704322622473450601409 := by
  unfold tailWord_3780744
  simp only [CollatzResearch.WordTrace]
  refine ⟨68947531107508831256766643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91930041476678441675688857 68947531107508831256766643)
  ·
    refine ⟨103421296661263246885149965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68947531107508831256766643 103421296661263246885149965)
    ·
      refine ⟨38782986247973717581931237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103421296661263246885149965 38782986247973717581931237)
      ·
        refine ⟨7271809921495072046612107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38782986247973717581931237 7271809921495072046612107)
        ·
          refine ⟨10907714882242608069918161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7271809921495072046612107 10907714882242608069918161)
          ·
            refine ⟨8180786161681956052438621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10907714882242608069918161 8180786161681956052438621)
            ·
              refine ⟨3067794810630733519664483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8180786161681956052438621 3067794810630733519664483)
              ·
                refine ⟨4601692215946100279496725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3067794810630733519664483 4601692215946100279496725)
                ·
                  refine ⟨215704322622473450601409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4601692215946100279496725 215704322622473450601409)
                  ·
                    rfl

theorem cell23_3780744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 6].length) (baseStart_3780744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780744 prefixEnd_3780744 := by exact prefixLift 3780744
  have htrace : WordTrace (prefixWord ++ tailWord_3780744) baseStart_3780744 baseEnd_3780744 := by
    simpa [prefixWord, tailWord_3780744, baseEnd_3780744] using wordTrace_append hprefix tailTrace_3780744
  have hstable : (prefixWord ++ tailWord_3780744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780744).length < 2 ^ (prefixWord ++ tailWord_3780744).sum := by decide
  have hdescent : baseEnd_3780744 < baseStart_3780744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780754 : List Nat := [3, 2, 3, 1, 1, 1, 1, 4, 3, 1, 3]
def baseStart_3780754 : Nat := 118140960795 + 3780754 * 2 ^ 59
def prefixEnd_3780754 : Nat := 4983230072969 + 3 ^ 40 * 3780754 * 2
def baseEnd_3780754 : Nat := 1941344038408806016287635

theorem tailTrace_3780754 : CollatzResearch.WordTrace tailWord_3780754 prefixEnd_3780754 1941344038408806016287635 := by
  unfold tailWord_3780754
  simp only [CollatzResearch.WordTrace]
  refine ⟨34473856736245358555349329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91930284629987622814264877 34473856736245358555349329)
  ·
    refine ⟨25855392552184018916511997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34473856736245358555349329 25855392552184018916511997)
    ·
      refine ⟨9695772207069007093691999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25855392552184018916511997 9695772207069007093691999)
      ·
        refine ⟨14543658310603510640537999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9695772207069007093691999 14543658310603510640537999)
        ·
          refine ⟨21815487465905265960806999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14543658310603510640537999 21815487465905265960806999)
          ·
            refine ⟨32723231198857898941210499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21815487465905265960806999 32723231198857898941210499)
            ·
              refine ⟨49084846798286848411815749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32723231198857898941210499 49084846798286848411815749)
              ·
                refine ⟨9203408774678784077215453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49084846798286848411815749 9203408774678784077215453)
                ·
                  refine ⟨3451278290504544028955795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9203408774678784077215453 3451278290504544028955795)
                  ·
                    refine ⟨5176917435756816043433693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3451278290504544028955795 5176917435756816043433693)
                    ·
                      refine ⟨1941344038408806016287635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5176917435756816043433693 1941344038408806016287635)
                      ·
                        rfl

theorem cell23_3780754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_3780754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780754 prefixEnd_3780754 := by exact prefixLift 3780754
  have htrace : WordTrace (prefixWord ++ tailWord_3780754) baseStart_3780754 baseEnd_3780754 := by
    simpa [prefixWord, tailWord_3780754, baseEnd_3780754] using wordTrace_append hprefix tailTrace_3780754
  have hstable : (prefixWord ++ tailWord_3780754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780754).length < 2 ^ (prefixWord ++ tailWord_3780754).sum := by decide
  have hdescent : baseEnd_3780754 < baseStart_3780754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780757 : List Nat := [1, 3, 2, 1, 1, 1, 6, 2, 1, 5]
def baseStart_3780757 : Nat := 118140960795 + 3780757 * 2 ^ 59
def prefixEnd_3780757 : Nat := 4983230072969 + 3 ^ 40 * 3780757 * 2
def baseEnd_3780757 : Nat := 647115192950256501516707

theorem tailTrace_3780757 : CollatzResearch.WordTrace tailWord_3780757 prefixEnd_3780757 647115192950256501516707 := by
  unfold tailWord_3780757
  simp only [CollatzResearch.WordTrace]
  refine ⟨137895536363970565733756525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91930357575980377155837683 137895536363970565733756525)
  ·
    refine ⟨51710826136488962150158697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137895536363970565733756525 51710826136488962150158697)
    ·
      refine ⟨38783119602366721612619023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51710826136488962150158697 38783119602366721612619023)
      ·
        refine ⟨58174679403550082418928535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38783119602366721612619023 58174679403550082418928535)
        ·
          refine ⟨87262019105325123628392803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58174679403550082418928535 87262019105325123628392803)
          ·
            refine ⟨130893028657987685442589205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87262019105325123628392803 130893028657987685442589205)
            ·
              refine ⟨6135610718343172755121369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130893028657987685442589205 6135610718343172755121369)
              ·
                refine ⟨4601708038757379566341027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6135610718343172755121369 4601708038757379566341027)
                ·
                  refine ⟨6902562058136069349511541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4601708038757379566341027 6902562058136069349511541)
                  ·
                    refine ⟨647115192950256501516707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6902562058136069349511541 647115192950256501516707)
                    ·
                      rfl

theorem cell23_3780757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_3780757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780757 prefixEnd_3780757 := by exact prefixLift 3780757
  have htrace : WordTrace (prefixWord ++ tailWord_3780757) baseStart_3780757 baseEnd_3780757 := by
    simpa [prefixWord, tailWord_3780757, baseEnd_3780757] using wordTrace_append hprefix tailTrace_3780757
  have hstable : (prefixWord ++ tailWord_3780757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780757).length < 2 ^ (prefixWord ++ tailWord_3780757).sum := by decide
  have hdescent : baseEnd_3780757 < baseStart_3780757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780764 : List Nat := [2, 2, 3, 2, 1, 1, 2, 3, 2, 3, 2]
def baseStart_3780764 : Nat := 118140960795 + 3780764 * 2 ^ 59
def prefixEnd_3780764 : Nat := 4983230072969 + 3 ^ 40 * 3780764 * 2
def baseEnd_3780764 : Nat := 1941349173215350977162589

theorem tailTrace_3780764 : CollatzResearch.WordTrace tailWord_3780764 prefixEnd_3780764 1941349173215350977162589 := by
  unfold tailWord_3780764
  simp only [CollatzResearch.WordTrace]
  refine ⟨68947895837472602964630673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91930527783296803952840897 68947895837472602964630673)
  ·
    refine ⟨51710921878104452223473005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68947895837472602964630673 51710921878104452223473005)
    ·
      refine ⟨19391595704289169583802377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51710921878104452223473005 19391595704289169583802377)
      ·
        refine ⟨14543696778216877187851783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19391595704289169583802377 14543696778216877187851783)
        ·
          refine ⟨21815545167325315781777675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14543696778216877187851783 21815545167325315781777675)
          ·
            refine ⟨32723317750987973672666513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21815545167325315781777675 32723317750987973672666513)
            ·
              refine ⟨24542488313240980254499885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32723317750987973672666513 24542488313240980254499885)
              ·
                refine ⟨9203433117465367595437457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24542488313240980254499885 9203433117465367595437457)
                ·
                  refine ⟨6902574838099025696578093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9203433117465367595437457 6902574838099025696578093)
                  ·
                    refine ⟨2588465564287134636216785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6902574838099025696578093 2588465564287134636216785)
                    ·
                      refine ⟨1941349173215350977162589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2588465564287134636216785 1941349173215350977162589)
                      ·
                        rfl

theorem cell23_3780764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_3780764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780764 prefixEnd_3780764 := by exact prefixLift 3780764
  have htrace : WordTrace (prefixWord ++ tailWord_3780764) baseStart_3780764 baseEnd_3780764 := by
    simpa [prefixWord, tailWord_3780764, baseEnd_3780764] using wordTrace_append hprefix tailTrace_3780764
  have hstable : (prefixWord ++ tailWord_3780764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780764).length < 2 ^ (prefixWord ++ tailWord_3780764).sum := by decide
  have hdescent : baseEnd_3780764 < baseStart_3780764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780780 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 3]
def baseStart_3780780 : Nat := 118140960795 + 3780780 * 2 ^ 59
def prefixEnd_3780780 : Nat := 4983230072969 + 3 ^ 40 * 3780780 * 2
def baseEnd_3780780 : Nat := 1941357388905822914562515

theorem tailTrace_3780780 : CollatzResearch.WordTrace tailWord_3780780 prefixEnd_3780780 1941357388905822914562515 := by
  unfold tailWord_3780780
  simp only [CollatzResearch.WordTrace]
  refine ⟨68948187621443620330921897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91930916828591493774562529 68948187621443620330921897)
  ·
    refine ⟨51711140716082715248191423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68948187621443620330921897 51711140716082715248191423)
    ·
      refine ⟨77566711074124072872287135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51711140716082715248191423 77566711074124072872287135)
      ·
        refine ⟨116350066611186109308430703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77566711074124072872287135 116350066611186109308430703)
        ·
          refine ⟨174525099916779163962646055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116350066611186109308430703 174525099916779163962646055)
          ·
            refine ⟨261787649875168745943969083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174525099916779163962646055 261787649875168745943969083)
            ·
              refine ⟨392681474812753118915953625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261787649875168745943969083 392681474812753118915953625)
              ·
                refine ⟨294511106109564839186965219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 392681474812753118915953625 294511106109564839186965219)
                ·
                  refine ⟨441766659164347258780447829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294511106109564839186965219 441766659164347258780447829)
                  ·
                    refine ⟨5176953037082194438833373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 441766659164347258780447829 5176953037082194438833373)
                    ·
                      refine ⟨1941357388905822914562515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5176953037082194438833373 1941357388905822914562515)
                      ·
                        rfl

theorem cell23_3780780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 3].length) (baseStart_3780780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780780 prefixEnd_3780780 := by exact prefixLift 3780780
  have htrace : WordTrace (prefixWord ++ tailWord_3780780) baseStart_3780780 baseEnd_3780780 := by
    simpa [prefixWord, tailWord_3780780, baseEnd_3780780] using wordTrace_append hprefix tailTrace_3780780
  have hstable : (prefixWord ++ tailWord_3780780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780780).length < 2 ^ (prefixWord ++ tailWord_3780780).sum := by decide
  have hdescent : baseEnd_3780780 < baseStart_3780780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780781 : List Nat := [1, 5, 2, 1, 2, 2, 1, 2, 2, 3, 2]
def baseStart_3780781 : Nat := 118140960795 + 3780781 * 2 ^ 59
def prefixEnd_3780781 : Nat := 4983230072969 + 3 ^ 40 * 3780781 * 2
def baseEnd_3780781 : Nat := 1941357902386477410650011

theorem tailTrace_3780781 : CollatzResearch.WordTrace tailWord_3780781 prefixEnd_3780781 1941357902386477410650011 := by
  unfold tailWord_3780781
  simp only [CollatzResearch.WordTrace]
  refine ⟨137896411715883617832630197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91930941143922411888420131 137896411715883617832630197)
  ·
    refine ⟨12927788598364089171809081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137896411715883617832630197 12927788598364089171809081)
    ·
      refine ⟨9695841448773066878856811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12927788598364089171809081 9695841448773066878856811)
      ·
        refine ⟨14543762173159600318285217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9695841448773066878856811 14543762173159600318285217)
        ·
          refine ⟨10907821629869700238713913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14543762173159600318285217 10907821629869700238713913)
          ·
            refine ⟨8180866222402275179035435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10907821629869700238713913 8180866222402275179035435)
            ·
              refine ⟨12271299333603412768553153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8180866222402275179035435 12271299333603412768553153)
              ·
                refine ⟨9203474500202559576414865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12271299333603412768553153 9203474500202559576414865)
                ·
                  refine ⟨6902605875151919682311149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9203474500202559576414865 6902605875151919682311149)
                  ·
                    refine ⟨2588477203181969880866681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6902605875151919682311149 2588477203181969880866681)
                    ·
                      refine ⟨1941357902386477410650011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2588477203181969880866681 1941357902386477410650011)
                      ·
                        rfl

theorem cell23_3780781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_3780781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780781 prefixEnd_3780781 := by exact prefixLift 3780781
  have htrace : WordTrace (prefixWord ++ tailWord_3780781) baseStart_3780781 baseEnd_3780781 := by
    simpa [prefixWord, tailWord_3780781, baseEnd_3780781] using wordTrace_append hprefix tailTrace_3780781
  have hstable : (prefixWord ++ tailWord_3780781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780781).length < 2 ^ (prefixWord ++ tailWord_3780781).sum := by decide
  have hdescent : baseEnd_3780781 < baseStart_3780781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780787 : List Nat := [1, 1, 1, 2, 3, 2, 1, 6, 2, 4]
def baseStart_3780787 : Nat := 118140960795 + 3780787 * 2 ^ 59
def prefixEnd_3780787 : Nat := 4983230072969 + 3 ^ 40 * 3780787 * 2
def baseEnd_3780787 : Nat := 647120327756801462391661

theorem tailTrace_3780787 : CollatzResearch.WordTrace tailWord_3780787 prefixEnd_3780787 647120327756801462391661 := by
  unfold tailWord_3780787
  simp only [CollatzResearch.WordTrace]
  refine ⟨137896630553861880857348615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91931087035907920571565743 137896630553861880857348615)
  ·
    refine ⟨206844945830792821286022923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137896630553861880857348615 206844945830792821286022923)
    ·
      refine ⟨310267418746189231929034385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206844945830792821286022923 310267418746189231929034385)
      ·
        refine ⟨232700564059641923946775789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310267418746189231929034385 232700564059641923946775789)
        ·
          refine ⟨87262711522365721480040921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232700564059641923946775789 87262711522365721480040921)
          ·
            refine ⟨65447033641774291110030691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87262711522365721480040921 65447033641774291110030691)
            ·
              refine ⟨98170550462661436665046037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65447033641774291110030691 98170550462661436665046037)
              ·
                refine ⟨4601744552937254843674033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98170550462661436665046037 4601744552937254843674033)
                ·
                  refine ⟨3451308414702941132755525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4601744552937254843674033 3451308414702941132755525)
                  ·
                    refine ⟨647120327756801462391661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3451308414702941132755525 647120327756801462391661)
                    ·
                      rfl

theorem cell23_3780787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 2, 4].length) (baseStart_3780787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780787 prefixEnd_3780787 := by exact prefixLift 3780787
  have htrace : WordTrace (prefixWord ++ tailWord_3780787) baseStart_3780787 baseEnd_3780787 := by
    simpa [prefixWord, tailWord_3780787, baseEnd_3780787] using wordTrace_append hprefix tailTrace_3780787
  have hstable : (prefixWord ++ tailWord_3780787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780787).length < 2 ^ (prefixWord ++ tailWord_3780787).sum := by decide
  have hdescent : baseEnd_3780787 < baseStart_3780787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780797 : List Nat := [1, 4, 1, 2, 1, 1, 1, 4, 3, 2, 3]
def baseStart_3780797 : Nat := 118140960795 + 3780797 * 2 ^ 59
def prefixEnd_3780797 : Nat := 4983230072969 + 3 ^ 40 * 3780797 * 2
def baseEnd_3780797 : Nat := 1941366118076949348049937

theorem tailTrace_3780797 : CollatzResearch.WordTrace tailWord_3780797 prefixEnd_3780797 1941366118076949348049937 := by
  unfold tailWord_3780797
  simp only [CollatzResearch.WordTrace]
  refine ⟨137896995283825652565212645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91931330189217101710141763 137896995283825652565212645)
  ·
    refine ⟨25855686615717309855977371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137896995283825652565212645 25855686615717309855977371)
    ·
      refine ⟨38783529923575964783966057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25855686615717309855977371 38783529923575964783966057)
      ·
        refine ⟨29087647442681973587974543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38783529923575964783966057 29087647442681973587974543)
        ·
          refine ⟨43631471164022960381961815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29087647442681973587974543 43631471164022960381961815)
          ·
            refine ⟨65447206746034440572942723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43631471164022960381961815 65447206746034440572942723)
            ·
              refine ⟨98170810119051660859414085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65447206746034440572942723 98170810119051660859414085)
              ·
                refine ⟨18407026897322186411140141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98170810119051660859414085 18407026897322186411140141)
                ·
                  refine ⟨6902635086495819904177553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18407026897322186411140141 6902635086495819904177553)
                  ·
                    refine ⟨5176976314871864928133165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6902635086495819904177553 5176976314871864928133165)
                    ·
                      refine ⟨1941366118076949348049937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5176976314871864928133165 1941366118076949348049937)
                      ·
                        rfl

theorem cell23_3780797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_3780797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780797 prefixEnd_3780797 := by exact prefixLift 3780797
  have htrace : WordTrace (prefixWord ++ tailWord_3780797) baseStart_3780797 baseEnd_3780797 := by
    simpa [prefixWord, tailWord_3780797, baseEnd_3780797] using wordTrace_append hprefix tailTrace_3780797
  have hstable : (prefixWord ++ tailWord_3780797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780797).length < 2 ^ (prefixWord ++ tailWord_3780797).sum := by decide
  have hdescent : baseEnd_3780797 < baseStart_3780797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780800 : List Nat := [2, 1, 1, 2, 5, 1, 1, 10]
def baseStart_3780800 : Nat := 118140960795 + 3780800 * 2 ^ 59
def prefixEnd_3780800 : Nat := 4983230072969 + 3 ^ 40 * 3780800 * 2
def baseEnd_3780800 : Nat := 71902505871070845789349

theorem tailTrace_3780800 : CollatzResearch.WordTrace tailWord_3780800 prefixEnd_3780800 71902505871070845789349 := by
  unfold tailWord_3780800
  simp only [CollatzResearch.WordTrace]
  refine ⟨68948552351407392038785927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91931403135209856051714569 68948552351407392038785927)
  ·
    refine ⟨103422828527111088058178891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68948552351407392038785927 103422828527111088058178891)
    ·
      refine ⟨155134242790666632087268337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103422828527111088058178891 155134242790666632087268337)
      ·
        refine ⟨116350682092999974065451253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155134242790666632087268337 116350682092999974065451253)
        ·
          refine ⟨10907876446218747568636055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116350682092999974065451253 10907876446218747568636055)
          ·
            refine ⟨16361814669328121352954083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10907876446218747568636055 16361814669328121352954083)
            ·
              refine ⟨24542722003992182029431125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16361814669328121352954083 24542722003992182029431125)
              ·
                refine ⟨71902505871070845789349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 24542722003992182029431125 71902505871070845789349)
                ·
                  rfl

theorem cell23_3780800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 10].length) (baseStart_3780800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780800 prefixEnd_3780800 := by exact prefixLift 3780800
  have htrace : WordTrace (prefixWord ++ tailWord_3780800) baseStart_3780800 baseEnd_3780800 := by
    simpa [prefixWord, tailWord_3780800, baseEnd_3780800] using wordTrace_append hprefix tailTrace_3780800
  have hstable : (prefixWord ++ tailWord_3780800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780800).length < 2 ^ (prefixWord ++ tailWord_3780800).sum := by decide
  have hdescent : baseEnd_3780800 < baseStart_3780800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780814 : List Nat := [4, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3]
def baseStart_3780814 : Nat := 118140960795 + 3780814 * 2 ^ 59
def prefixEnd_3780814 : Nat := 4983230072969 + 3 ^ 40 * 3780814 * 2
def baseEnd_3780814 : Nat := 1941374847248075781537359

theorem tailTrace_3780814 : CollatzResearch.WordTrace tailWord_3780814 prefixEnd_3780814 1941374847248075781537359 := by
  unfold tailWord_3780814
  simp only [CollatzResearch.WordTrace]
  refine ⟨17237201915595508058572687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91931743549842709645720997 17237201915595508058572687)
  ·
    refine ⟨25855802873393262087859031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17237201915595508058572687 25855802873393262087859031)
    ·
      refine ⟨38783704310089893131788547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25855802873393262087859031 38783704310089893131788547)
      ·
        refine ⟨58175556465134839697682821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38783704310089893131788547 58175556465134839697682821)
        ·
          refine ⟨10907916837212782443315529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58175556465134839697682821 10907916837212782443315529)
          ·
            refine ⟨8180937627909586832486647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10907916837212782443315529 8180937627909586832486647)
            ·
              refine ⟨12271406441864380248729971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8180937627909586832486647 12271406441864380248729971)
              ·
                refine ⟨18407109662796570373094957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12271406441864380248729971 18407109662796570373094957)
                ·
                  refine ⟨6902666123548713889910609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18407109662796570373094957 6902666123548713889910609)
                  ·
                    refine ⟨5176999592661535417432957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6902666123548713889910609 5176999592661535417432957)
                    ·
                      refine ⟨1941374847248075781537359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5176999592661535417432957 1941374847248075781537359)
                      ·
                        rfl

theorem cell23_3780814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_3780814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780814 prefixEnd_3780814 := by exact prefixLift 3780814
  have htrace : WordTrace (prefixWord ++ tailWord_3780814) baseStart_3780814 baseEnd_3780814 := by
    simpa [prefixWord, tailWord_3780814, baseEnd_3780814] using wordTrace_append hprefix tailTrace_3780814
  have hstable : (prefixWord ++ tailWord_3780814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780814).length < 2 ^ (prefixWord ++ tailWord_3780814).sum := by decide
  have hdescent : baseEnd_3780814 < baseStart_3780814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780834 : List Nat := [3, 3, 4, 1, 12]
def baseStart_3780834 : Nat := 118140960795 + 3780834 * 2 ^ 59
def prefixEnd_3780834 : Nat := 4983230072969 + 3 ^ 40 * 3780834 * 2
def baseEnd_3780834 : Nat := 2663079721345906314523

theorem tailTrace_3780834 : CollatzResearch.WordTrace tailWord_3780834 prefixEnd_3780834 2663079721345906314523 := by
  unfold tailWord_3780834
  simp only [CollatzResearch.WordTrace]
  refine ⟨34474586196172901971077389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91932229856461071922873037 34474586196172901971077389)
  ·
    refine ⟨12927969823564838239154021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34474586196172901971077389 12927969823564838239154021)
    ·
      refine ⟨2423994341918407169841379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12927969823564838239154021 2423994341918407169841379)
      ·
        refine ⟨3635991512877610754762069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2423994341918407169841379 3635991512877610754762069)
        ·
          refine ⟨2663079721345906314523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3635991512877610754762069 2663079721345906314523)
          ·
            rfl

theorem cell23_3780834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 12].length) (baseStart_3780834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780834 prefixEnd_3780834 := by exact prefixLift 3780834
  have htrace : WordTrace (prefixWord ++ tailWord_3780834) baseStart_3780834 baseEnd_3780834 := by
    simpa [prefixWord, tailWord_3780834, baseEnd_3780834] using wordTrace_append hprefix tailTrace_3780834
  have hstable : (prefixWord ++ tailWord_3780834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780834).length < 2 ^ (prefixWord ++ tailWord_3780834).sum := by decide
  have hdescent : baseEnd_3780834 < baseStart_3780834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780845 : List Nat := [1, 5, 1, 2, 3, 1, 1, 4, 1, 2, 2]
def baseStart_3780845 : Nat := 118140960795 + 3780845 * 2 ^ 59
def prefixEnd_3780845 : Nat := 4983230072969 + 3 ^ 40 * 3780845 * 2
def baseEnd_3780845 : Nat := 1941390765148365160249717

theorem tailTrace_3780845 : CollatzResearch.WordTrace tailWord_3780845 prefixEnd_3780845 1941390765148365160249717 := by
  unfold tailWord_3780845
  simp only [CollatzResearch.WordTrace]
  refine ⟨137898745987651756762959989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91932497325101171175306659 137898745987651756762959989)
  ·
    refine ⟨12928007436342352196527499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137898745987651756762959989 12928007436342352196527499)
    ·
      refine ⟨19392011154513528294791249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12928007436342352196527499 19392011154513528294791249)
      ·
        refine ⟨14544008365885146221093437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19392011154513528294791249 14544008365885146221093437)
        ·
          refine ⟨5454003137206929832910039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14544008365885146221093437 5454003137206929832910039)
          ·
            refine ⟨8181004705810394749365059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5454003137206929832910039 8181004705810394749365059)
            ·
              refine ⟨12271507058715592124047589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8181004705810394749365059 12271507058715592124047589)
              ·
                refine ⟨2300907573509173523258923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12271507058715592124047589 2300907573509173523258923)
                ·
                  refine ⟨3451361360263760284888385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2300907573509173523258923 3451361360263760284888385)
                  ·
                    refine ⟨2588521020197820213666289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3451361360263760284888385 2588521020197820213666289)
                    ·
                      refine ⟨1941390765148365160249717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2588521020197820213666289 1941390765148365160249717)
                      ·
                        rfl

theorem cell23_3780845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_3780845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780845 prefixEnd_3780845 := by exact prefixLift 3780845
  have htrace : WordTrace (prefixWord ++ tailWord_3780845) baseStart_3780845 baseEnd_3780845 := by
    simpa [prefixWord, tailWord_3780845, baseEnd_3780845] using wordTrace_append hprefix tailTrace_3780845
  have hstable : (prefixWord ++ tailWord_3780845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780845).length < 2 ^ (prefixWord ++ tailWord_3780845).sum := by decide
  have hdescent : baseEnd_3780845 < baseStart_3780845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780897 : List Nat := [1, 2, 3, 2, 1, 1, 3, 2, 2, 2, 4]
def baseStart_3780897 : Nat := 118140960795 + 3780897 * 2 ^ 59
def prefixEnd_3780897 : Nat := 4983230072969 + 3 ^ 40 * 3780897 * 2
def baseEnd_3780897 : Nat := 1941417466142398956799477

theorem tailTrace_3780897 : CollatzResearch.WordTrace tailWord_3780897 prefixEnd_3780897 1941417466142398956799477 := by
  unfold tailWord_3780897
  simp only [CollatzResearch.WordTrace]
  refine ⟨137900642583463369643852945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91933761722308913095901963 137900642583463369643852945)
  ·
    refine ⟨103425481937597527232889709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137900642583463369643852945 103425481937597527232889709)
    ·
      refine ⟨38784555726599072712333641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103425481937597527232889709 38784555726599072712333641)
      ·
        refine ⟨29088416794949304534250231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38784555726599072712333641 29088416794949304534250231)
        ·
          refine ⟨43632625192423956801375347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29088416794949304534250231 43632625192423956801375347)
          ·
            refine ⟨65448937788635935202063021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43632625192423956801375347 65448937788635935202063021)
            ·
              refine ⟨24543351670738475700773633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65448937788635935202063021 24543351670738475700773633)
              ·
                refine ⟨18407513753053856775580225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24543351670738475700773633 18407513753053856775580225)
                ·
                  refine ⟨13805635314790392581685169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18407513753053856775580225 13805635314790392581685169)
                  ·
                    refine ⟨10354226486092794436263877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13805635314790392581685169 10354226486092794436263877)
                    ·
                      refine ⟨1941417466142398956799477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10354226486092794436263877 1941417466142398956799477)
                      ·
                        rfl

theorem cell23_3780897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_3780897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780897 prefixEnd_3780897 := by exact prefixLift 3780897
  have htrace : WordTrace (prefixWord ++ tailWord_3780897) baseStart_3780897 baseEnd_3780897 := by
    simpa [prefixWord, tailWord_3780897, baseEnd_3780897] using wordTrace_append hprefix tailTrace_3780897
  have hstable : (prefixWord ++ tailWord_3780897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780897).length < 2 ^ (prefixWord ++ tailWord_3780897).sum := by decide
  have hdescent : baseEnd_3780897 < baseStart_3780897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780937 : List Nat := [1, 2, 1, 1, 2, 3, 1, 5, 2, 5]
def baseStart_3780937 : Nat := 118140960795 + 3780937 * 2 ^ 59
def prefixEnd_3780937 : Nat := 4983230072969 + 3 ^ 40 * 3780937 * 2
def baseEnd_3780937 : Nat := 647146001789526266766431

theorem tailTrace_3780937 : CollatzResearch.WordTrace tailWord_3780937 prefixEnd_3780937 647146001789526266766431 := by
  unfold tailWord_3780937
  simp only [CollatzResearch.WordTrace]
  refine ⟨137902101503318456475309065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91934734335545637650206043 137902101503318456475309065)
  ·
    refine ⟨103426576127488842356481799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137902101503318456475309065 103426576127488842356481799)
    ·
      refine ⟨155139864191233263534722699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103426576127488842356481799 155139864191233263534722699)
      ·
        refine ⟨232709796286849895302084049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155139864191233263534722699 232709796286849895302084049)
        ·
          refine ⟨174532347215137421476563037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232709796286849895302084049 174532347215137421476563037)
          ·
            refine ⟨65449630205676533053711139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174532347215137421476563037 65449630205676533053711139)
            ·
              refine ⟨98174445308514799580566709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65449630205676533053711139 98174445308514799580566709)
              ·
                refine ⟨9203854247673262460678129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98174445308514799580566709 9203854247673262460678129)
                ·
                  refine ⟨6902890685754946845508597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9203854247673262460678129 6902890685754946845508597)
                  ·
                    refine ⟨647146001789526266766431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6902890685754946845508597 647146001789526266766431)
                    ·
                      rfl

theorem cell23_3780937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 5].length) (baseStart_3780937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3780937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3780937 prefixEnd_3780937 := by exact prefixLift 3780937
  have htrace : WordTrace (prefixWord ++ tailWord_3780937) baseStart_3780937 baseEnd_3780937 := by
    simpa [prefixWord, tailWord_3780937, baseEnd_3780937] using wordTrace_append hprefix tailTrace_3780937
  have hstable : (prefixWord ++ tailWord_3780937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780937).length < 2 ^ (prefixWord ++ tailWord_3780937).sum := by decide
  have hdescent : baseEnd_3780937 < baseStart_3780937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781017 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 1, 2, 6]
def baseStart_3781017 : Nat := 118140960795 + 3781017 * 2 ^ 59
def prefixEnd_3781017 : Nat := 4983230072969 + 3 ^ 40 * 3781017 * 2
def baseEnd_3781017 : Nat := 1941479083820938487298925

theorem tailTrace_3781017 : CollatzResearch.WordTrace tailWord_3781017 prefixEnd_3781017 1941479083820938487298925 := by
  unfold tailWord_3781017
  simp only [CollatzResearch.WordTrace]
  refine ⟨137905019343028630138221305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91936679562019086758814203 137905019343028630138221305)
  ·
    refine ⟨103428764507271472603665979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137905019343028630138221305 103428764507271472603665979)
    ·
      refine ⟨155143146760907208905498969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103428764507271472603665979 155143146760907208905498969)
      ·
        refine ⟨116357360070680406679124227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155143146760907208905498969 116357360070680406679124227)
        ·
          refine ⟨174536040106020610018686341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116357360070680406679124227 174536040106020610018686341)
          ·
            refine ⟨32725507519878864378503689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174536040106020610018686341 32725507519878864378503689)
            ·
              refine ⟨24544130639909148283877767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32725507519878864378503689 24544130639909148283877767)
              ·
                refine ⟨36816195959863722425816651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24544130639909148283877767 36816195959863722425816651)
                ·
                  refine ⟨55224293939795583638724977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36816195959863722425816651 55224293939795583638724977)
                  ·
                    refine ⟨41418220454846687729043733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55224293939795583638724977 41418220454846687729043733)
                    ·
                      refine ⟨1941479083820938487298925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41418220454846687729043733 1941479083820938487298925)
                      ·
                        rfl

theorem cell23_3781017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_3781017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781017 prefixEnd_3781017 := by exact prefixLift 3781017
  have htrace : WordTrace (prefixWord ++ tailWord_3781017) baseStart_3781017 baseEnd_3781017 := by
    simpa [prefixWord, tailWord_3781017, baseEnd_3781017] using wordTrace_append hprefix tailTrace_3781017
  have hstable : (prefixWord ++ tailWord_3781017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781017).length < 2 ^ (prefixWord ++ tailWord_3781017).sum := by decide
  have hdescent : baseEnd_3781017 < baseStart_3781017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781018 : List Nat := [3, 1, 1, 4, 1, 3, 1, 4, 1, 4]
def baseStart_3781018 : Nat := 118140960795 + 3781018 * 2 ^ 59
def prefixEnd_3781018 : Nat := 4983230072969 + 3 ^ 40 * 3781018 * 2
def baseEnd_3781018 : Nat := 647159865767197661128807

theorem tailTrace_3781018 : CollatzResearch.WordTrace tailWord_3781018 prefixEnd_3781018 647159865767197661128807 := by
  unfold tailWord_3781018
  simp only [CollatzResearch.WordTrace]
  refine ⟨34476263954006251827251927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91936703877350004872671805 34476263954006251827251927)
  ·
    refine ⟨51714395931009377740877891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34476263954006251827251927 51714395931009377740877891)
    ·
      refine ⟨77571593896514066611316837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51714395931009377740877891 77571593896514066611316837)
      ·
        refine ⟨14544673855596387489621907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77571593896514066611316837 14544673855596387489621907)
        ·
          refine ⟨21817010783394581234432861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14544673855596387489621907 21817010783394581234432861)
          ·
            refine ⟨8181379043772967962912323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21817010783394581234432861 8181379043772967962912323)
            ·
              refine ⟨12272068565659451944368485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8181379043772967962912323 12272068565659451944368485)
              ·
                refine ⟨2301012856061147239569091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12272068565659451944368485 2301012856061147239569091)
                ·
                  refine ⟨3451519284091720859353637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2301012856061147239569091 3451519284091720859353637)
                  ·
                    refine ⟨647159865767197661128807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3451519284091720859353637 647159865767197661128807)
                    ·
                      rfl

theorem cell23_3781018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 4, 1, 4].length) (baseStart_3781018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781018 prefixEnd_3781018 := by exact prefixLift 3781018
  have htrace : WordTrace (prefixWord ++ tailWord_3781018) baseStart_3781018 baseEnd_3781018 := by
    simpa [prefixWord, tailWord_3781018, baseEnd_3781018] using wordTrace_append hprefix tailTrace_3781018
  have hstable : (prefixWord ++ tailWord_3781018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781018).length < 2 ^ (prefixWord ++ tailWord_3781018).sum := by decide
  have hdescent : baseEnd_3781018 < baseStart_3781018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781041 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 5, 1, 3]
def baseStart_3781041 : Nat := 118140960795 + 3781041 * 2 ^ 59
def prefixEnd_3781041 : Nat := 4983230072969 + 3 ^ 40 * 3781041 * 2
def baseEnd_3781041 : Nat := 1941491407356646393398815

theorem tailTrace_3781041 : CollatzResearch.WordTrace tailWord_3781041 prefixEnd_3781041 1941491407356646393398815 := by
  unfold tailWord_3781041
  simp only [CollatzResearch.WordTrace]
  refine ⟨137905894694941682237094977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91937263129961121491396651 137905894694941682237094977)
  ·
    refine ⟨103429421021206261677821233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137905894694941682237094977 103429421021206261677821233)
    ·
      refine ⟨77572065765904696258365925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103429421021206261677821233 77572065765904696258365925)
      ·
        refine ⟨14544762331107130548443611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77572065765904696258365925 14544762331107130548443611)
        ·
          refine ⟨21817143496660695822665417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14544762331107130548443611 21817143496660695822665417)
          ·
            refine ⟨16362857622495521866999063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21817143496660695822665417 16362857622495521866999063)
            ·
              refine ⟨24544286433743282800498595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16362857622495521866999063 24544286433743282800498595)
              ·
                refine ⟨36816429650614924200747893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24544286433743282800498595 36816429650614924200747893)
                ·
                  refine ⟨3451540279745149143820115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36816429650614924200747893 3451540279745149143820115)
                  ·
                    refine ⟨5177310419617723715730173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3451540279745149143820115 5177310419617723715730173)
                    ·
                      refine ⟨1941491407356646393398815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5177310419617723715730173 1941491407356646393398815)
                      ·
                        rfl

theorem cell23_3781041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_3781041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781041 prefixEnd_3781041 := by exact prefixLift 3781041
  have htrace : WordTrace (prefixWord ++ tailWord_3781041) baseStart_3781041 baseEnd_3781041 := by
    simpa [prefixWord, tailWord_3781041, baseEnd_3781041] using wordTrace_append hprefix tailTrace_3781041
  have hstable : (prefixWord ++ tailWord_3781041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781041).length < 2 ^ (prefixWord ++ tailWord_3781041).sum := by decide
  have hdescent : baseEnd_3781041 < baseStart_3781041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781045 : List Nat := [1, 3, 3, 2, 4, 1, 1, 1, 2, 2, 3]
def baseStart_3781045 : Nat := 118140960795 + 3781045 * 2 ^ 59
def prefixEnd_3781045 : Nat := 4983230072969 + 3 ^ 40 * 3781045 * 2
def baseEnd_3781045 : Nat := 1941493461279264377748797

theorem tailTrace_3781045 : CollatzResearch.WordTrace tailWord_3781045 prefixEnd_3781045 1941493461279264377748797 := by
  unfold tailWord_3781045
  simp only [CollatzResearch.WordTrace]
  refine ⟨137906040586927190920240589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91937360391284793946827059 137906040586927190920240589)
  ·
    refine ⟨51714765220097696595090221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137906040586927190920240589 51714765220097696595090221)
    ·
      refine ⟨19393036957536636223158833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51714765220097696595090221 19393036957536636223158833)
      ·
        refine ⟨14544777718152477167369125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19393036957536636223158833 14544777718152477167369125)
        ·
          refine ⟨2727145822153589468881711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14544777718152477167369125 2727145822153589468881711)
          ·
            refine ⟨4090718733230384203322567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2727145822153589468881711 4090718733230384203322567)
            ·
              refine ⟨6136078099845576304983851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4090718733230384203322567 6136078099845576304983851)
              ·
                refine ⟨9204117149768364457475777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6136078099845576304983851 9204117149768364457475777)
                ·
                  refine ⟨6903087862326273343106833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9204117149768364457475777 6903087862326273343106833)
                  ·
                    refine ⟨5177315896744705007330125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6903087862326273343106833 5177315896744705007330125)
                    ·
                      refine ⟨1941493461279264377748797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5177315896744705007330125 1941493461279264377748797)
                      ·
                        rfl

theorem cell23_3781045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_3781045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781045 prefixEnd_3781045 := by exact prefixLift 3781045
  have htrace : WordTrace (prefixWord ++ tailWord_3781045) baseStart_3781045 baseEnd_3781045 := by
    simpa [prefixWord, tailWord_3781045, baseEnd_3781045] using wordTrace_append hprefix tailTrace_3781045
  have hstable : (prefixWord ++ tailWord_3781045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781045).length < 2 ^ (prefixWord ++ tailWord_3781045).sum := by decide
  have hdescent : baseEnd_3781045 < baseStart_3781045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781098 : List Nat := [3, 1, 3, 1, 3, 2, 2, 2, 1, 1, 4]
def baseStart_3781098 : Nat := 118140960795 + 3781098 * 2 ^ 59
def prefixEnd_3781098 : Nat := 4983230072969 + 3 ^ 40 * 3781098 * 2
def baseEnd_3781098 : Nat := 1941520675753952670386053

theorem tailTrace_3781098 : CollatzResearch.WordTrace tailWord_3781098 prefixEnd_3781098 1941520675753952670386053 := by
  unfold tailWord_3781098
  simp only [CollatzResearch.WordTrace]
  refine ⟨34476993413933795242979987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91938649103823453981279965 34476993413933795242979987)
  ·
    refine ⟨51715490120900692864469981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34476993413933795242979987 51715490120900692864469981)
    ·
      refine ⟨19393308795337759824176243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51715490120900692864469981 19393308795337759824176243)
      ·
        refine ⟨29089963193006639736264365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19393308795337759824176243 29089963193006639736264365)
        ·
          refine ⟨10908736197377489901099137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29089963193006639736264365 10908736197377489901099137)
          ·
            refine ⟨8181552148033117425824353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10908736197377489901099137 8181552148033117425824353)
            ·
              refine ⟨6136164111024838069368265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8181552148033117425824353 6136164111024838069368265)
              ·
                refine ⟨4602123083268628552026199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6136164111024838069368265 4602123083268628552026199)
                ·
                  refine ⟨6903184624902942828039299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4602123083268628552026199 6903184624902942828039299)
                  ·
                    refine ⟨10354776937354414242058949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6903184624902942828039299 10354776937354414242058949)
                    ·
                      refine ⟨1941520675753952670386053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10354776937354414242058949 1941520675753952670386053)
                      ·
                        rfl

theorem cell23_3781098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_3781098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781098 prefixEnd_3781098 := by exact prefixLift 3781098
  have htrace : WordTrace (prefixWord ++ tailWord_3781098) baseStart_3781098 baseEnd_3781098 := by
    simpa [prefixWord, tailWord_3781098, baseEnd_3781098] using wordTrace_append hprefix tailTrace_3781098
  have hstable : (prefixWord ++ tailWord_3781098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781098).length < 2 ^ (prefixWord ++ tailWord_3781098).sum := by decide
  have hdescent : baseEnd_3781098 < baseStart_3781098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781109 : List Nat := [1, 3, 5, 1, 2, 2, 1, 3, 1, 1, 3]
def baseStart_3781109 : Nat := 118140960795 + 3781109 * 2 ^ 59
def prefixEnd_3781109 : Nat := 4983230072969 + 3 ^ 40 * 3781109 * 2
def baseEnd_3781109 : Nat := 1941526324041152127348503

theorem tailTrace_3781109 : CollatzResearch.WordTrace tailWord_3781109 prefixEnd_3781109 1941526324041152127348503 := by
  unfold tailWord_3781109
  simp only [CollatzResearch.WordTrace]
  refine ⟨137908374858695329850570381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91938916572463553233713587 137908374858695329850570381)
  ·
    refine ⟨51715640572010748693963893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137908374858695329850570381 51715640572010748693963893)
    ·
      refine ⟨4848341303626007690059115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51715640572010748693963893 4848341303626007690059115)
      ·
        refine ⟨7272511955439011535088673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4848341303626007690059115 7272511955439011535088673)
        ·
          refine ⟨5454383966579258651316505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7272511955439011535088673 5454383966579258651316505)
          ·
            refine ⟨4090787974934443988487379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5454383966579258651316505 4090787974934443988487379)
            ·
              refine ⟨6136181962401665982731069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4090787974934443988487379 6136181962401665982731069)
              ·
                refine ⟨2301068235900624743524151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6136181962401665982731069 2301068235900624743524151)
                ·
                  refine ⟨3451602353850937115286227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2301068235900624743524151 3451602353850937115286227)
                  ·
                    refine ⟨5177403530776405672929341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3451602353850937115286227 5177403530776405672929341)
                    ·
                      refine ⟨1941526324041152127348503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5177403530776405672929341 1941526324041152127348503)
                      ·
                        rfl

theorem cell23_3781109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_3781109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781109 prefixEnd_3781109 := by exact prefixLift 3781109
  have htrace : WordTrace (prefixWord ++ tailWord_3781109) baseStart_3781109 baseEnd_3781109 := by
    simpa [prefixWord, tailWord_3781109, baseEnd_3781109] using wordTrace_append hprefix tailTrace_3781109
  have hstable : (prefixWord ++ tailWord_3781109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781109).length < 2 ^ (prefixWord ++ tailWord_3781109).sum := by decide
  have hdescent : baseEnd_3781109 < baseStart_3781109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781152 : List Nat := [2, 1, 1, 6, 3, 1, 1, 2, 1, 2, 3]
def baseStart_3781152 : Nat := 118140960795 + 3781152 * 2 ^ 59
def prefixEnd_3781152 : Nat := 4983230072969 + 3 ^ 40 * 3781152 * 2
def baseEnd_3781152 : Nat := 1941548403709295459110805

theorem tailTrace_3781152 : CollatzResearch.WordTrace tailWord_3781152 prefixEnd_3781152 1941548403709295459110805 := by
  unfold tailWord_3781152
  simp only [CollatzResearch.WordTrace]
  refine ⟨68954971598769774097192855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91939962131693032129590473 68954971598769774097192855)
  ·
    refine ⟨103432457398154661145789283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68954971598769774097192855 103432457398154661145789283)
    ·
      refine ⟨155148686097231991718683925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103432457398154661145789283 155148686097231991718683925)
      ·
        refine ⟨7272594660807749611813309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 155148686097231991718683925 7272594660807749611813309)
        ·
          refine ⟨2727222997802906104429991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7272594660807749611813309 2727222997802906104429991)
          ·
            refine ⟨4090834496704359156644987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2727222997802906104429991 4090834496704359156644987)
            ·
              refine ⟨6136251745056538734967481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4090834496704359156644987 6136251745056538734967481)
              ·
                refine ⟨4602188808792404051225611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6136251745056538734967481 4602188808792404051225611)
                ·
                  refine ⟨6903283213188606076838417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4602188808792404051225611 6903283213188606076838417)
                  ·
                    refine ⟨5177462409891454557628813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6903283213188606076838417 5177462409891454557628813)
                    ·
                      refine ⟨1941548403709295459110805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5177462409891454557628813 1941548403709295459110805)
                      ·
                        rfl

theorem cell23_3781152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_3781152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781152 prefixEnd_3781152 := by exact prefixLift 3781152
  have htrace : WordTrace (prefixWord ++ tailWord_3781152) baseStart_3781152 baseEnd_3781152 := by
    simpa [prefixWord, tailWord_3781152, baseEnd_3781152] using wordTrace_append hprefix tailTrace_3781152
  have hstable : (prefixWord ++ tailWord_3781152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781152).length < 2 ^ (prefixWord ++ tailWord_3781152).sum := by decide
  have hdescent : baseEnd_3781152 < baseStart_3781152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781154 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 1, 2, 8]
def baseStart_3781154 : Nat := 118140960795 + 3781154 * 2 ^ 59
def prefixEnd_3781154 : Nat := 4983230072969 + 3 ^ 40 * 3781154 * 2
def baseEnd_3781154 : Nat := 1941549430670604451285795

theorem tailTrace_3781154 : CollatzResearch.WordTrace tailWord_3781154 prefixEnd_3781154 1941549430670604451285795 := by
  unfold tailWord_3781154
  simp only [CollatzResearch.WordTrace]
  refine ⟨34477504035883075633989629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91940010762354868357305677 34477504035883075633989629)
  ·
    refine ⟨12929064013456153362746111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34477504035883075633989629 12929064013456153362746111)
    ·
      refine ⟨19393596020184230044119167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12929064013456153362746111 19393596020184230044119167)
      ·
        refine ⟨29090394030276345066178751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19393596020184230044119167 29090394030276345066178751)
        ·
          refine ⟨43635591045414517599268127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29090394030276345066178751 43635591045414517599268127)
          ·
            refine ⟨65453386568121776398902191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43635591045414517599268127 65453386568121776398902191)
            ·
              refine ⟨98180079852182664598353287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65453386568121776398902191 98180079852182664598353287)
              ·
                refine ⟨147270119778273996897529931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98180079852182664598353287 147270119778273996897529931)
                ·
                  refine ⟨220905179667410995346294897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147270119778273996897529931 220905179667410995346294897)
                  ·
                    refine ⟨165678884750558246509721173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 220905179667410995346294897 165678884750558246509721173)
                    ·
                      refine ⟨1941549430670604451285795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 165678884750558246509721173 1941549430670604451285795)
                      ·
                        rfl

theorem cell23_3781154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_3781154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781154 prefixEnd_3781154 := by exact prefixLift 3781154
  have htrace : WordTrace (prefixWord ++ tailWord_3781154) baseStart_3781154 baseEnd_3781154 := by
    simpa [prefixWord, tailWord_3781154, baseEnd_3781154] using wordTrace_append hprefix tailTrace_3781154
  have hstable : (prefixWord ++ tailWord_3781154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781154).length < 2 ^ (prefixWord ++ tailWord_3781154).sum := by decide
  have hdescent : baseEnd_3781154 < baseStart_3781154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781175 : List Nat := [1, 1, 3, 1, 2, 3, 5, 1, 1, 3, 2]
def baseStart_3781175 : Nat := 118140960795 + 3781175 * 2 ^ 59
def prefixEnd_3781175 : Nat := 4983230072969 + 3 ^ 40 * 3781175 * 2
def baseEnd_3781175 : Nat := 1941560213764348869123199

theorem tailTrace_3781175 : CollatzResearch.WordTrace tailWord_3781175 prefixEnd_3781175 1941560213764348869123199 := by
  unfold tailWord_3781175
  simp only [CollatzResearch.WordTrace]
  refine ⟨137910782076456223122472979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91940521384304148748315319 137910782076456223122472979)
  ·
    refine ⟨206866173114684334683709469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137910782076456223122472979 206866173114684334683709469)
    ·
      refine ⟨77574814918006625506391051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206866173114684334683709469 77574814918006625506391051)
      ·
        refine ⟨116362222377009938259586577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77574814918006625506391051 116362222377009938259586577)
        ·
          refine ⟨87271666782757453694689933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116362222377009938259586577 87271666782757453694689933)
          ·
            refine ⟨32726875043534045135508725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87271666782757453694689933 32726875043534045135508725)
            ·
              refine ⟨3068144535331316731453943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32726875043534045135508725 3068144535331316731453943)
              ·
                refine ⟨4602216802996975097180915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3068144535331316731453943 4602216802996975097180915)
                ·
                  refine ⟨6903325204495462645771373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4602216802996975097180915 6903325204495462645771373)
                  ·
                    refine ⟨2588746951685798492164265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6903325204495462645771373 2588746951685798492164265)
                    ·
                      refine ⟨1941560213764348869123199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2588746951685798492164265 1941560213764348869123199)
                      ·
                        rfl

theorem cell23_3781175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 1, 3, 2].length) (baseStart_3781175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781175 prefixEnd_3781175 := by exact prefixLift 3781175
  have htrace : WordTrace (prefixWord ++ tailWord_3781175) baseStart_3781175 baseEnd_3781175 := by
    simpa [prefixWord, tailWord_3781175, baseEnd_3781175] using wordTrace_append hprefix tailTrace_3781175
  have hstable : (prefixWord ++ tailWord_3781175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781175).length < 2 ^ (prefixWord ++ tailWord_3781175).sum := by decide
  have hdescent : baseEnd_3781175 < baseStart_3781175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781191 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 2, 4, 3]
def baseStart_3781191 : Nat := 118140960795 + 3781191 * 2 ^ 59
def prefixEnd_3781191 : Nat := 4983230072969 + 3 ^ 40 * 3781191 * 2
def baseEnd_3781191 : Nat := 1941568429454820806523125

theorem tailTrace_3781191 : CollatzResearch.WordTrace tailWord_3781191 prefixEnd_3781191 1941568429454820806523125 := by
  unfold tailWord_3781191
  simp only [CollatzResearch.WordTrace]
  refine ⟨137911365644398257855055427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91940910429598838570036951 137911365644398257855055427)
  ·
    refine ⟨206867048466597386782583141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137911365644398257855055427 206867048466597386782583141)
    ·
      refine ⟨38787571587487010021734339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206867048466597386782583141 38787571587487010021734339)
      ·
        refine ⟨58181357381230515032601509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38787571587487010021734339 58181357381230515032601509)
        ·
          refine ⟨10909004508980721568612783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58181357381230515032601509 10909004508980721568612783)
          ·
            refine ⟨16363506763471082352919175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10909004508980721568612783 16363506763471082352919175)
            ·
              refine ⟨24545260145206623529378763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16363506763471082352919175 24545260145206623529378763)
              ·
                refine ⟨36817890217809935294068145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24545260145206623529378763 36817890217809935294068145)
                ·
                  refine ⟨27613417663357451470551109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36817890217809935294068145 27613417663357451470551109)
                  ·
                    refine ⟨5177515811879522150728333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27613417663357451470551109 5177515811879522150728333)
                    ·
                      refine ⟨1941568429454820806523125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5177515811879522150728333 1941568429454820806523125)
                      ·
                        rfl

theorem cell23_3781191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_3781191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781191 prefixEnd_3781191 := by exact prefixLift 3781191
  have htrace : WordTrace (prefixWord ++ tailWord_3781191) baseStart_3781191 baseEnd_3781191 := by
    simpa [prefixWord, tailWord_3781191, baseEnd_3781191] using wordTrace_append hprefix tailTrace_3781191
  have hstable : (prefixWord ++ tailWord_3781191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781191).length < 2 ^ (prefixWord ++ tailWord_3781191).sum := by decide
  have hdescent : baseEnd_3781191 < baseStart_3781191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781201 : List Nat := [1, 2, 2, 1, 3, 4, 1, 1, 2, 2, 4]
def baseStart_3781201 : Nat := 118140960795 + 3781201 * 2 ^ 59
def prefixEnd_3781201 : Nat := 4983230072969 + 3 ^ 40 * 3781201 * 2
def baseEnd_3781201 : Nat := 1941573564261365767398079

theorem tailTrace_3781201 : CollatzResearch.WordTrace tailWord_3781201 prefixEnd_3781201 1941573564261365767398079 := by
  unfold tailWord_3781201
  simp only [CollatzResearch.WordTrace]
  refine ⟨137911730374362029562919457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91941153582908019708612971 137911730374362029562919457)
  ·
    refine ⟨103433797780771522172189593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137911730374362029562919457 103433797780771522172189593)
    ·
      refine ⟨77575348335578641629142195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103433797780771522172189593 77575348335578641629142195)
      ·
        refine ⟨116363022503367962443713293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77575348335578641629142195 116363022503367962443713293)
        ·
          refine ⟨43636133438762985916392485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116363022503367962443713293 43636133438762985916392485)
          ·
            refine ⟨8181775019768059859323591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43636133438762985916392485 8181775019768059859323591)
            ·
              refine ⟨12272662529652089788985387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8181775019768059859323591 12272662529652089788985387)
              ·
                refine ⟨18408993794478134683478081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12272662529652089788985387 18408993794478134683478081)
                ·
                  refine ⟨13806745345858601012608561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18408993794478134683478081 13806745345858601012608561)
                  ·
                    refine ⟨10355059009393950759456421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13806745345858601012608561 10355059009393950759456421)
                    ·
                      refine ⟨1941573564261365767398079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10355059009393950759456421 1941573564261365767398079)
                      ·
                        rfl

theorem cell23_3781201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_3781201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781201 prefixEnd_3781201 := by exact prefixLift 3781201
  have htrace : WordTrace (prefixWord ++ tailWord_3781201) baseStart_3781201 baseEnd_3781201 := by
    simpa [prefixWord, tailWord_3781201, baseEnd_3781201] using wordTrace_append hprefix tailTrace_3781201
  have hstable : (prefixWord ++ tailWord_3781201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781201).length < 2 ^ (prefixWord ++ tailWord_3781201).sum := by decide
  have hdescent : baseEnd_3781201 < baseStart_3781201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781205 : List Nat := [1, 3, 2, 2, 1, 1, 4, 3, 2, 2, 2]
def baseStart_3781205 : Nat := 118140960795 + 3781205 * 2 ^ 59
def prefixEnd_3781205 : Nat := 4983230072969 + 3 ^ 40 * 3781205 * 2
def baseEnd_3781205 : Nat := 1941575618183983751748061

theorem tailTrace_3781205 : CollatzResearch.WordTrace tailWord_3781205 prefixEnd_3781205 1941575618183983751748061 := by
  unfold tailWord_3781205
  simp only [CollatzResearch.WordTrace]
  refine ⟨137911876266347538246065069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91941250844231692164043379 137911876266347538246065069)
  ·
    refine ⟨51716953599880326842274401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137911876266347538246065069 51716953599880326842274401)
    ·
      refine ⟨38787715199910245131705801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51716953599880326842274401 38787715199910245131705801)
      ·
        refine ⟨29090786399932683848779351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38787715199910245131705801 29090786399932683848779351)
        ·
          refine ⟨43636179599899025773169027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29090786399932683848779351 43636179599899025773169027)
          ·
            refine ⟨65454269399848538659753541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43636179599899025773169027 65454269399848538659753541)
            ·
              refine ⟨12272675512471600998703789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65454269399848538659753541 12272675512471600998703789)
              ·
                refine ⟨4602253317176850374513921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12272675512471600998703789 4602253317176850374513921)
                ·
                  refine ⟨3451689987882637780885441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4602253317176850374513921 3451689987882637780885441)
                  ·
                    refine ⟨2588767490911978335664081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3451689987882637780885441 2588767490911978335664081)
                    ·
                      refine ⟨1941575618183983751748061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2588767490911978335664081 1941575618183983751748061)
                      ·
                        rfl

theorem cell23_3781205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_3781205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781205 prefixEnd_3781205 := by exact prefixLift 3781205
  have htrace : WordTrace (prefixWord ++ tailWord_3781205) baseStart_3781205 baseEnd_3781205 := by
    simpa [prefixWord, tailWord_3781205, baseEnd_3781205] using wordTrace_append hprefix tailTrace_3781205
  have hstable : (prefixWord ++ tailWord_3781205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781205).length < 2 ^ (prefixWord ++ tailWord_3781205).sum := by decide
  have hdescent : baseEnd_3781205 < baseStart_3781205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781278 : List Nat := [4, 3, 1, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_3781278 : Nat := 118140960795 + 3781278 * 2 ^ 59
def prefixEnd_3781278 : Nat := 4983230072969 + 3 ^ 40 * 3781278 * 2
def baseEnd_3781278 : Nat := 1941613102271761966135225

theorem tailTrace_3781278 : CollatzResearch.WordTrace tailWord_3781278 prefixEnd_3781278 1941613102271761966135225 := by
  unfold tailWord_3781278
  simp only [CollatzResearch.WordTrace]
  refine ⟨17239317349385383964184061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91943025863388714475648325 17239317349385383964184061)
  ·
    refine ⟨6464744006019518986569023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17239317349385383964184061 6464744006019518986569023)
    ·
      refine ⟨9697116009029278479853535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6464744006019518986569023 9697116009029278479853535)
      ·
        refine ⟨14545674013543917719780303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9697116009029278479853535 14545674013543917719780303)
        ·
          refine ⟨21818511020315876579670455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14545674013543917719780303 21818511020315876579670455)
          ·
            refine ⟨32727766530473814869505683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21818511020315876579670455 32727766530473814869505683)
            ·
              refine ⟨49091649795710722304258525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32727766530473814869505683 49091649795710722304258525)
              ·
                refine ⟨18409368673391520864096947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49091649795710722304258525 18409368673391520864096947)
                ·
                  refine ⟨27614053010087281296145421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18409368673391520864096947 27614053010087281296145421)
                  ·
                    refine ⟨10355269878782730486054533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27614053010087281296145421 10355269878782730486054533)
                    ·
                      refine ⟨1941613102271761966135225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10355269878782730486054533 1941613102271761966135225)
                      ·
                        rfl

theorem cell23_3781278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_3781278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781278 prefixEnd_3781278 := by exact prefixLift 3781278
  have htrace : WordTrace (prefixWord ++ tailWord_3781278) baseStart_3781278 baseEnd_3781278 := by
    simpa [prefixWord, tailWord_3781278, baseEnd_3781278] using wordTrace_append hprefix tailTrace_3781278
  have hstable : (prefixWord ++ tailWord_3781278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781278).length < 2 ^ (prefixWord ++ tailWord_3781278).sum := by decide
  have hdescent : baseEnd_3781278 < baseStart_3781278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781332 : List Nat := [2, 4, 1, 3, 2, 1, 2, 1, 2, 2, 3]
def baseStart_3781332 : Nat := 118140960795 + 3781332 * 2 ^ 59
def prefixEnd_3781332 : Nat := 4983230072969 + 3 ^ 40 * 3781332 * 2
def baseEnd_3781332 : Nat := 1941640830227104754859977

theorem tailTrace_3781332 : CollatzResearch.WordTrace tailWord_3781332 prefixEnd_3781332 1941640830227104754859977 := by
  unfold tailWord_3781332
  simp only [CollatzResearch.WordTrace]
  refine ⟨68958254168443719467969125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91944338891258292623958833 68958254168443719467969125)
  ·
    refine ⟨12929672656583197400244211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68958254168443719467969125 12929672656583197400244211)
    ·
      refine ⟨19394508984874796100366317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12929672656583197400244211 19394508984874796100366317)
      ·
        refine ⟨7272940869328048537637369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19394508984874796100366317 7272940869328048537637369)
        ·
          refine ⟨5454705651996036403228027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7272940869328048537637369 5454705651996036403228027)
          ·
            refine ⟨8182058477994054604842041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5454705651996036403228027 8182058477994054604842041)
            ·
              refine ⟨6136543858495540953631531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8182058477994054604842041 6136543858495540953631531)
              ·
                refine ⟨9204815787743311430447297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6136543858495540953631531 9204815787743311430447297)
                ·
                  refine ⟨6903611840807483572835473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9204815787743311430447297 6903611840807483572835473)
                  ·
                    refine ⟨5177708880605612679626605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6903611840807483572835473 5177708880605612679626605)
                    ·
                      refine ⟨1941640830227104754859977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5177708880605612679626605 1941640830227104754859977)
                      ·
                        rfl

theorem cell23_3781332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_3781332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781332 prefixEnd_3781332 := by exact prefixLift 3781332
  have htrace : WordTrace (prefixWord ++ tailWord_3781332) baseStart_3781332 baseEnd_3781332 := by
    simpa [prefixWord, tailWord_3781332, baseEnd_3781332] using wordTrace_append hprefix tailTrace_3781332
  have hstable : (prefixWord ++ tailWord_3781332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781332).length < 2 ^ (prefixWord ++ tailWord_3781332).sum := by decide
  have hdescent : baseEnd_3781332 < baseStart_3781332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781361 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 3, 6]
def baseStart_3781361 : Nat := 118140960795 + 3781361 * 2 ^ 59
def prefixEnd_3781361 : Nat := 4983230072969 + 3 ^ 40 * 3781361 * 2
def baseEnd_3781361 : Nat := 647218573722028380465781

theorem tailTrace_3781361 : CollatzResearch.WordTrace tailWord_3781361 prefixEnd_3781361 647218573722028380465781 := by
  unfold tailWord_3781361
  simp only [CollatzResearch.WordTrace]
  refine ⟨137917566053782376888743937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91945044035854917925829291 137917566053782376888743937)
  ·
    refine ⟨103438174540336782666557953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137917566053782376888743937 103438174540336782666557953)
    ·
      refine ⟨77578630905252586999918465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103438174540336782666557953 77578630905252586999918465)
      ·
        refine ⟨58183973178939440249938849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77578630905252586999918465 58183973178939440249938849)
        ·
          refine ⟨43637979884204580187454137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58183973178939440249938849 43637979884204580187454137)
          ·
            refine ⟨32728484913153435140590603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43637979884204580187454137 32728484913153435140590603)
            ·
              refine ⟨49092727369730152710885905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32728484913153435140590603 49092727369730152710885905)
              ·
                refine ⟨36819545527297614533164429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49092727369730152710885905 36819545527297614533164429)
                ·
                  refine ⟨13807329572736605449936661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36819545527297614533164429 13807329572736605449936661)
                  ·
                    refine ⟨647218573722028380465781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13807329572736605449936661 647218573722028380465781)
                    ·
                      rfl

theorem cell23_3781361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 6].length) (baseStart_3781361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781361 prefixEnd_3781361 := by exact prefixLift 3781361
  have htrace : WordTrace (prefixWord ++ tailWord_3781361) baseStart_3781361 baseEnd_3781361 := by
    simpa [prefixWord, tailWord_3781361, baseEnd_3781361] using wordTrace_append hprefix tailTrace_3781361
  have hstable : (prefixWord ++ tailWord_3781361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781361).length < 2 ^ (prefixWord ++ tailWord_3781361).sum := by decide
  have hdescent : baseEnd_3781361 < baseStart_3781361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781381 : List Nat := [1, 3, 1, 1, 2, 1, 1, 5, 1, 1, 6]
def baseStart_3781381 : Nat := 118140960795 + 3781381 * 2 ^ 59
def prefixEnd_3781381 : Nat := 4983230072969 + 3 ^ 40 * 3781381 * 2
def baseEnd_3781381 : Nat := 1941665990779175063147251

theorem tailTrace_3781381 : CollatzResearch.WordTrace tailWord_3781381 prefixEnd_3781381 1941665990779175063147251 := by
  unfold tailWord_3781381
  simp only [CollatzResearch.WordTrace]
  refine ⟨137918295513709920304471997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91945530342473280202981331 137918295513709920304471997)
  ·
    refine ⟨51719360817641220114176999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137918295513709920304471997 51719360817641220114176999)
    ·
      refine ⟨77579041226461830171265499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51719360817641220114176999 77579041226461830171265499)
      ·
        refine ⟨116368561839692745256898249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77579041226461830171265499 116368561839692745256898249)
        ·
          refine ⟨87276421379769558942673687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116368561839692745256898249 87276421379769558942673687)
          ·
            refine ⟨130914632069654338414010531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87276421379769558942673687 130914632069654338414010531)
            ·
              refine ⟨196371948104481507621015797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130914632069654338414010531 196371948104481507621015797)
              ·
                refine ⟨18409870134795141339470231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 196371948104481507621015797 18409870134795141339470231)
                ·
                  refine ⟨27614805202192712009205347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18409870134795141339470231 27614805202192712009205347)
                  ·
                    refine ⟨41422207803289068013808021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27614805202192712009205347 41422207803289068013808021)
                    ·
                      refine ⟨1941665990779175063147251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41422207803289068013808021 1941665990779175063147251)
                      ·
                        rfl

theorem cell23_3781381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_3781381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781381 prefixEnd_3781381 := by exact prefixLift 3781381
  have htrace : WordTrace (prefixWord ++ tailWord_3781381) baseStart_3781381 baseEnd_3781381 := by
    simpa [prefixWord, tailWord_3781381, baseEnd_3781381] using wordTrace_append hprefix tailTrace_3781381
  have hstable : (prefixWord ++ tailWord_3781381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781381).length < 2 ^ (prefixWord ++ tailWord_3781381).sum := by decide
  have hdescent : baseEnd_3781381 < baseStart_3781381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781385 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 5, 2, 2]
def baseStart_3781385 : Nat := 118140960795 + 3781385 * 2 ^ 59
def prefixEnd_3781385 : Nat := 4983230072969 + 3 ^ 40 * 3781385 * 2
def baseEnd_3781385 : Nat := 1941668044701793047497233

theorem tailTrace_3781385 : CollatzResearch.WordTrace tailWord_3781385 prefixEnd_3781385 1941668044701793047497233 := by
  unfold tailWord_3781385
  simp only [CollatzResearch.WordTrace]
  refine ⟨137918441405695428987617609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91945627603796952658411739 137918441405695428987617609)
  ·
    refine ⟨103438831054271571740713207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137918441405695428987617609 103438831054271571740713207)
    ·
      refine ⟨155158246581407357611069811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103438831054271571740713207 155158246581407357611069811)
      ·
        refine ⟨232737369872111036416604717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155158246581407357611069811 232737369872111036416604717)
        ·
          refine ⟨87276513702041638656226769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232737369872111036416604717 87276513702041638656226769)
          ·
            refine ⟨65457385276531228992170077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87276513702041638656226769 65457385276531228992170077)
            ·
              refine ⟨24546519478699210872063779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65457385276531228992170077 24546519478699210872063779)
              ·
                refine ⟨36819779218048816308095669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24546519478699210872063779 36819779218048816308095669)
                ·
                  refine ⟨3451854301692076528883969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36819779218048816308095669 3451854301692076528883969)
                  ·
                    refine ⟨2588890726269057396662977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3451854301692076528883969 2588890726269057396662977)
                    ·
                      refine ⟨1941668044701793047497233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2588890726269057396662977 1941668044701793047497233)
                      ·
                        rfl

theorem cell23_3781385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 5, 2, 2].length) (baseStart_3781385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781385 prefixEnd_3781385 := by exact prefixLift 3781385
  have htrace : WordTrace (prefixWord ++ tailWord_3781385) baseStart_3781385 baseEnd_3781385 := by
    simpa [prefixWord, tailWord_3781385, baseEnd_3781385] using wordTrace_append hprefix tailTrace_3781385
  have hstable : (prefixWord ++ tailWord_3781385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781385).length < 2 ^ (prefixWord ++ tailWord_3781385).sum := by decide
  have hdescent : baseEnd_3781385 < baseStart_3781385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781399 : List Nat := [1, 1, 3, 4, 4, 1, 2, 1, 1, 5]
def baseStart_3781399 : Nat := 118140960795 + 3781399 * 2 ^ 59
def prefixEnd_3781399 : Nat := 4983230072969 + 3 ^ 40 * 3781399 * 2
def baseEnd_3781399 : Nat := 647225077810318664240723

theorem tailTrace_3781399 : CollatzResearch.WordTrace tailWord_3781399 prefixEnd_3781399 647225077810318664240723 := by
  unfold tailWord_3781399
  simp only [CollatzResearch.WordTrace]
  refine ⟨137918952027644709378627251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91945968018429806252418167 137918952027644709378627251)
  ·
    refine ⟨206878428041467064067940877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137918952027644709378627251 206878428041467064067940877)
    ·
      refine ⟨77579410515550149025477829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206878428041467064067940877 77579410515550149025477829)
      ·
        refine ⟨14546139471665652942277093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77579410515550149025477829 14546139471665652942277093)
        ·
          refine ⟨2727401150937309926676955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14546139471665652942277093 2727401150937309926676955)
          ·
            refine ⟨4091101726405964890015433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2727401150937309926676955 4091101726405964890015433)
            ·
              refine ⟨3068326294804473667511575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4091101726405964890015433 3068326294804473667511575)
              ·
                refine ⟨4602489442206710501267363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3068326294804473667511575 4602489442206710501267363)
                ·
                  refine ⟨6903734163310065751901045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4602489442206710501267363 6903734163310065751901045)
                  ·
                    refine ⟨647225077810318664240723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6903734163310065751901045 647225077810318664240723)
                    ·
                      rfl

theorem cell23_3781399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 1, 5].length) (baseStart_3781399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781399 prefixEnd_3781399 := by exact prefixLift 3781399
  have htrace : WordTrace (prefixWord ++ tailWord_3781399) baseStart_3781399 baseEnd_3781399 := by
    simpa [prefixWord, tailWord_3781399, baseEnd_3781399] using wordTrace_append hprefix tailTrace_3781399
  have hstable : (prefixWord ++ tailWord_3781399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781399).length < 2 ^ (prefixWord ++ tailWord_3781399).sum := by decide
  have hdescent : baseEnd_3781399 < baseStart_3781399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781411 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 6]
def baseStart_3781411 : Nat := 118140960795 + 3781411 * 2 ^ 59
def prefixEnd_3781411 : Nat := 4983230072969 + 3 ^ 40 * 3781411 * 2
def baseEnd_3781411 : Nat := 1941681395198809945772113

theorem tailTrace_3781411 : CollatzResearch.WordTrace tailWord_3781411 prefixEnd_3781411 1941681395198809945772113 := by
  unfold tailWord_3781411
  simp only [CollatzResearch.WordTrace]
  refine ⟨137919389703601235428064087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91946259802400823618709391 137919389703601235428064087)
  ·
    refine ⟨206879084555401853142096131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137919389703601235428064087 206879084555401853142096131)
    ·
      refine ⟨310318626833102779713144197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206879084555401853142096131 310318626833102779713144197)
      ·
        refine ⟨58184742531206771196214537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 310318626833102779713144197 58184742531206771196214537)
        ·
          refine ⟨43638556898405078397160903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58184742531206771196214537 43638556898405078397160903)
          ·
            refine ⟨65457835347607617595741355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43638556898405078397160903 65457835347607617595741355)
            ·
              refine ⟨98186753021411426393612033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65457835347607617595741355 98186753021411426393612033)
              ·
                refine ⟨73640064766058569795209025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98186753021411426393612033 73640064766058569795209025)
                ·
                  refine ⟨55230048574543927346406769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73640064766058569795209025 55230048574543927346406769)
                  ·
                    refine ⟨41422536430907945509805077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55230048574543927346406769 41422536430907945509805077)
                    ·
                      refine ⟨1941681395198809945772113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41422536430907945509805077 1941681395198809945772113)
                      ·
                        rfl

theorem cell23_3781411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_3781411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781411 prefixEnd_3781411 := by exact prefixLift 3781411
  have htrace : WordTrace (prefixWord ++ tailWord_3781411) baseStart_3781411 baseEnd_3781411 := by
    simpa [prefixWord, tailWord_3781411, baseEnd_3781411] using wordTrace_append hprefix tailTrace_3781411
  have hstable : (prefixWord ++ tailWord_3781411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781411).length < 2 ^ (prefixWord ++ tailWord_3781411).sum := by decide
  have hdescent : baseEnd_3781411 < baseStart_3781411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781488 : List Nat := [2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 4]
def baseStart_3781488 : Nat := 118140960795 + 3781488 * 2 ^ 59
def prefixEnd_3781488 : Nat := 4983230072969 + 3 ^ 40 * 3781488 * 2
def baseEnd_3781488 : Nat := 1941720933209206144509259

theorem tailTrace_3781488 : CollatzResearch.WordTrace tailWord_3781488 prefixEnd_3781488 1941720933209206144509259 := by
  unfold tailWord_3781488
  simp only [CollatzResearch.WordTrace]
  refine ⟨68961099062161138789308559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91948132082881518385744745 68961099062161138789308559)
  ·
    refine ⟨103441648593241708183962839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68961099062161138789308559 103441648593241708183962839)
    ·
      refine ⟨155162472889862562275944259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103441648593241708183962839 155162472889862562275944259)
      ·
        refine ⟨232743709334793843413916389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155162472889862562275944259 232743709334793843413916389)
        ·
          refine ⟨43639445500273845640109323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232743709334793843413916389 43639445500273845640109323)
          ·
            refine ⟨65459168250410768460163985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43639445500273845640109323 65459168250410768460163985)
            ·
              refine ⟨49094376187808076345122989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65459168250410768460163985 49094376187808076345122989)
              ·
                refine ⟨18410391070428028629421121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49094376187808076345122989 18410391070428028629421121)
                ·
                  refine ⟨13807793302821021472065841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18410391070428028629421121 13807793302821021472065841)
                  ·
                    refine ⟨10355844977115766104049381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13807793302821021472065841 10355844977115766104049381)
                    ·
                      refine ⟨1941720933209206144509259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10355844977115766104049381 1941720933209206144509259)
                      ·
                        rfl

theorem cell23_3781488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 4].length) (baseStart_3781488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781488 prefixEnd_3781488 := by exact prefixLift 3781488
  have htrace : WordTrace (prefixWord ++ tailWord_3781488) baseStart_3781488 baseEnd_3781488 := by
    simpa [prefixWord, tailWord_3781488, baseEnd_3781488] using wordTrace_append hprefix tailTrace_3781488
  have hstable : (prefixWord ++ tailWord_3781488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781488).length < 2 ^ (prefixWord ++ tailWord_3781488).sum := by decide
  have hdescent : baseEnd_3781488 < baseStart_3781488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781548 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 4]
def baseStart_3781548 : Nat := 118140960795 + 3781548 * 2 ^ 59
def prefixEnd_3781548 : Nat := 4983230072969 + 3 ^ 40 * 3781548 * 2
def baseEnd_3781548 : Nat := 1941751742048475909758983

theorem tailTrace_3781548 : CollatzResearch.WordTrace tailWord_3781548 prefixEnd_3781548 1941751742048475909758983 := by
  unfold tailWord_3781548
  simp only [CollatzResearch.WordTrace]
  refine ⟨68962193252052453912900649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91949591002736605217200865 68962193252052453912900649)
  ·
    refine ⟨51721644939039340434675487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68962193252052453912900649 51721644939039340434675487)
    ·
      refine ⟨77582467408559010652013231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51721644939039340434675487 77582467408559010652013231)
      ·
        refine ⟨116373701112838515978019847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77582467408559010652013231 116373701112838515978019847)
        ·
          refine ⟨174560551669257773967029771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116373701112838515978019847 174560551669257773967029771)
          ·
            refine ⟨261840827503886660950544657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174560551669257773967029771 261840827503886660950544657)
            ·
              refine ⟨196380620627914995712908493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261840827503886660950544657 196380620627914995712908493)
              ·
                refine ⟨73642732735468123392340685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196380620627914995712908493 73642732735468123392340685)
                ·
                  refine ⟨27616024775800546272127757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73642732735468123392340685 27616024775800546272127757)
                  ·
                    refine ⟨10356009290925204852047909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27616024775800546272127757 10356009290925204852047909)
                    ·
                      refine ⟨1941751742048475909758983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10356009290925204852047909 1941751742048475909758983)
                      ·
                        rfl

theorem cell23_3781548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_3781548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781548 prefixEnd_3781548 := by exact prefixLift 3781548
  have htrace : WordTrace (prefixWord ++ tailWord_3781548) baseStart_3781548 baseEnd_3781548 := by
    simpa [prefixWord, tailWord_3781548, baseEnd_3781548] using wordTrace_append hprefix tailTrace_3781548
  have hstable : (prefixWord ++ tailWord_3781548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781548).length < 2 ^ (prefixWord ++ tailWord_3781548).sum := by decide
  have hdescent : baseEnd_3781548 < baseStart_3781548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781582 : List Nat := [4, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2]
def baseStart_3781582 : Nat := 118140960795 + 3781582 * 2 ^ 59
def prefixEnd_3781582 : Nat := 4983230072969 + 3 ^ 40 * 3781582 * 2
def baseEnd_3781582 : Nat := 1941769200390728776733827

theorem tailTrace_3781582 : CollatzResearch.WordTrace tailWord_3781582 prefixEnd_3781582 1941769200390728776733827 := by
  unfold tailWord_3781582
  simp only [CollatzResearch.WordTrace]
  refine ⟨17240703323247716454067375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91950417723987821088359333 17240703323247716454067375)
  ·
    refine ⟨25861054984871574681101063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17240703323247716454067375 25861054984871574681101063)
    ·
      refine ⟨38791582477307362021651595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25861054984871574681101063 38791582477307362021651595)
      ·
        refine ⟨58187373715961043032477393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38791582477307362021651595 58187373715961043032477393)
        ·
          refine ⟨43640530286970782274358045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58187373715961043032477393 43640530286970782274358045)
          ·
            refine ⟨16365198857614043352884267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43640530286970782274358045 16365198857614043352884267)
            ·
              refine ⟨24547798286421065029326401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16365198857614043352884267 24547798286421065029326401)
              ·
                refine ⟨18410848714815798771994801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24547798286421065029326401 18410848714815798771994801)
                ·
                  refine ⟨13808136536111849078996101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18410848714815798771994801 13808136536111849078996101)
                  ·
                    refine ⟨2589025600520971702311769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13808136536111849078996101 2589025600520971702311769)
                    ·
                      refine ⟨1941769200390728776733827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2589025600520971702311769 1941769200390728776733827)
                      ·
                        rfl

theorem cell23_3781582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2].length) (baseStart_3781582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781582 prefixEnd_3781582 := by exact prefixLift 3781582
  have htrace : WordTrace (prefixWord ++ tailWord_3781582) baseStart_3781582 baseEnd_3781582 := by
    simpa [prefixWord, tailWord_3781582, baseEnd_3781582] using wordTrace_append hprefix tailTrace_3781582
  have hstable : (prefixWord ++ tailWord_3781582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781582).length < 2 ^ (prefixWord ++ tailWord_3781582).sum := by decide
  have hdescent : baseEnd_3781582 < baseStart_3781582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781585 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 4, 2, 3]
def baseStart_3781585 : Nat := 118140960795 + 3781585 * 2 ^ 59
def prefixEnd_3781585 : Nat := 4983230072969 + 3 ^ 40 * 3781585 * 2
def baseEnd_3781585 : Nat := 1941770740832692264996313

theorem tailTrace_3781585 : CollatzResearch.WordTrace tailWord_3781585 prefixEnd_3781585 1941770740832692264996313 := by
  unfold tailWord_3781585
  simp only [CollatzResearch.WordTrace]
  refine ⟨137925736004970863144898209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91950490669980575429932139 137925736004970863144898209)
  ·
    refine ⟨103444302003728147358673657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137925736004970863144898209 103444302003728147358673657)
    ·
      refine ⟨77583226502796110519005243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103444302003728147358673657 77583226502796110519005243)
      ·
        refine ⟨116374839754194165778507865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77583226502796110519005243 116374839754194165778507865)
        ·
          refine ⟨87281129815645624333880899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116374839754194165778507865 87281129815645624333880899)
          ·
            refine ⟨130921694723468436500821349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87281129815645624333880899 130921694723468436500821349)
            ·
              refine ⟨24547817760650331843904003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130921694723468436500821349 24547817760650331843904003)
              ·
                refine ⟨36821726640975497765856005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24547817760650331843904003 36821726640975497765856005)
                ·
                  refine ⟨6904073745182905831098001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36821726640975497765856005 6904073745182905831098001)
                  ·
                    refine ⟨5178055308887179373323501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6904073745182905831098001 5178055308887179373323501)
                    ·
                      refine ⟨1941770740832692264996313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5178055308887179373323501 1941770740832692264996313)
                      ·
                        rfl

theorem cell23_3781585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 2, 3].length) (baseStart_3781585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781585 prefixEnd_3781585 := by exact prefixLift 3781585
  have htrace : WordTrace (prefixWord ++ tailWord_3781585) baseStart_3781585 baseEnd_3781585 := by
    simpa [prefixWord, tailWord_3781585, baseEnd_3781585] using wordTrace_append hprefix tailTrace_3781585
  have hstable : (prefixWord ++ tailWord_3781585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781585).length < 2 ^ (prefixWord ++ tailWord_3781585).sum := by decide
  have hdescent : baseEnd_3781585 < baseStart_3781585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781592 : List Nat := [2, 1, 2, 2, 2, 4, 2, 1, 3, 4]
def baseStart_3781592 : Nat := 118140960795 + 3781592 * 2 ^ 59
def prefixEnd_3781592 : Nat := 4983230072969 + 3 ^ 40 * 3781592 * 2
def baseEnd_3781592 : Nat := 647258111732424579202927

theorem tailTrace_3781592 : CollatzResearch.WordTrace tailWord_3781592 prefixEnd_3781592 647258111732424579202927 := by
  unfold tailWord_3781592
  simp only [CollatzResearch.WordTrace]
  refine ⟨68962995657972751670201515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91950660877297002226935353 68962995657972751670201515)
  ·
    refine ⟨103444493486959127505302273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68962995657972751670201515 103444493486959127505302273)
    ·
      refine ⟨77583370115219345628976705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103444493486959127505302273 77583370115219345628976705)
      ·
        refine ⟨58187527586414509221732529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77583370115219345628976705 58187527586414509221732529)
        ·
          refine ⟨43640645689810881916299397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58187527586414509221732529 43640645689810881916299397)
          ·
            refine ⟨8182621066839540359306137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43640645689810881916299397 8182621066839540359306137)
            ·
              refine ⟨6136965800129655269479603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8182621066839540359306137 6136965800129655269479603)
              ·
                refine ⟨9205448700194482904219405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6136965800129655269479603 9205448700194482904219405)
                ·
                  refine ⟨3452043262572931089082277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9205448700194482904219405 3452043262572931089082277)
                  ·
                    refine ⟨647258111732424579202927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3452043262572931089082277 647258111732424579202927)
                    ·
                      rfl

theorem cell23_3781592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 3, 4].length) (baseStart_3781592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781592 prefixEnd_3781592 := by exact prefixLift 3781592
  have htrace : WordTrace (prefixWord ++ tailWord_3781592) baseStart_3781592 baseEnd_3781592 := by
    simpa [prefixWord, tailWord_3781592, baseEnd_3781592] using wordTrace_append hprefix tailTrace_3781592
  have hstable : (prefixWord ++ tailWord_3781592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781592).length < 2 ^ (prefixWord ++ tailWord_3781592).sum := by decide
  have hdescent : baseEnd_3781592 < baseStart_3781592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781648 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 2, 10]
def baseStart_3781648 : Nat := 118140960795 + 3781648 * 2 ^ 59
def prefixEnd_3781648 : Nat := 4983230072969 + 3 ^ 40 * 3781648 * 2
def baseEnd_3781648 : Nat := 647267696704641839502841

theorem tailTrace_3781648 : CollatzResearch.WordTrace tailWord_3781648 prefixEnd_3781648 647267696704641839502841 := by
  unfold tailWord_3781648
  simp only [CollatzResearch.WordTrace]
  refine ⟨68964016901871312452220799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91952022535828416602961065 68964016901871312452220799)
  ·
    refine ⟨103446025352806968678331199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68964016901871312452220799 103446025352806968678331199)
    ·
      refine ⟨155169038029210453017496799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103446025352806968678331199 155169038029210453017496799)
      ·
        refine ⟨232753557043815679526245199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155169038029210453017496799 232753557043815679526245199)
        ·
          refine ⟨349130335565723519289367799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232753557043815679526245199 349130335565723519289367799)
          ·
            refine ⟨523695503348585278934051699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349130335565723519289367799 523695503348585278934051699)
            ·
              refine ⟨785543255022877918401077549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523695503348585278934051699 785543255022877918401077549)
              ·
                refine ⟨294578720633579219400404081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 785543255022877918401077549 294578720633579219400404081)
                ·
                  refine ⟨220934040475184414550303061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294578720633579219400404081 220934040475184414550303061)
                  ·
                    refine ⟨647267696704641839502841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 220934040475184414550303061 647267696704641839502841)
                    ·
                      rfl

theorem cell23_3781648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 10].length) (baseStart_3781648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781648 prefixEnd_3781648 := by exact prefixLift 3781648
  have htrace : WordTrace (prefixWord ++ tailWord_3781648) baseStart_3781648 baseEnd_3781648 := by
    simpa [prefixWord, tailWord_3781648, baseEnd_3781648] using wordTrace_append hprefix tailTrace_3781648
  have hstable : (prefixWord ++ tailWord_3781648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781648).length < 2 ^ (prefixWord ++ tailWord_3781648).sum := by decide
  have hdescent : baseEnd_3781648 < baseStart_3781648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781649 : List Nat := [1, 2, 2, 1, 1, 2, 1, 8, 1, 1, 3]
def baseStart_3781649 : Nat := 118140960795 + 3781649 * 2 ^ 59
def prefixEnd_3781649 : Nat := 4983230072969 + 3 ^ 40 * 3781649 * 2
def baseEnd_3781649 : Nat := 1941803603594580014596019

theorem tailTrace_3781649 : CollatzResearch.WordTrace tailWord_3781649 prefixEnd_3781649 1941803603594580014596019 := by
  unfold tailWord_3781649
  simp only [CollatzResearch.WordTrace]
  refine ⟨137928070276739002075228001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91952046851159334716818667 137928070276739002075228001)
  ·
    refine ⟨103446052707554251556421001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137928070276739002075228001 103446052707554251556421001)
    ·
      refine ⟨77584539530665688667315751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103446052707554251556421001 77584539530665688667315751)
      ·
        refine ⟨116376809295998533000973627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77584539530665688667315751 116376809295998533000973627)
        ·
          refine ⟨174565213943997799501460441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116376809295998533000973627 174565213943997799501460441)
          ·
            refine ⟨130923910457998349626095331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174565213943997799501460441 130923910457998349626095331)
            ·
              refine ⟨196385865686997524439142997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130923910457998349626095331 196385865686997524439142997)
              ·
                refine ⟨2301396863519502239521207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 196385865686997524439142997 2301396863519502239521207)
                ·
                  refine ⟨3452095295279253359281811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2301396863519502239521207 3452095295279253359281811)
                  ·
                    refine ⟨5178142942918880038922717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3452095295279253359281811 5178142942918880038922717)
                    ·
                      refine ⟨1941803603594580014596019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5178142942918880038922717 1941803603594580014596019)
                      ·
                        rfl

theorem cell23_3781649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 8, 1, 1, 3].length) (baseStart_3781649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781649 prefixEnd_3781649 := by exact prefixLift 3781649
  have htrace : WordTrace (prefixWord ++ tailWord_3781649) baseStart_3781649 baseEnd_3781649 := by
    simpa [prefixWord, tailWord_3781649, baseEnd_3781649] using wordTrace_append hprefix tailTrace_3781649
  have hstable : (prefixWord ++ tailWord_3781649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781649).length < 2 ^ (prefixWord ++ tailWord_3781649).sum := by decide
  have hdescent : baseEnd_3781649 < baseStart_3781649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781686 : List Nat := [5, 1, 2, 1, 1, 3, 3, 1, 1, 5]
def baseStart_3781686 : Nat := 118140960795 + 3781686 * 2 ^ 59
def prefixEnd_3781686 : Nat := 4983230072969 + 3 ^ 40 * 3781686 * 2
def baseEnd_3781686 : Nat := 647274200792932123277783

theorem tailTrace_3781686 : CollatzResearch.WordTrace tailWord_3781686 prefixEnd_3781686 647274200792932123277783 := by
  unfold tailWord_3781686
  simp only [CollatzResearch.WordTrace]
  refine ⟨8620588736100309837145307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91952946518403304929549941 8620588736100309837145307)
  ·
    refine ⟨12930883104150464755717961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8620588736100309837145307 12930883104150464755717961)
    ·
      refine ⟨9698162328112848566788471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12930883104150464755717961 9698162328112848566788471)
      ·
        refine ⟨14547243492169272850182707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9698162328112848566788471 14547243492169272850182707)
        ·
          refine ⟨21820865238253909275274061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14547243492169272850182707 21820865238253909275274061)
          ·
            refine ⟨8182824464345215978227773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21820865238253909275274061 8182824464345215978227773)
            ·
              refine ⟨3068559174129455991835415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8182824464345215978227773 3068559174129455991835415)
              ·
                refine ⟨4602838761194183987753123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3068559174129455991835415 4602838761194183987753123)
                ·
                  refine ⟨6904258141791275981629685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4602838761194183987753123 6904258141791275981629685)
                  ·
                    refine ⟨647274200792932123277783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6904258141791275981629685 647274200792932123277783)
                    ·
                      rfl

theorem cell23_3781686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_3781686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781686 prefixEnd_3781686 := by exact prefixLift 3781686
  have htrace : WordTrace (prefixWord ++ tailWord_3781686) baseStart_3781686 baseEnd_3781686 := by
    simpa [prefixWord, tailWord_3781686, baseEnd_3781686] using wordTrace_append hprefix tailTrace_3781686
  have hstable : (prefixWord ++ tailWord_3781686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781686).length < 2 ^ (prefixWord ++ tailWord_3781686).sum := by decide
  have hdescent : baseEnd_3781686 < baseStart_3781686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781692 : List Nat := [2, 2, 2, 2, 2, 2, 3, 1, 1, 1, 5]
def baseStart_3781692 : Nat := 118140960795 + 3781692 * 2 ^ 59
def prefixEnd_3781692 : Nat := 4983230072969 + 3 ^ 40 * 3781692 * 2
def baseEnd_3781692 : Nat := 1941825683262723346358321

theorem tailTrace_3781692 : CollatzResearch.WordTrace tailWord_3781692 prefixEnd_3781692 1941825683262723346358321 := by
  unfold tailWord_3781692
  simp only [CollatzResearch.WordTrace]
  refine ⟨68964819307791610209521665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91953092410388813612695553 68964819307791610209521665)
  ·
    refine ⟨51723614480843707657141249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68964819307791610209521665 51723614480843707657141249)
    ·
      refine ⟨38792710860632780742855937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51723614480843707657141249 38792710860632780742855937)
      ·
        refine ⟨29094533145474585557141953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38792710860632780742855937 29094533145474585557141953)
        ·
          refine ⟨21820899859105939167856465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29094533145474585557141953 21820899859105939167856465)
          ·
            refine ⟨16365674894329454375892349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21820899859105939167856465 16365674894329454375892349)
            ·
              refine ⟨6137128085373545390959631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16365674894329454375892349 6137128085373545390959631)
              ·
                refine ⟨9205692128060318086439447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6137128085373545390959631 9205692128060318086439447)
                ·
                  refine ⟨13808538192090477129659171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9205692128060318086439447 13808538192090477129659171)
                  ·
                    refine ⟨20712807288135715694488757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13808538192090477129659171 20712807288135715694488757)
                    ·
                      refine ⟨1941825683262723346358321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20712807288135715694488757 1941825683262723346358321)
                      ·
                        rfl

theorem cell23_3781692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_3781692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781692 prefixEnd_3781692 := by exact prefixLift 3781692
  have htrace : WordTrace (prefixWord ++ tailWord_3781692) baseStart_3781692 baseEnd_3781692 := by
    simpa [prefixWord, tailWord_3781692, baseEnd_3781692] using wordTrace_append hprefix tailTrace_3781692
  have hstable : (prefixWord ++ tailWord_3781692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781692).length < 2 ^ (prefixWord ++ tailWord_3781692).sum := by decide
  have hdescent : baseEnd_3781692 < baseStart_3781692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781709 : List Nat := [1, 6, 1, 1, 1, 2, 1, 2, 3, 2, 3]
def baseStart_3781709 : Nat := 118140960795 + 3781709 * 2 ^ 59
def prefixEnd_3781709 : Nat := 4983230072969 + 3 ^ 40 * 3781709 * 2
def baseEnd_3781709 : Nat := 1941834412433849779845743

theorem tailTrace_3781709 : CollatzResearch.WordTrace tailWord_3781709 prefixEnd_3781709 1941834412433849779845743 := by
  unfold tailWord_3781709
  simp only [CollatzResearch.WordTrace]
  refine ⟨137930258656521632322412181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91953505771014421548274787 137930258656521632322412181)
  ·
    refine ⟨6465480874524451515113071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 137930258656521632322412181 6465480874524451515113071)
    ·
      refine ⟨9698221311786677272669607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6465480874524451515113071 9698221311786677272669607)
      ·
        refine ⟨14547331967680015909004411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9698221311786677272669607 14547331967680015909004411)
        ·
          refine ⟨21820997951520023863506617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14547331967680015909004411 21820997951520023863506617)
          ·
            refine ⟨16365748463640017897629963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21820997951520023863506617 16365748463640017897629963)
            ·
              refine ⟨24548622695460026846444945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16365748463640017897629963 24548622695460026846444945)
              ·
                refine ⟨18411467021595020134833709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24548622695460026846444945 18411467021595020134833709)
                ·
                  refine ⟨6904300133098132550562641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18411467021595020134833709 6904300133098132550562641)
                  ·
                    refine ⟨5178225099823599412921981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6904300133098132550562641 5178225099823599412921981)
                    ·
                      refine ⟨1941834412433849779845743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5178225099823599412921981 1941834412433849779845743)
                      ·
                        rfl

theorem cell23_3781709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_3781709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781709 prefixEnd_3781709 := by exact prefixLift 3781709
  have htrace : WordTrace (prefixWord ++ tailWord_3781709) baseStart_3781709 baseEnd_3781709 := by
    simpa [prefixWord, tailWord_3781709, baseEnd_3781709] using wordTrace_append hprefix tailTrace_3781709
  have hstable : (prefixWord ++ tailWord_3781709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781709).length < 2 ^ (prefixWord ++ tailWord_3781709).sum := by decide
  have hdescent : baseEnd_3781709 < baseStart_3781709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781745 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 1, 5, 4]
def baseStart_3781745 : Nat := 118140960795 + 3781745 * 2 ^ 59
def prefixEnd_3781745 : Nat := 4983230072969 + 3 ^ 40 * 3781745 * 2
def baseEnd_3781745 : Nat := 1941852897737411638995577

theorem tailTrace_3781745 : CollatzResearch.WordTrace tailWord_3781745 prefixEnd_3781745 1941852897737411638995577 := by
  unfold tailWord_3781745
  simp only [CollatzResearch.WordTrace]
  refine ⟨137931571684391210470722689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91954381122927473647148459 137931571684391210470722689)
  ·
    refine ⟨103448678763293407853042017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137931571684391210470722689 103448678763293407853042017)
    ·
      refine ⟨77586509072470055889781513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103448678763293407853042017 77586509072470055889781513)
      ·
        refine ⟨58189881804352541917336135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77586509072470055889781513 58189881804352541917336135)
        ·
          refine ⟨87284822706528812876004203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58189881804352541917336135 87284822706528812876004203)
          ·
            refine ⟨130927234059793219314006305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87284822706528812876004203 130927234059793219314006305)
            ·
              refine ⟨98195425544844914485504729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130927234059793219314006305 98195425544844914485504729)
              ·
                refine ⟨73646569158633685864128547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98195425544844914485504729 73646569158633685864128547)
                ·
                  refine ⟨110469853737950528796192821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73646569158633685864128547 110469853737950528796192821)
                  ·
                    refine ⟨10356548787932862074643077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110469853737950528796192821 10356548787932862074643077)
                    ·
                      refine ⟨1941852897737411638995577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10356548787932862074643077 1941852897737411638995577)
                      ·
                        rfl

theorem cell23_3781745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_3781745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781745 prefixEnd_3781745 := by exact prefixLift 3781745
  have htrace : WordTrace (prefixWord ++ tailWord_3781745) baseStart_3781745 baseEnd_3781745 := by
    simpa [prefixWord, tailWord_3781745, baseEnd_3781745] using wordTrace_append hprefix tailTrace_3781745
  have hstable : (prefixWord ++ tailWord_3781745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781745).length < 2 ^ (prefixWord ++ tailWord_3781745).sum := by decide
  have hdescent : baseEnd_3781745 < baseStart_3781745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781775 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 4]
def baseStart_3781775 : Nat := 118140960795 + 3781775 * 2 ^ 59
def prefixEnd_3781775 : Nat := 4983230072969 + 3 ^ 40 * 3781775 * 2
def baseEnd_3781775 : Nat := 1941868302157046521620439

theorem tailTrace_3781775 : CollatzResearch.WordTrace tailWord_3781775 prefixEnd_3781775 1941868302157046521620439 := by
  unfold tailWord_3781775
  simp only [CollatzResearch.WordTrace]
  refine ⟨137932665874282525594314779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91955110582855017062876519 137932665874282525594314779)
  ·
    refine ⟨206898998811423788391472169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137932665874282525594314779 206898998811423788391472169)
    ·
      refine ⟨155174249108567841293604127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206898998811423788391472169 155174249108567841293604127)
      ·
        refine ⟨232761373662851761940406191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155174249108567841293604127 232761373662851761940406191)
        ·
          refine ⟨349142060494277642910609287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232761373662851761940406191 349142060494277642910609287)
          ·
            refine ⟨523713090741416464365913931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349142060494277642910609287 523713090741416464365913931)
            ·
              refine ⟨785569636112124696548870897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523713090741416464365913931 785569636112124696548870897)
              ·
                refine ⟨589177227084093522411653173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 785569636112124696548870897 589177227084093522411653173)
                ·
                  refine ⟨55235365039133767726092485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 589177227084093522411653173 55235365039133767726092485)
                  ·
                    refine ⟨10356630944837581448642341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55235365039133767726092485 10356630944837581448642341)
                    ·
                      refine ⟨1941868302157046521620439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10356630944837581448642341 1941868302157046521620439)
                      ·
                        rfl

theorem cell23_3781775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 4].length) (baseStart_3781775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781775 prefixEnd_3781775 := by exact prefixLift 3781775
  have htrace : WordTrace (prefixWord ++ tailWord_3781775) baseStart_3781775 baseEnd_3781775 := by
    simpa [prefixWord, tailWord_3781775, baseEnd_3781775] using wordTrace_append hprefix tailTrace_3781775
  have hstable : (prefixWord ++ tailWord_3781775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781775).length < 2 ^ (prefixWord ++ tailWord_3781775).sum := by decide
  have hdescent : baseEnd_3781775 < baseStart_3781775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781779 : List Nat := [1, 1, 1, 2, 1, 2, 7, 1, 1, 4, 2]
def baseStart_3781779 : Nat := 118140960795 + 3781779 * 2 ^ 59
def prefixEnd_3781779 : Nat := 4983230072969 + 3 ^ 40 * 3781779 * 2
def baseEnd_3781779 : Nat := 1941870356079664505970421

theorem tailTrace_3781779 : CollatzResearch.WordTrace tailWord_3781779 prefixEnd_3781779 1941870356079664505970421 := by
  unfold tailWord_3781779
  simp only [CollatzResearch.WordTrace]
  refine ⟨137932811766268034277460391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91955207844178689518306927 137932811766268034277460391)
  ·
    refine ⟨206899217649402051416190587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137932811766268034277460391 206899217649402051416190587)
    ·
      refine ⟨310348826474103077124285881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206899217649402051416190587 310348826474103077124285881)
      ·
        refine ⟨232761619855577307843214411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310348826474103077124285881 232761619855577307843214411)
        ·
          refine ⟨349142429783365961764821617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232761619855577307843214411 349142429783365961764821617)
          ·
            refine ⟨261856822337524471323616213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349142429783365961764821617 261856822337524471323616213)
            ·
              refine ⟨6137269273535729796647255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 261856822337524471323616213 6137269273535729796647255)
              ·
                refine ⟨9205903910303594694970883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6137269273535729796647255 9205903910303594694970883)
                ·
                  refine ⟨13808855865455392042456325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9205903910303594694970883 13808855865455392042456325)
                  ·
                    refine ⟨2589160474772886007960561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13808855865455392042456325 2589160474772886007960561)
                    ·
                      refine ⟨1941870356079664505970421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2589160474772886007960561 1941870356079664505970421)
                      ·
                        rfl

theorem cell23_3781779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 4, 2].length) (baseStart_3781779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781779 prefixEnd_3781779 := by exact prefixLift 3781779
  have htrace : WordTrace (prefixWord ++ tailWord_3781779) baseStart_3781779 baseEnd_3781779 := by
    simpa [prefixWord, tailWord_3781779, baseEnd_3781779] using wordTrace_append hprefix tailTrace_3781779
  have hstable : (prefixWord ++ tailWord_3781779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781779).length < 2 ^ (prefixWord ++ tailWord_3781779).sum := by decide
  have hdescent : baseEnd_3781779 < baseStart_3781779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781796 : List Nat := [2, 3, 1, 2, 3, 1, 1, 2, 4, 2, 2]
def baseStart_3781796 : Nat := 118140960795 + 3781796 * 2 ^ 59
def prefixEnd_3781796 : Nat := 4983230072969 + 3 ^ 40 * 3781796 * 2
def baseEnd_3781796 : Nat := 1941879085250790939457843

theorem tailTrace_3781796 : CollatzResearch.WordTrace tailWord_3781796 prefixEnd_3781796 1941879085250790939457843 := by
  unfold tailWord_3781796
  simp only [CollatzResearch.WordTrace]
  refine ⟨68966715903603223090414621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91955621204804297453886161 68966715903603223090414621)
  ·
    refine ⟨25862518463851208658905483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68966715903603223090414621 25862518463851208658905483)
    ·
      refine ⟨38793777695776812988358225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25862518463851208658905483 38793777695776812988358225)
      ·
        refine ⟨29095333271832609741268669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38793777695776812988358225 29095333271832609741268669)
        ·
          refine ⟨10910749976937228652975751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29095333271832609741268669 10910749976937228652975751)
          ·
            refine ⟨16366124965405842979463627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10910749976937228652975751 16366124965405842979463627)
            ·
              refine ⟨24549187448108764469195441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16366124965405842979463627 24549187448108764469195441)
              ·
                refine ⟨18411890586081573351896581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24549187448108764469195441 18411890586081573351896581)
                ·
                  refine ⟨3452229484890295003480609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18411890586081573351896581 3452229484890295003480609)
                  ·
                    refine ⟨2589172113667721252610457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3452229484890295003480609 2589172113667721252610457)
                    ·
                      refine ⟨1941879085250790939457843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2589172113667721252610457 1941879085250790939457843)
                      ·
                        rfl

theorem cell23_3781796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_3781796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781796 prefixEnd_3781796 := by exact prefixLift 3781796
  have htrace : WordTrace (prefixWord ++ tailWord_3781796) baseStart_3781796 baseEnd_3781796 := by
    simpa [prefixWord, tailWord_3781796, baseEnd_3781796] using wordTrace_append hprefix tailTrace_3781796
  have hstable : (prefixWord ++ tailWord_3781796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781796).length < 2 ^ (prefixWord ++ tailWord_3781796).sum := by decide
  have hdescent : baseEnd_3781796 < baseStart_3781796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781799 : List Nat := [1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_3781799 : Nat := 118140960795 + 3781799 * 2 ^ 59
def prefixEnd_3781799 : Nat := 4983230072969 + 3 ^ 40 * 3781799 * 2
def baseEnd_3781799 : Nat := 1941880625692754427720329

theorem tailTrace_3781799 : CollatzResearch.WordTrace tailWord_3781799 prefixEnd_3781799 1941880625692754427720329 := by
  unfold tailWord_3781799
  simp only [CollatzResearch.WordTrace]
  refine ⟨137933541226195577693188451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91955694150797051795458967 137933541226195577693188451)
  ·
    refine ⟨206900311839293366539782677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137933541226195577693188451 206900311839293366539782677)
    ·
      refine ⟨9698452117466876556552313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 206900311839293366539782677 9698452117466876556552313)
      ·
        refine ⟨7273839088100157417414235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9698452117466876556552313 7273839088100157417414235)
        ·
          refine ⟨10910758632150236126121353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7273839088100157417414235 10910758632150236126121353)
          ·
            refine ⟨8183068974112677094591015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10910758632150236126121353 8183068974112677094591015)
            ·
              refine ⟨12274603461169015641886523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8183068974112677094591015 12274603461169015641886523)
              ·
                refine ⟨18411905191753523462829785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12274603461169015641886523 18411905191753523462829785)
                ·
                  refine ⟨13808928893815142597122339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18411905191753523462829785 13808928893815142597122339)
                  ·
                    refine ⟨20713393340722713895683509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13808928893815142597122339 20713393340722713895683509)
                    ·
                      refine ⟨1941880625692754427720329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20713393340722713895683509 1941880625692754427720329)
                      ·
                        rfl

theorem cell23_3781799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_3781799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781799 prefixEnd_3781799 := by exact prefixLift 3781799
  have htrace : WordTrace (prefixWord ++ tailWord_3781799) baseStart_3781799 baseEnd_3781799 := by
    simpa [prefixWord, tailWord_3781799, baseEnd_3781799] using wordTrace_append hprefix tailTrace_3781799
  have hstable : (prefixWord ++ tailWord_3781799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781799).length < 2 ^ (prefixWord ++ tailWord_3781799).sum := by decide
  have hdescent : baseEnd_3781799 < baseStart_3781799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781842 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 1, 1, 7]
def baseStart_3781842 : Nat := 118140960795 + 3781842 * 2 ^ 59
def prefixEnd_3781842 : Nat := 4983230072969 + 3 ^ 40 * 3781842 * 2
def baseEnd_3781842 : Nat := 1941902705360897759482631

theorem tailTrace_3781842 : CollatzResearch.WordTrace tailWord_3781842 prefixEnd_3781842 1941902705360897759482631 := by
  unfold tailWord_3781842
  simp only [CollatzResearch.WordTrace]
  refine ⟨34483777391259949009250945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91956739710026530691335853 34483777391259949009250945)
  ·
    refine ⟨25862833043444961756938209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34483777391259949009250945 25862833043444961756938209)
    ·
      refine ⟨19397124782583721317703657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25862833043444961756938209 19397124782583721317703657)
      ·
        refine ⟨14547843586937790988277743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19397124782583721317703657 14547843586937790988277743)
        ·
          refine ⟨21821765380406686482416615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14547843586937790988277743 21821765380406686482416615)
          ·
            refine ⟨32732648070610029723624923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21821765380406686482416615 32732648070610029723624923)
            ·
              refine ⟨49098972105915044585437385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32732648070610029723624923 49098972105915044585437385)
              ·
                refine ⟨36824229079436283439078039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49098972105915044585437385 36824229079436283439078039)
                ·
                  refine ⟨55236343619154425158617059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36824229079436283439078039 55236343619154425158617059)
                  ·
                    refine ⟨82854515428731637737925589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55236343619154425158617059 82854515428731637737925589)
                    ·
                      refine ⟨1941902705360897759482631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 82854515428731637737925589 1941902705360897759482631)
                      ·
                        rfl

theorem cell23_3781842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_3781842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781842 prefixEnd_3781842 := by exact prefixLift 3781842
  have htrace : WordTrace (prefixWord ++ tailWord_3781842) baseStart_3781842 baseEnd_3781842 := by
    simpa [prefixWord, tailWord_3781842, baseEnd_3781842] using wordTrace_append hprefix tailTrace_3781842
  have hstable : (prefixWord ++ tailWord_3781842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781842).length < 2 ^ (prefixWord ++ tailWord_3781842).sum := by decide
  have hdescent : baseEnd_3781842 < baseStart_3781842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781872 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 3]
def baseStart_3781872 : Nat := 118140960795 + 3781872 * 2 ^ 59
def prefixEnd_3781872 : Nat := 4983230072969 + 3 ^ 40 * 3781872 * 2
def baseEnd_3781872 : Nat := 1941918109780532642107493

theorem tailTrace_3781872 : CollatzResearch.WordTrace tailWord_3781872 prefixEnd_3781872 1941918109780532642107493 := by
  unfold tailWord_3781872
  simp only [CollatzResearch.WordTrace]
  refine ⟨68968101877465555580297935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91957469169954074107063913 68968101877465555580297935)
  ·
    refine ⟨103452152816198333370446903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68968101877465555580297935 103452152816198333370446903)
    ·
      refine ⟨155178229224297500055670355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103452152816198333370446903 155178229224297500055670355)
      ·
        refine ⟨232767343836446250083505533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155178229224297500055670355 232767343836446250083505533)
        ·
          refine ⟨87287753938667343781314575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232767343836446250083505533 87287753938667343781314575)
          ·
            refine ⟨130931630908001015671971863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87287753938667343781314575 130931630908001015671971863)
            ·
              refine ⟨196397446362001523507957795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130931630908001015671971863 196397446362001523507957795)
              ·
                refine ⟨294596169543002285261936693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196397446362001523507957795 294596169543002285261936693)
                ·
                  refine ⟨27618390894656464243306565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 294596169543002285261936693 27618390894656464243306565)
                  ·
                    refine ⟨5178448292748087045619981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27618390894656464243306565 5178448292748087045619981)
                    ·
                      refine ⟨1941918109780532642107493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5178448292748087045619981 1941918109780532642107493)
                      ·
                        rfl

theorem cell23_3781872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 3].length) (baseStart_3781872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781872 prefixEnd_3781872 := by exact prefixLift 3781872
  have htrace : WordTrace (prefixWord ++ tailWord_3781872) baseStart_3781872 baseEnd_3781872 := by
    simpa [prefixWord, tailWord_3781872, baseEnd_3781872] using wordTrace_append hprefix tailTrace_3781872
  have hstable : (prefixWord ++ tailWord_3781872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781872).length < 2 ^ (prefixWord ++ tailWord_3781872).sum := by decide
  have hdescent : baseEnd_3781872 < baseStart_3781872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781886 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2]
def baseStart_3781886 : Nat := 118140960795 + 3781886 * 2 ^ 59
def prefixEnd_3781886 : Nat := 4983230072969 + 3 ^ 40 * 3781886 * 2
def baseEnd_3781886 : Nat := 1941925298509695587332429

theorem tailTrace_3781886 : CollatzResearch.WordTrace tailWord_3781886 prefixEnd_3781886 1941925298509695587332429 := by
  unfold tailWord_3781886
  simp only [CollatzResearch.WordTrace]
  refine ⟨17242089297110048943950689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91957809584586927701070341 17242089297110048943950689)
  ·
    refine ⟨12931566972832536707963017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17242089297110048943950689 12931566972832536707963017)
    ·
      refine ⟨9698675229624402530972263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12931566972832536707963017 9698675229624402530972263)
      ·
        refine ⟨14548012844436603796458395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9698675229624402530972263 14548012844436603796458395)
        ·
          refine ⟨21822019266654905694687593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14548012844436603796458395 21822019266654905694687593)
          ·
            refine ⟨16366514449991179271015695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21822019266654905694687593 16366514449991179271015695)
            ·
              refine ⟨24549771674986768906523543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16366514449991179271015695 24549771674986768906523543)
              ·
                refine ⟨36824657512480153359785315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24549771674986768906523543 36824657512480153359785315)
                ·
                  refine ⟨55236986268720230039677973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36824657512480153359785315 55236986268720230039677973)
                  ·
                    refine ⟨2589233731346260783109905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55236986268720230039677973 2589233731346260783109905)
                    ·
                      refine ⟨1941925298509695587332429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2589233731346260783109905 1941925298509695587332429)
                      ·
                        rfl

theorem cell23_3781886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_3781886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781886 prefixEnd_3781886 := by exact prefixLift 3781886
  have htrace : WordTrace (prefixWord ++ tailWord_3781886) baseStart_3781886 baseEnd_3781886 := by
    simpa [prefixWord, tailWord_3781886, baseEnd_3781886] using wordTrace_append hprefix tailTrace_3781886
  have hstable : (prefixWord ++ tailWord_3781886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781886).length < 2 ^ (prefixWord ++ tailWord_3781886).sum := by decide
  have hdescent : baseEnd_3781886 < baseStart_3781886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781896 : List Nat := [2, 1, 3, 2, 4, 1, 1, 2, 3, 4]
def baseStart_3781896 : Nat := 118140960795 + 3781896 * 2 ^ 59
def prefixEnd_3781896 : Nat := 4983230072969 + 3 ^ 40 * 3781896 * 2
def baseEnd_3781896 : Nat := 647310144438746849402461

theorem tailTrace_3781896 : CollatzResearch.WordTrace tailWord_3781896 prefixEnd_3781896 647310144438746849402461 := by
  unfold tailWord_3781896
  simp only [CollatzResearch.WordTrace]
  refine ⟨68968539553422081629734771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91958052737896108839646361 68968539553422081629734771)
  ·
    refine ⟨103452809330133122444602157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68968539553422081629734771 103452809330133122444602157)
    ·
      refine ⟨38794803498799920916725809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103452809330133122444602157 38794803498799920916725809)
      ·
        refine ⟨29096102624099940687544357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38794803498799920916725809 29096102624099940687544357)
        ·
          refine ⟨5455519242018738878914567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29096102624099940687544357 5455519242018738878914567)
          ·
            refine ⟨8183278863028108318371851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5455519242018738878914567 8183278863028108318371851)
            ·
              refine ⟨12274918294542162477557777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8183278863028108318371851 12274918294542162477557777)
              ·
                refine ⟨9206188720906621858168333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12274918294542162477557777 9206188720906621858168333)
                ·
                  refine ⟨3452320770339983196813125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9206188720906621858168333 3452320770339983196813125)
                  ·
                    refine ⟨647310144438746849402461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3452320770339983196813125 647310144438746849402461)
                    ·
                      rfl

theorem cell23_3781896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_3781896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781896 prefixEnd_3781896 := by exact prefixLift 3781896
  have htrace : WordTrace (prefixWord ++ tailWord_3781896) baseStart_3781896 baseEnd_3781896 := by
    simpa [prefixWord, tailWord_3781896, baseEnd_3781896] using wordTrace_append hprefix tailTrace_3781896
  have hstable : (prefixWord ++ tailWord_3781896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781896).length < 2 ^ (prefixWord ++ tailWord_3781896).sum := by decide
  have hdescent : baseEnd_3781896 < baseStart_3781896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781936 : List Nat := [2, 1, 1, 1, 2, 2, 6, 1, 3, 1, 3]
def baseStart_3781936 : Nat := 118140960795 + 3781936 * 2 ^ 59
def prefixEnd_3781936 : Nat := 4983230072969 + 3 ^ 40 * 3781936 * 2
def baseEnd_3781936 : Nat := 1941950972542420391707199

theorem tailTrace_3781936 : CollatzResearch.WordTrace tailWord_3781936 prefixEnd_3781936 1941950972542420391707199 := by
  unfold tailWord_3781936
  simp only [CollatzResearch.WordTrace]
  refine ⟨68969269013349625045462831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91959025351132833393950441 68969269013349625045462831)
  ·
    refine ⟨103453903520024437568194247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68969269013349625045462831 103453903520024437568194247)
    ·
      refine ⟨155180855280036656352291371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103453903520024437568194247 155180855280036656352291371)
      ·
        refine ⟨232771282920054984528437057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155180855280036656352291371 232771282920054984528437057)
        ·
          refine ⟨174578462190041238396327793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232771282920054984528437057 174578462190041238396327793)
          ·
            refine ⟨130933846642530928797245845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174578462190041238396327793 130933846642530928797245845)
            ·
              refine ⟨6137524061368637287370899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130933846642530928797245845 6137524061368637287370899)
              ·
                refine ⟨9206286092052955931056349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6137524061368637287370899 9206286092052955931056349)
                ·
                  refine ⟨3452357284519858474146131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9206286092052955931056349 3452357284519858474146131)
                  ·
                    refine ⟨5178535926779787711219197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3452357284519858474146131 5178535926779787711219197)
                    ·
                      refine ⟨1941950972542420391707199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5178535926779787711219197 1941950972542420391707199)
                      ·
                        rfl

theorem cell23_3781936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 3, 1, 3].length) (baseStart_3781936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781936 prefixEnd_3781936 := by exact prefixLift 3781936
  have htrace : WordTrace (prefixWord ++ tailWord_3781936) baseStart_3781936 baseEnd_3781936 := by
    simpa [prefixWord, tailWord_3781936, baseEnd_3781936] using wordTrace_append hprefix tailTrace_3781936
  have hstable : (prefixWord ++ tailWord_3781936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781936).length < 2 ^ (prefixWord ++ tailWord_3781936).sum := by decide
  have hdescent : baseEnd_3781936 < baseStart_3781936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781953 : List Nat := [1, 2, 5, 2, 1, 1, 2, 2, 3, 1, 3]
def baseStart_3781953 : Nat := 118140960795 + 3781953 * 2 ^ 59
def prefixEnd_3781953 : Nat := 4983230072969 + 3 ^ 40 * 3781953 * 2
def baseEnd_3781953 : Nat := 1941959701713546825194621

theorem tailTrace_3781953 : CollatzResearch.WordTrace tailWord_3781953 prefixEnd_3781953 1941959701713546825194621 := by
  unfold tailWord_3781953
  simp only [CollatzResearch.WordTrace]
  refine ⟨137939158067637661994294513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91959438711758441329529675 137939158067637661994294513)
  ·
    refine ⟨103454368550728246495720885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137939158067637661994294513 103454368550728246495720885)
    ·
      refine ⟨9698847051630773108973833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103454368550728246495720885 9698847051630773108973833)
      ·
        refine ⟨7274135288723079831730375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9698847051630773108973833 7274135288723079831730375)
        ·
          refine ⟨10911202933084619747595563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7274135288723079831730375 10911202933084619747595563)
          ·
            refine ⟨16366804399626929621393345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10911202933084619747595563 16366804399626929621393345)
            ·
              refine ⟨12275103299720197216045009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16366804399626929621393345 12275103299720197216045009)
              ·
                refine ⟨9206327474790147912033757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12275103299720197216045009 9206327474790147912033757)
                ·
                  refine ⟨3452372803046305467012659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9206327474790147912033757 3452372803046305467012659)
                  ·
                    refine ⟨5178559204569458200518989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3452372803046305467012659 5178559204569458200518989)
                    ·
                      refine ⟨1941959701713546825194621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5178559204569458200518989 1941959701713546825194621)
                      ·
                        rfl

theorem cell23_3781953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_3781953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781953 prefixEnd_3781953 := by exact prefixLift 3781953
  have htrace : WordTrace (prefixWord ++ tailWord_3781953) baseStart_3781953 baseEnd_3781953 := by
    simpa [prefixWord, tailWord_3781953, baseEnd_3781953] using wordTrace_append hprefix tailTrace_3781953
  have hstable : (prefixWord ++ tailWord_3781953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781953).length < 2 ^ (prefixWord ++ tailWord_3781953).sum := by decide
  have hdescent : baseEnd_3781953 < baseStart_3781953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781969 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 6, 4]
def baseStart_3781969 : Nat := 118140960795 + 3781969 * 2 ^ 59
def prefixEnd_3781969 : Nat := 4983230072969 + 3 ^ 40 * 3781969 * 2
def baseEnd_3781969 : Nat := 647322639134672920864849

theorem tailTrace_3781969 : CollatzResearch.WordTrace tailWord_3781969 prefixEnd_3781969 647322639134672920864849 := by
  unfold tailWord_3781969
  simp only [CollatzResearch.WordTrace]
  refine ⟨137939741635579696726876961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91959827757053131151251307 137939741635579696726876961)
  ·
    refine ⟨103454806226684772545157721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137939741635579696726876961 103454806226684772545157721)
    ·
      refine ⟨77591104670013579408868291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103454806226684772545157721 77591104670013579408868291)
      ·
        refine ⟨116386657005020369113302437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77591104670013579408868291 116386657005020369113302437)
        ·
          refine ⟨21822498188441319208744207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116386657005020369113302437 21822498188441319208744207)
          ·
            refine ⟨32733747282661978813116311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21822498188441319208744207 32733747282661978813116311)
            ·
              refine ⟨49100620923992968219674467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32733747282661978813116311 49100620923992968219674467)
              ·
                refine ⟨73650931385989452329511701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49100620923992968219674467 73650931385989452329511701)
                ·
                  refine ⟨3452387408718255577945861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73650931385989452329511701 3452387408718255577945861)
                  ·
                    refine ⟨647322639134672920864849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3452387408718255577945861 647322639134672920864849)
                    ·
                      rfl

theorem cell23_3781969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 6, 4].length) (baseStart_3781969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781969 prefixEnd_3781969 := by exact prefixLift 3781969
  have htrace : WordTrace (prefixWord ++ tailWord_3781969) baseStart_3781969 baseEnd_3781969 := by
    simpa [prefixWord, tailWord_3781969, baseEnd_3781969] using wordTrace_append hprefix tailTrace_3781969
  have hstable : (prefixWord ++ tailWord_3781969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781969).length < 2 ^ (prefixWord ++ tailWord_3781969).sum := by decide
  have hdescent : baseEnd_3781969 < baseStart_3781969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781986 : List Nat := [3, 3, 2, 1, 1, 1, 1, 3, 4, 4]
def baseStart_3781986 : Nat := 118140960795 + 3781986 * 2 ^ 59
def prefixEnd_3781986 : Nat := 4983230072969 + 3 ^ 40 * 3781986 * 2
def baseEnd_3781986 : Nat := 647325548858381732027323

theorem tailTrace_3781986 : CollatzResearch.WordTrace tailWord_3781986 prefixEnd_3781986 647325548858381732027323 := by
  unfold tailWord_3781986
  simp only [CollatzResearch.WordTrace]
  refine ⟨34485090419129527157561453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91960241117678739086830541 34485090419129527157561453)
  ·
    refine ⟨12931908907173572684085545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34485090419129527157561453 12931908907173572684085545)
    ·
      refine ⟨9698931680380179513064159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12931908907173572684085545 9698931680380179513064159)
      ·
        refine ⟨14548397520570269269596239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9698931680380179513064159 14548397520570269269596239)
        ·
          refine ⟨21822596280855403904394359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14548397520570269269596239 21822596280855403904394359)
          ·
            refine ⟨32733894421283105856591539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21822596280855403904394359 32733894421283105856591539)
            ·
              refine ⟨49100841631924658784887309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32733894421283105856591539 49100841631924658784887309)
              ·
                refine ⟨18412815611971747044332741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49100841631924658784887309 18412815611971747044332741)
                ·
                  refine ⟨3452402927244702570812389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18412815611971747044332741 3452402927244702570812389)
                  ·
                    refine ⟨647325548858381732027323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3452402927244702570812389 647325548858381732027323)
                    ·
                      rfl

theorem cell23_3781986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_3781986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3781986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3781986 prefixEnd_3781986 := by exact prefixLift 3781986
  have htrace : WordTrace (prefixWord ++ tailWord_3781986) baseStart_3781986 baseEnd_3781986 := by
    simpa [prefixWord, tailWord_3781986, baseEnd_3781986] using wordTrace_append hprefix tailTrace_3781986
  have hstable : (prefixWord ++ tailWord_3781986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781986).length < 2 ^ (prefixWord ++ tailWord_3781986).sum := by decide
  have hdescent : baseEnd_3781986 < baseStart_3781986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782030 : List Nat := [4, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5]
def baseStart_3782030 : Nat := 118140960795 + 3782030 * 2 ^ 59
def prefixEnd_3782030 : Nat := 4983230072969 + 3 ^ 40 * 3782030 * 2
def baseEnd_3782030 : Nat := 1941999239723943023931767

theorem tailTrace_3782030 : CollatzResearch.WordTrace tailWord_3782030 prefixEnd_3782030 1941999239723943023931767 := by
  unfold tailWord_3782030
  simp only [CollatzResearch.WordTrace]
  refine ⟨17242745811044838018105943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91961310992239136096565029 17242745811044838018105943)
  ·
    refine ⟨25864118716567257027158915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17242745811044838018105943 25864118716567257027158915)
    ·
      refine ⟨38796178074850885540738373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25864118716567257027158915 38796178074850885540738373)
      ·
        refine ⟨7274283389034541038888445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38796178074850885540738373 7274283389034541038888445)
        ·
          refine ⟨2727856270887952889583167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7274283389034541038888445 2727856270887952889583167)
          ·
            refine ⟨4091784406331929334374751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2727856270887952889583167 4091784406331929334374751)
            ·
              refine ⟨6137676609497894001562127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4091784406331929334374751 6137676609497894001562127)
              ·
                refine ⟨9206514914246841002343191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6137676609497894001562127 9206514914246841002343191)
                ·
                  refine ⟨13809772371370261503514787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9206514914246841002343191 13809772371370261503514787)
                  ·
                    refine ⟨20714658557055392255272181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13809772371370261503514787 20714658557055392255272181)
                    ·
                      refine ⟨1941999239723943023931767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20714658557055392255272181 1941999239723943023931767)
                      ·
                        rfl

theorem cell23_3782030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_3782030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782030 prefixEnd_3782030 := by exact prefixLift 3782030
  have htrace : WordTrace (prefixWord ++ tailWord_3782030) baseStart_3782030 baseEnd_3782030 := by
    simpa [prefixWord, tailWord_3782030, baseEnd_3782030] using wordTrace_append hprefix tailTrace_3782030
  have hstable : (prefixWord ++ tailWord_3782030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782030).length < 2 ^ (prefixWord ++ tailWord_3782030).sum := by decide
  have hdescent : baseEnd_3782030 < baseStart_3782030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782044 : List Nat := [2, 2, 3, 4, 1, 1, 1, 4, 1, 2, 2]
def baseStart_3782044 : Nat := 118140960795 + 3782044 * 2 ^ 59
def prefixEnd_3782044 : Nat := 4983230072969 + 3 ^ 40 * 3782044 * 2
def baseEnd_3782044 : Nat := 1942006428453105969156703

theorem tailTrace_3782044 : CollatzResearch.WordTrace tailWord_3782044 prefixEnd_3782044 1942006428453105969156703 := by
  unfold tailWord_3782044
  simp only [CollatzResearch.WordTrace]
  refine ⟨68971238555153992267928593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91961651406871989690571457 68971238555153992267928593)
  ·
    refine ⟨51728428916365494200946445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68971238555153992267928593 51728428916365494200946445)
    ·
      refine ⟨19398160843637060325354917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51728428916365494200946445 19398160843637060325354917)
      ·
        refine ⟨3637155158181948811004047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19398160843637060325354917 3637155158181948811004047)
        ·
          refine ⟨5455732737272923216506071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3637155158181948811004047 5455732737272923216506071)
          ·
            refine ⟨8183599105909384824759107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5455732737272923216506071 8183599105909384824759107)
            ·
              refine ⟨12275398658864077237138661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8183599105909384824759107 12275398658864077237138661)
              ·
                refine ⟨2301637248537014481963499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12275398658864077237138661 2301637248537014481963499)
                ·
                  refine ⟨3452455872805521722945249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2301637248537014481963499 3452455872805521722945249)
                  ·
                    refine ⟨2589341904604141292208937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3452455872805521722945249 2589341904604141292208937)
                    ·
                      refine ⟨1942006428453105969156703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2589341904604141292208937 1942006428453105969156703)
                      ·
                        rfl

theorem cell23_3782044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_3782044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782044 prefixEnd_3782044 := by exact prefixLift 3782044
  have htrace : WordTrace (prefixWord ++ tailWord_3782044) baseStart_3782044 baseEnd_3782044 := by
    simpa [prefixWord, tailWord_3782044, baseEnd_3782044] using wordTrace_append hprefix tailTrace_3782044
  have hstable : (prefixWord ++ tailWord_3782044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782044).length < 2 ^ (prefixWord ++ tailWord_3782044).sum := by decide
  have hdescent : baseEnd_3782044 < baseStart_3782044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782099 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 2, 9, 3]
def baseStart_3782099 : Nat := 118140960795 + 3782099 * 2 ^ 59
def prefixEnd_3782099 : Nat := 4983230072969 + 3 ^ 40 * 3782099 * 2
def baseEnd_3782099 : Nat := 1942034669889103253968949

theorem tailTrace_3782099 : CollatzResearch.WordTrace tailWord_3782099 prefixEnd_3782099 1942034669889103253968949 := by
  unfold tailWord_3782099
  simp only [CollatzResearch.WordTrace]
  refine ⟨137944483125108728929109351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91962988750072485952739567 137944483125108728929109351)
  ·
    refine ⟨206916724687663093393664027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137944483125108728929109351 206916724687663093393664027)
    ·
      refine ⟨310375087031494640090496041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206916724687663093393664027 310375087031494640090496041)
      ·
        refine ⟨232781315273620980067872031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310375087031494640090496041 232781315273620980067872031)
        ·
          refine ⟨349171972910431470101808047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232781315273620980067872031 349171972910431470101808047)
          ·
            refine ⟨523757959365647205152712071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349171972910431470101808047 523757959365647205152712071)
            ·
              refine ⟨785636939048470807729068107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523757959365647205152712071 785636939048470807729068107)
              ·
                refine ⟨1178455408572706211593602161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 785636939048470807729068107 1178455408572706211593602161)
                ·
                  refine ⟨883841556429529658695201621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1178455408572706211593602161 883841556429529658695201621)
                  ·
                    refine ⟨5178759119704275343917197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 883841556429529658695201621 5178759119704275343917197)
                    ·
                      refine ⟨1942034669889103253968949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5178759119704275343917197 1942034669889103253968949)
                      ·
                        rfl

theorem cell23_3782099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 9, 3].length) (baseStart_3782099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782099 prefixEnd_3782099 := by exact prefixLift 3782099
  have htrace : WordTrace (prefixWord ++ tailWord_3782099) baseStart_3782099 baseEnd_3782099 := by
    simpa [prefixWord, tailWord_3782099, baseEnd_3782099] using wordTrace_append hprefix tailTrace_3782099
  have hstable : (prefixWord ++ tailWord_3782099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782099).length < 2 ^ (prefixWord ++ tailWord_3782099).sum := by decide
  have hdescent : baseEnd_3782099 < baseStart_3782099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782106 : List Nat := [3, 1, 1, 2, 3, 3, 2, 1, 7]
def baseStart_3782106 : Nat := 118140960795 + 3782106 * 2 ^ 59
def prefixEnd_3782106 : Nat := 4983230072969 + 3 ^ 40 * 3782106 * 2
def baseEnd_3782106 : Nat := 215782029361520525175713

theorem tailTrace_3782106 : CollatzResearch.WordTrace tailWord_3782106 prefixEnd_3782106 215782029361520525175713 := by
  unfold tailWord_3782106
  simp only [CollatzResearch.WordTrace]
  refine ⟨34486184609020842281153543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91963158957388912749742781 34486184609020842281153543)
  ·
    refine ⟨51729276913531263421730315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34486184609020842281153543 51729276913531263421730315)
    ·
      refine ⟨77593915370296895132595473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51729276913531263421730315 77593915370296895132595473)
      ·
        refine ⟨58195436527722671349446605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77593915370296895132595473 58195436527722671349446605)
        ·
          refine ⟨21823288697896001756042477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58195436527722671349446605 21823288697896001756042477)
          ·
            refine ⟨8183733261711000658515929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21823288697896001756042477 8183733261711000658515929)
            ·
              refine ⟨6137799946283250493886947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8183733261711000658515929 6137799946283250493886947)
              ·
                refine ⟨9206699919424875740830421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6137799946283250493886947 9206699919424875740830421)
                ·
                  refine ⟨215782029361520525175713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9206699919424875740830421 215782029361520525175713)
                  ·
                    rfl

theorem cell23_3782106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 7].length) (baseStart_3782106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782106 prefixEnd_3782106 := by exact prefixLift 3782106
  have htrace : WordTrace (prefixWord ++ tailWord_3782106) baseStart_3782106 baseEnd_3782106 := by
    simpa [prefixWord, tailWord_3782106, baseEnd_3782106] using wordTrace_append hprefix tailTrace_3782106
  have hstable : (prefixWord ++ tailWord_3782106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782106).length < 2 ^ (prefixWord ++ tailWord_3782106).sum := by decide
  have hdescent : baseEnd_3782106 < baseStart_3782106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782157 : List Nat := [1, 7, 1, 1, 2, 2, 1, 1, 7]
def baseStart_3782157 : Nat := 118140960795 + 3782157 * 2 ^ 59
def prefixEnd_3782157 : Nat := 4983230072969 + 3 ^ 40 * 3782157 * 2
def baseEnd_3782157 : Nat := 215784939085229336338187

theorem tailTrace_3782157 : CollatzResearch.WordTrace tailWord_3782157 prefixEnd_3782157 215784939085229336338187 := by
  unfold tailWord_3782157
  simp only [CollatzResearch.WordTrace]
  refine ⟨137946598558898604834720725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91964399039265736556480483 137946598558898604834720725)
  ·
    refine ⟨3233123403724186050813767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 137946598558898604834720725 3233123403724186050813767)
    ·
      refine ⟨4849685105586279076220651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3233123403724186050813767 4849685105586279076220651)
      ·
        refine ⟨7274527658379418614330977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4849685105586279076220651 7274527658379418614330977)
        ·
          refine ⟨5455895743784563960748233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7274527658379418614330977 5455895743784563960748233)
          ·
            refine ⟨4091921807838422970561175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5455895743784563960748233 4091921807838422970561175)
            ·
              refine ⟨6137882711757634455841763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4091921807838422970561175 6137882711757634455841763)
              ·
                refine ⟨9206824067636451683762645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6137882711757634455841763 9206824067636451683762645)
                ·
                  refine ⟨215784939085229336338187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9206824067636451683762645 215784939085229336338187)
                  ·
                    rfl

theorem cell23_3782157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_3782157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782157 prefixEnd_3782157 := by exact prefixLift 3782157
  have htrace : WordTrace (prefixWord ++ tailWord_3782157) baseStart_3782157 baseEnd_3782157 := by
    simpa [prefixWord, tailWord_3782157, baseEnd_3782157] using wordTrace_append hprefix tailTrace_3782157
  have hstable : (prefixWord ++ tailWord_3782157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782157).length < 2 ^ (prefixWord ++ tailWord_3782157).sum := by decide
  have hdescent : baseEnd_3782157 < baseStart_3782157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782173 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 1, 6, 2]
def baseStart_3782173 : Nat := 118140960795 + 3782173 * 2 ^ 59
def prefixEnd_3782173 : Nat := 4983230072969 + 3 ^ 40 * 3782173 * 2
def baseEnd_3782173 : Nat := 1942072667457535964443609

theorem tailTrace_3782173 : CollatzResearch.WordTrace tailWord_3782173 prefixEnd_3782173 1942072667457535964443609 := by
  unfold tailWord_3782173
  simp only [CollatzResearch.WordTrace]
  refine ⟨137947182126840639567303173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91964788084560426378202115 137947182126840639567303173)
  ·
    refine ⟨25865096648782619918869345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137947182126840639567303173 25865096648782619918869345)
    ·
      refine ⟨19398822486586964939152009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25865096648782619918869345 19398822486586964939152009)
      ·
        refine ⟨14549116864940223704364007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19398822486586964939152009 14549116864940223704364007)
        ·
          refine ⟨21823675297410335556546011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14549116864940223704364007 21823675297410335556546011)
          ·
            refine ⟨32735512946115503334819017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21823675297410335556546011 32735512946115503334819017)
            ·
              refine ⟨24551634709586627501114263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32735512946115503334819017 24551634709586627501114263)
              ·
                refine ⟨36827452064379941251671395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24551634709586627501114263 36827452064379941251671395)
                ·
                  refine ⟨55241178096569911877507093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36827452064379941251671395 55241178096569911877507093)
                  ·
                    refine ⟨2589430223276714619258145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55241178096569911877507093 2589430223276714619258145)
                    ·
                      refine ⟨1942072667457535964443609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2589430223276714619258145 1942072667457535964443609)
                      ·
                        rfl

theorem cell23_3782173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_3782173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782173 prefixEnd_3782173 := by exact prefixLift 3782173
  have htrace : WordTrace (prefixWord ++ tailWord_3782173) baseStart_3782173 baseEnd_3782173 := by
    simpa [prefixWord, tailWord_3782173, baseEnd_3782173] using wordTrace_append hprefix tailTrace_3782173
  have hstable : (prefixWord ++ tailWord_3782173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782173).length < 2 ^ (prefixWord ++ tailWord_3782173).sum := by decide
  have hdescent : baseEnd_3782173 < baseStart_3782173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782190 : List Nat := [4, 1, 3, 1, 2, 2, 2, 1, 2, 1, 4]
def baseStart_3782190 : Nat := 118140960795 + 3782190 * 2 ^ 59
def prefixEnd_3782190 : Nat := 4983230072969 + 3 ^ 40 * 3782190 * 2
def baseEnd_3782190 : Nat := 1942081396628662397931031

theorem tailTrace_3782190 : CollatzResearch.WordTrace tailWord_3782190 prefixEnd_3782190 1942081396628662397931031 := by
  unfold tailWord_3782190
  simp only [CollatzResearch.WordTrace]
  refine ⟨17243475270972381433834003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91965201445186034313781349 17243475270972381433834003)
  ·
    refine ⟨25865212906458572150751005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17243475270972381433834003 25865212906458572150751005)
    ·
      refine ⟨9699454839921964556531627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25865212906458572150751005 9699454839921964556531627)
      ·
        refine ⟨14549182259882946834797441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9699454839921964556531627 14549182259882946834797441)
        ·
          refine ⟨10911886694912210126098081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14549182259882946834797441 10911886694912210126098081)
          ·
            refine ⟨8183915021184157594573561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10911886694912210126098081 8183915021184157594573561)
            ·
              refine ⟨6137936265888118195930171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8183915021184157594573561 6137936265888118195930171)
              ·
                refine ⟨9206904398832177293895257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6137936265888118195930171 9206904398832177293895257)
                ·
                  refine ⟨6905178299124132970421443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9206904398832177293895257 6905178299124132970421443)
                  ·
                    refine ⟨10357767448686199455632165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6905178299124132970421443 10357767448686199455632165)
                    ·
                      refine ⟨1942081396628662397931031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10357767448686199455632165 1942081396628662397931031)
                      ·
                        rfl

theorem cell23_3782190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_3782190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782190 prefixEnd_3782190 := by exact prefixLift 3782190
  have htrace : WordTrace (prefixWord ++ tailWord_3782190) baseStart_3782190 baseEnd_3782190 := by
    simpa [prefixWord, tailWord_3782190, baseEnd_3782190] using wordTrace_append hprefix tailTrace_3782190
  have hstable : (prefixWord ++ tailWord_3782190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782190).length < 2 ^ (prefixWord ++ tailWord_3782190).sum := by decide
  have hdescent : baseEnd_3782190 < baseStart_3782190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782223 : List Nat := [1, 1, 2, 1, 1, 2, 3, 5, 3, 1, 3]
def baseStart_3782223 : Nat := 118140960795 + 3782223 * 2 ^ 59
def prefixEnd_3782223 : Nat := 4983230072969 + 3 ^ 40 * 3782223 * 2
def baseEnd_3782223 : Nat := 1942098341490260768818379

theorem tailTrace_3782223 : CollatzResearch.WordTrace tailWord_3782223 prefixEnd_3782223 1942098341490260768818379 := by
  unfold tailWord_3782223
  simp only [CollatzResearch.WordTrace]
  refine ⟨137949005776659498106623323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91966003851106332071082215 137949005776659498106623323)
  ·
    refine ⟨206923508664989247159934985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137949005776659498106623323 206923508664989247159934985)
    ·
      refine ⟨155192631498741935369951239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206923508664989247159934985 155192631498741935369951239)
      ·
        refine ⟨232788947248112903054926859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155192631498741935369951239 232788947248112903054926859)
        ·
          refine ⟨349183420872169354582390289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232788947248112903054926859 349183420872169354582390289)
          ·
            refine ⟨261887565654127015936792717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349183420872169354582390289 261887565654127015936792717)
            ·
              refine ⟨98207837120297630976297269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261887565654127015936792717 98207837120297630976297269)
              ·
                refine ⟨9206984730027902904027869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98207837120297630976297269 9206984730027902904027869)
                ·
                  refine ⟨3452619273760463589010451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9206984730027902904027869 3452619273760463589010451)
                  ·
                    refine ⟨5178928910640695383515677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3452619273760463589010451 5178928910640695383515677)
                    ·
                      refine ⟨1942098341490260768818379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5178928910640695383515677 1942098341490260768818379)
                      ·
                        rfl

theorem cell23_3782223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 3, 1, 3].length) (baseStart_3782223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782223 prefixEnd_3782223 := by exact prefixLift 3782223
  have htrace : WordTrace (prefixWord ++ tailWord_3782223) baseStart_3782223 baseEnd_3782223 := by
    simpa [prefixWord, tailWord_3782223, baseEnd_3782223] using wordTrace_append hprefix tailTrace_3782223
  have hstable : (prefixWord ++ tailWord_3782223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782223).length < 2 ^ (prefixWord ++ tailWord_3782223).sum := by decide
  have hdescent : baseEnd_3782223 < baseStart_3782223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782233 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 4, 3, 2]
def baseStart_3782233 : Nat := 118140960795 + 3782233 * 2 ^ 59
def prefixEnd_3782233 : Nat := 4983230072969 + 3 ^ 40 * 3782233 * 2
def baseEnd_3782233 : Nat := 1942103476296805729693333

theorem tailTrace_3782233 : CollatzResearch.WordTrace tailWord_3782233 prefixEnd_3782233 1942103476296805729693333 := by
  unfold tailWord_3782233
  simp only [CollatzResearch.WordTrace]
  refine ⟨137949370506623269814487353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91966247004415513209658235 137949370506623269814487353)
  ·
    refine ⟨103462027879967452360865515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137949370506623269814487353 103462027879967452360865515)
    ·
      refine ⟨155193041819951178541298273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103462027879967452360865515 155193041819951178541298273)
      ·
        refine ⟨116394781364963383905973705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155193041819951178541298273 116394781364963383905973705)
        ·
          refine ⟨87296086023722537929480279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116394781364963383905973705 87296086023722537929480279)
          ·
            refine ⟨130944129035583806894220419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87296086023722537929480279 130944129035583806894220419)
            ·
              refine ⟨196416193553375710341330629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130944129035583806894220419 196416193553375710341330629)
              ·
                refine ⟨36828036291257945688999493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 196416193553375710341330629 36828036291257945688999493)
                ·
                  refine ⟨6905256804610864816687405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36828036291257945688999493 6905256804610864816687405)
                  ·
                    refine ⟨2589471301729074306257777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6905256804610864816687405 2589471301729074306257777)
                    ·
                      refine ⟨1942103476296805729693333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2589471301729074306257777 1942103476296805729693333)
                      ·
                        rfl

theorem cell23_3782233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 3, 2].length) (baseStart_3782233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782233 prefixEnd_3782233 := by exact prefixLift 3782233
  have htrace : WordTrace (prefixWord ++ tailWord_3782233) baseStart_3782233 baseEnd_3782233 := by
    simpa [prefixWord, tailWord_3782233, baseEnd_3782233] using wordTrace_append hprefix tailTrace_3782233
  have hstable : (prefixWord ++ tailWord_3782233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782233).length < 2 ^ (prefixWord ++ tailWord_3782233).sum := by decide
  have hdescent : baseEnd_3782233 < baseStart_3782233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782250 : List Nat := [3, 1, 3, 2, 1, 3, 1, 1, 1, 5, 2]
def baseStart_3782250 : Nat := 118140960795 + 3782250 * 2 ^ 59
def prefixEnd_3782250 : Nat := 4983230072969 + 3 ^ 40 * 3782250 * 2
def baseEnd_3782250 : Nat := 1942112205467932163180755

theorem tailTrace_3782250 : CollatzResearch.WordTrace tailWord_3782250 prefixEnd_3782250 1942112205467932163180755 := by
  unfold tailWord_3782250
  simp only [CollatzResearch.WordTrace]
  refine ⟨34487497636890420429464051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91966660365041121145237469 34487497636890420429464051)
  ·
    refine ⟨51731246455335630644196077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34487497636890420429464051 51731246455335630644196077)
    ·
      refine ⟨19399217420750861491573529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51731246455335630644196077 19399217420750861491573529)
      ·
        refine ⟨14549413065563146118680147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19399217420750861491573529 14549413065563146118680147)
        ·
          refine ⟨21824119598344719178020221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14549413065563146118680147 21824119598344719178020221)
          ·
            refine ⟨8184044849379269691757583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21824119598344719178020221 8184044849379269691757583)
            ·
              refine ⟨12276067274068904537636375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8184044849379269691757583 12276067274068904537636375)
              ·
                refine ⟨18414100911103356806454563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12276067274068904537636375 18414100911103356806454563)
                ·
                  refine ⟨27621151366655035209681845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18414100911103356806454563 27621151366655035209681845)
                  ·
                    refine ⟨2589482940623909550907673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27621151366655035209681845 2589482940623909550907673)
                    ·
                      refine ⟨1942112205467932163180755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2589482940623909550907673 1942112205467932163180755)
                      ·
                        rfl

theorem cell23_3782250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_3782250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782250 prefixEnd_3782250 := by exact prefixLift 3782250
  have htrace : WordTrace (prefixWord ++ tailWord_3782250) baseStart_3782250 baseEnd_3782250 := by
    simpa [prefixWord, tailWord_3782250, baseEnd_3782250] using wordTrace_append hprefix tailTrace_3782250
  have hstable : (prefixWord ++ tailWord_3782250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782250).length < 2 ^ (prefixWord ++ tailWord_3782250).sum := by decide
  have hdescent : baseEnd_3782250 < baseStart_3782250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782330 : List Nat := [3, 1, 1, 1, 2, 4, 2, 1, 4, 1, 3]
def baseStart_3782330 : Nat := 118140960795 + 3782330 * 2 ^ 59
def prefixEnd_3782330 : Nat := 4983230072969 + 3 ^ 40 * 3782330 * 2
def baseEnd_3782330 : Nat := 1942153283920291850180387

theorem tailTrace_3782330 : CollatzResearch.WordTrace tailWord_3782330 prefixEnd_3782330 1942153283920291850180387 := by
  unfold tailWord_3782330
  simp only [CollatzResearch.WordTrace]
  refine ⟨34488227096817963845192111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91968605591514570253845629 34488227096817963845192111)
  ·
    refine ⟨51732340645226945767788167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34488227096817963845192111 51732340645226945767788167)
    ·
      refine ⟨77598510967840418651682251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51732340645226945767788167 77598510967840418651682251)
      ·
        refine ⟨116397766451760627977523377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77598510967840418651682251 116397766451760627977523377)
        ·
          refine ⟨87298324838820470983142533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116397766451760627977523377 87298324838820470983142533)
          ·
            refine ⟨16368435907278838309339225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87298324838820470983142533 16368435907278838309339225)
            ·
              refine ⟨12276326930459128732004419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16368435907278838309339225 12276326930459128732004419)
              ·
                refine ⟨18414490395688693098006629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12276326930459128732004419 18414490395688693098006629)
                ·
                  refine ⟨3452716949191629955876243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18414490395688693098006629 3452716949191629955876243)
                  ·
                    refine ⟨5179075423787444933814365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3452716949191629955876243 5179075423787444933814365)
                    ·
                      refine ⟨1942153283920291850180387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5179075423787444933814365 1942153283920291850180387)
                      ·
                        rfl

theorem cell23_3782330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 4, 1, 3].length) (baseStart_3782330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782330 prefixEnd_3782330 := by exact prefixLift 3782330
  have htrace : WordTrace (prefixWord ++ tailWord_3782330) baseStart_3782330 baseEnd_3782330 := by
    simpa [prefixWord, tailWord_3782330, baseEnd_3782330] using wordTrace_append hprefix tailTrace_3782330
  have hstable : (prefixWord ++ tailWord_3782330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782330).length < 2 ^ (prefixWord ++ tailWord_3782330).sum := by decide
  have hdescent : baseEnd_3782330 < baseStart_3782330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782373 : List Nat := [1, 3, 1, 4, 1, 1, 1, 3, 2, 1, 5]
def baseStart_3782373 : Nat := 118140960795 + 3782373 * 2 ^ 59
def prefixEnd_3782373 : Nat := 4983230072969 + 3 ^ 40 * 3782373 * 2
def baseEnd_3782373 : Nat := 1942175363588435181942689

theorem tailTrace_3782373 : CollatzResearch.WordTrace tailWord_3782373 prefixEnd_3782373 1942175363588435181942689 := by
  unfold tailWord_3782373
  simp only [CollatzResearch.WordTrace]
  refine ⟨137954476726116073724583773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91969651150744049149722515 137954476726116073724583773)
  ·
    refine ⟨51732928772293527646718915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137954476726116073724583773 51732928772293527646718915)
    ·
      refine ⟨77599393158440291470078373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51732928772293527646718915 77599393158440291470078373)
      ·
        refine ⟨14549886217207554650639695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77599393158440291470078373 14549886217207554650639695)
        ·
          refine ⟨21824829325811331975959543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14549886217207554650639695 21824829325811331975959543)
          ·
            refine ⟨32737243988716997963939315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21824829325811331975959543 32737243988716997963939315)
            ·
              refine ⟨49105865983075496945908973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32737243988716997963939315 49105865983075496945908973)
              ·
                refine ⟨18414699743653311354715865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49105865983075496945908973 18414699743653311354715865)
                ·
                  refine ⟨13811024807739983516036899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18414699743653311354715865 13811024807739983516036899)
                  ·
                    refine ⟨20716537211609975274055349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13811024807739983516036899 20716537211609975274055349)
                    ·
                      refine ⟨1942175363588435181942689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20716537211609975274055349 1942175363588435181942689)
                      ·
                        rfl

theorem cell23_3782373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_3782373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782373 prefixEnd_3782373 := by exact prefixLift 3782373
  have htrace : WordTrace (prefixWord ++ tailWord_3782373) baseStart_3782373 baseEnd_3782373 := by
    simpa [prefixWord, tailWord_3782373, baseEnd_3782373] using wordTrace_append hprefix tailTrace_3782373
  have hstable : (prefixWord ++ tailWord_3782373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782373).length < 2 ^ (prefixWord ++ tailWord_3782373).sum := by decide
  have hdescent : baseEnd_3782373 < baseStart_3782373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782383 : List Nat := [1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 4]
def baseStart_3782383 : Nat := 118140960795 + 3782383 * 2 ^ 59
def prefixEnd_3782383 : Nat := 4983230072969 + 3 ^ 40 * 3782383 * 2
def baseEnd_3782383 : Nat := 1942180498394980142817643

theorem tailTrace_3782383 : CollatzResearch.WordTrace tailWord_3782383 prefixEnd_3782383 1942180498394980142817643 := by
  unfold tailWord_3782383
  simp only [CollatzResearch.WordTrace]
  refine ⟨137954841456079845432447803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91969894304053230288298535 137954841456079845432447803)
  ·
    refine ⟨206932262184119768148671705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137954841456079845432447803 206932262184119768148671705)
    ·
      refine ⟨155199196638089826111503779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206932262184119768148671705 155199196638089826111503779)
      ·
        refine ⟨232798794957134739167255669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155199196638089826111503779 232798794957134739167255669)
        ·
          refine ⟨21824887027231381796930219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 232798794957134739167255669 21824887027231381796930219)
          ·
            refine ⟨32737330540847072695395329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21824887027231381796930219 32737330540847072695395329)
            ·
              refine ⟨24552997905635304521546497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32737330540847072695395329 24552997905635304521546497)
              ·
                refine ⟨18414748429226478391159873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24552997905635304521546497 18414748429226478391159873)
                ·
                  refine ⟨13811061321919858793369905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18414748429226478391159873 13811061321919858793369905)
                  ·
                    refine ⟨10358295991439894095027429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13811061321919858793369905 10358295991439894095027429)
                    ·
                      refine ⟨1942180498394980142817643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10358295991439894095027429 1942180498394980142817643)
                      ·
                        rfl

theorem cell23_3782383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 4].length) (baseStart_3782383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782383 prefixEnd_3782383 := by exact prefixLift 3782383
  have htrace : WordTrace (prefixWord ++ tailWord_3782383) baseStart_3782383 baseEnd_3782383 := by
    simpa [prefixWord, tailWord_3782383, baseEnd_3782383] using wordTrace_append hprefix tailTrace_3782383
  have hstable : (prefixWord ++ tailWord_3782383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782383).length < 2 ^ (prefixWord ++ tailWord_3782383).sum := by decide
  have hdescent : baseEnd_3782383 < baseStart_3782383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782387 : List Nat := [1, 1, 1, 2, 2, 3, 3, 4, 2, 2, 2]
def baseStart_3782387 : Nat := 118140960795 + 3782387 * 2 ^ 59
def prefixEnd_3782387 : Nat := 4983230072969 + 3 ^ 40 * 3782387 * 2
def baseEnd_3782387 : Nat := 1942182552317598127167625

theorem tailTrace_3782387 : CollatzResearch.WordTrace tailWord_3782387 prefixEnd_3782387 1942182552317598127167625 := by
  unfold tailWord_3782387
  simp only [CollatzResearch.WordTrace]
  refine ⟨137954987348065354115593415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91969991565376902743728943 137954987348065354115593415)
  ·
    refine ⟨206932481022098031173390123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137954987348065354115593415 206932481022098031173390123)
    ·
      refine ⟨310398721533147046760085185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206932481022098031173390123 310398721533147046760085185)
      ·
        refine ⟨232799041149860285070063889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310398721533147046760085185 232799041149860285070063889)
        ·
          refine ⟨174599280862395213802547917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232799041149860285070063889 174599280862395213802547917)
          ·
            refine ⟨65474730323398205175955469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174599280862395213802547917 65474730323398205175955469)
            ·
              refine ⟨24553023871274326940983301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65474730323398205175955469 24553023871274326940983301)
              ·
                refine ⟨4603691975863936301434369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24553023871274326940983301 4603691975863936301434369)
                ·
                  refine ⟨3452768981897952226075777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4603691975863936301434369 3452768981897952226075777)
                  ·
                    refine ⟨2589576736423464169556833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3452768981897952226075777 2589576736423464169556833)
                    ·
                      refine ⟨1942182552317598127167625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2589576736423464169556833 1942182552317598127167625)
                      ·
                        rfl

theorem cell23_3782387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 2, 2, 2].length) (baseStart_3782387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782387 prefixEnd_3782387 := by exact prefixLift 3782387
  have htrace : WordTrace (prefixWord ++ tailWord_3782387) baseStart_3782387 baseEnd_3782387 := by
    simpa [prefixWord, tailWord_3782387, baseEnd_3782387] using wordTrace_append hprefix tailTrace_3782387
  have hstable : (prefixWord ++ tailWord_3782387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782387).length < 2 ^ (prefixWord ++ tailWord_3782387).sum := by decide
  have hdescent : baseEnd_3782387 < baseStart_3782387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782390 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3]
def baseStart_3782390 : Nat := 118140960795 + 3782390 * 2 ^ 59
def prefixEnd_3782390 : Nat := 4983230072969 + 3 ^ 40 * 3782390 * 2
def baseEnd_3782390 : Nat := 1942184092759561615430111

theorem tailTrace_3782390 : CollatzResearch.WordTrace tailWord_3782390 prefixEnd_3782390 1942184092759561615430111 := by
  unfold tailWord_3782390
  simp only [CollatzResearch.WordTrace]
  refine ⟨8622193547940905351747039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91970064511369657085301749 8622193547940905351747039)
  ·
    refine ⟨12933290321911358027620559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8622193547940905351747039 12933290321911358027620559)
    ·
      refine ⟨19399935482867037041430839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12933290321911358027620559 19399935482867037041430839)
      ·
        refine ⟨29099903224300555562146259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19399935482867037041430839 29099903224300555562146259)
        ·
          refine ⟨43649854836450833343219389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29099903224300555562146259 43649854836450833343219389)
          ·
            refine ⟨16368695563669062503707271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43649854836450833343219389 16368695563669062503707271)
            ·
              refine ⟨24553043345503593755560907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16368695563669062503707271 24553043345503593755560907)
              ·
                refine ⟨36829565018255390633341361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24553043345503593755560907 36829565018255390633341361)
                ·
                  refine ⟨27622173763691542975006021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36829565018255390633341361 27622173763691542975006021)
                  ·
                    refine ⟨5179157580692164307813629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27622173763691542975006021 5179157580692164307813629)
                    ·
                      refine ⟨1942184092759561615430111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5179157580692164307813629 1942184092759561615430111)
                      ·
                        rfl

theorem cell23_3782390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_3782390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782390 prefixEnd_3782390 := by exact prefixLift 3782390
  have htrace : WordTrace (prefixWord ++ tailWord_3782390) baseStart_3782390 baseEnd_3782390 := by
    simpa [prefixWord, tailWord_3782390, baseEnd_3782390] using wordTrace_append hprefix tailTrace_3782390
  have hstable : (prefixWord ++ tailWord_3782390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782390).length < 2 ^ (prefixWord ++ tailWord_3782390).sum := by decide
  have hdescent : baseEnd_3782390 < baseStart_3782390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782403 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 1, 5, 3]
def baseStart_3782403 : Nat := 118140960795 + 3782403 * 2 ^ 59
def prefixEnd_3782403 : Nat := 4983230072969 + 3 ^ 40 * 3782403 * 2
def baseEnd_3782403 : Nat := 1942190768008070064567551

theorem tailTrace_3782403 : CollatzResearch.WordTrace tailWord_3782403 prefixEnd_3782403 1942190768008070064567551 := by
  unfold tailWord_3782403
  simp only [CollatzResearch.WordTrace]
  refine ⟨137955570916007388848175863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91970380610671592565450575 137955570916007388848175863)
  ·
    refine ⟨206933356374011083272263795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137955570916007388848175863 206933356374011083272263795)
    ·
      refine ⟨310400034561016624908395693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206933356374011083272263795 310400034561016624908395693)
      ·
        refine ⟨116400012960381234340648385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310400034561016624908395693 116400012960381234340648385)
        ·
          refine ⟨87300009720285925755486289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116400012960381234340648385 87300009720285925755486289)
          ·
            refine ⟨65475007290214444316614717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87300009720285925755486289 65475007290214444316614717)
            ·
              refine ⟨24553127733830416618730519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65475007290214444316614717 24553127733830416618730519)
              ·
                refine ⟨36829691600745624928095779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24553127733830416618730519 36829691600745624928095779)
                ·
                  refine ⟨55244537401118437392143669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36829691600745624928095779 55244537401118437392143669)
                  ·
                    refine ⟨5179175381354853505513469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55244537401118437392143669 5179175381354853505513469)
                    ·
                      refine ⟨1942190768008070064567551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5179175381354853505513469 1942190768008070064567551)
                      ·
                        rfl

theorem cell23_3782403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 5, 3].length) (baseStart_3782403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782403 prefixEnd_3782403 := by exact prefixLift 3782403
  have htrace : WordTrace (prefixWord ++ tailWord_3782403) baseStart_3782403 baseEnd_3782403 := by
    simpa [prefixWord, tailWord_3782403, baseEnd_3782403] using wordTrace_append hprefix tailTrace_3782403
  have hstable : (prefixWord ++ tailWord_3782403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782403).length < 2 ^ (prefixWord ++ tailWord_3782403).sum := by decide
  have hdescent : baseEnd_3782403 < baseStart_3782403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782404 : List Nat := [2, 3, 2, 2, 1, 2, 2, 3, 2, 2, 2]
def baseStart_3782404 : Nat := 118140960795 + 3782404 * 2 ^ 59
def prefixEnd_3782404 : Nat := 4983230072969 + 3 ^ 40 * 3782404 * 2
def baseEnd_3782404 : Nat := 1942191281488724560655047

theorem tailTrace_3782404 : CollatzResearch.WordTrace tailWord_3782404 prefixEnd_3782404 1942191281488724560655047 := by
  unfold tailWord_3782404
  simp only [CollatzResearch.WordTrace]
  refine ⟨68977803694501883009481133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91970404926002510679308177 68977803694501883009481133)
  ·
    refine ⟨25866676385438206128555425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68977803694501883009481133 25866676385438206128555425)
    ·
      refine ⟨19400007289078654596416569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25866676385438206128555425 19400007289078654596416569)
      ·
        refine ⟨14550005466808990947312427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19400007289078654596416569 14550005466808990947312427)
        ·
          refine ⟨21825008200213486420968641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14550005466808990947312427 21825008200213486420968641)
          ·
            refine ⟨16368756150160114815726481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21825008200213486420968641 16368756150160114815726481)
            ·
              refine ⟨12276567112620086111794861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16368756150160114815726481 12276567112620086111794861)
              ·
                refine ⟨4603712667232532291923073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12276567112620086111794861 4603712667232532291923073)
                ·
                  refine ⟨3452784500424399218942305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4603712667232532291923073 3452784500424399218942305)
                  ·
                    refine ⟨2589588375318299414206729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3452784500424399218942305 2589588375318299414206729)
                    ·
                      refine ⟨1942191281488724560655047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2589588375318299414206729 1942191281488724560655047)
                      ·
                        rfl

theorem cell23_3782404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_3782404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782404 prefixEnd_3782404 := by exact prefixLift 3782404
  have htrace : WordTrace (prefixWord ++ tailWord_3782404) baseStart_3782404 baseEnd_3782404 := by
    simpa [prefixWord, tailWord_3782404, baseEnd_3782404] using wordTrace_append hprefix tailTrace_3782404
  have hstable : (prefixWord ++ tailWord_3782404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782404).length < 2 ^ (prefixWord ++ tailWord_3782404).sum := by decide
  have hdescent : baseEnd_3782404 < baseStart_3782404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782473 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 2, 4, 4]
def baseStart_3782473 : Nat := 118140960795 + 3782473 * 2 ^ 59
def prefixEnd_3782473 : Nat := 4983230072969 + 3 ^ 40 * 3782473 * 2
def baseEnd_3782473 : Nat := 1942226711653884790692229

theorem tailTrace_3782473 : CollatzResearch.WordTrace tailWord_3782473 prefixEnd_3782473 1942226711653884790692229 := by
  unfold tailWord_3782473
  simp only [CollatzResearch.WordTrace]
  refine ⟨137958124025753790803224073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91972082683835860535482715 137958124025753790803224073)
  ·
    refine ⟨103468593019315343102418055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137958124025753790803224073 103468593019315343102418055)
    ·
      refine ⟨155202889528973014653627083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103468593019315343102418055 155202889528973014653627083)
      ·
        refine ⟨232804334293459521980440625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155202889528973014653627083 232804334293459521980440625)
        ·
          refine ⟨174603250720094641485330469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232804334293459521980440625 174603250720094641485330469)
          ·
            refine ⟨32738109510017745278499463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174603250720094641485330469 32738109510017745278499463)
            ·
              refine ⟨49107164265026617917749195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32738109510017745278499463 49107164265026617917749195)
              ·
                refine ⟨73660746397539926876623793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49107164265026617917749195 73660746397539926876623793)
                ·
                  refine ⟨55245559798154945157467845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73660746397539926876623793 55245559798154945157467845)
                  ·
                    refine ⟨10358542462154052217025221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55245559798154945157467845 10358542462154052217025221)
                    ·
                      refine ⟨1942226711653884790692229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10358542462154052217025221 1942226711653884790692229)
                      ·
                        rfl

theorem cell23_3782473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 4, 4].length) (baseStart_3782473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782473 prefixEnd_3782473 := by exact prefixLift 3782473
  have htrace : WordTrace (prefixWord ++ tailWord_3782473) baseStart_3782473 baseEnd_3782473 := by
    simpa [prefixWord, tailWord_3782473, baseEnd_3782473] using wordTrace_append hprefix tailTrace_3782473
  have hstable : (prefixWord ++ tailWord_3782473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782473).length < 2 ^ (prefixWord ++ tailWord_3782473).sum := by decide
  have hdescent : baseEnd_3782473 < baseStart_3782473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782477 : List Nat := [1, 6, 1, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_3782477 : Nat := 118140960795 + 3782477 * 2 ^ 59
def prefixEnd_3782477 : Nat := 4983230072969 + 3 ^ 40 * 3782477 * 2
def baseEnd_3782477 : Nat := 1942228765576502775042211

theorem tailTrace_3782477 : CollatzResearch.WordTrace tailWord_3782477 prefixEnd_3782477 1942228765576502775042211 := by
  unfold tailWord_3782477
  simp only [CollatzResearch.WordTrace]
  refine ⟨137958269917739299486369685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91972179945159532990913123 137958269917739299486369685)
  ·
    refine ⟨6466793902394029663423579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 137958269917739299486369685 6466793902394029663423579)
    ·
      refine ⟨9700190853591044495135369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6466793902394029663423579 9700190853591044495135369)
      ·
        refine ⟨7275143140193283371351527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9700190853591044495135369 7275143140193283371351527)
        ·
          refine ⟨10912714710289925057027291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7275143140193283371351527 10912714710289925057027291)
          ·
            refine ⟨16369072065434887585540937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10912714710289925057027291 16369072065434887585540937)
            ·
              refine ⟨12276804049076165689155703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16369072065434887585540937 12276804049076165689155703)
              ·
                refine ⟨18415206073614248533733555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12276804049076165689155703 18415206073614248533733555)
                ·
                  refine ⟨27622809110421372800600333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18415206073614248533733555 27622809110421372800600333)
                  ·
                    refine ⟨10358553416408014800225125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27622809110421372800600333 10358553416408014800225125)
                    ·
                      refine ⟨1942228765576502775042211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10358553416408014800225125 1942228765576502775042211)
                      ·
                        rfl

theorem cell23_3782477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_3782477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782477 prefixEnd_3782477 := by exact prefixLift 3782477
  have htrace : WordTrace (prefixWord ++ tailWord_3782477) baseStart_3782477 baseEnd_3782477 := by
    simpa [prefixWord, tailWord_3782477, baseEnd_3782477] using wordTrace_append hprefix tailTrace_3782477
  have hstable : (prefixWord ++ tailWord_3782477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782477).length < 2 ^ (prefixWord ++ tailWord_3782477).sum := by decide
  have hdescent : baseEnd_3782477 < baseStart_3782477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782480 : List Nat := [2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 3]
def baseStart_3782480 : Nat := 118140960795 + 3782480 * 2 ^ 59
def prefixEnd_3782480 : Nat := 4983230072969 + 3 ^ 40 * 3782480 * 2
def baseEnd_3782480 : Nat := 1942230306018466263304697

theorem tailTrace_3782480 : CollatzResearch.WordTrace tailWord_3782480 prefixEnd_3782480 1942230306018466263304697 := by
  unfold tailWord_3782480
  simp only [CollatzResearch.WordTrace]
  refine ⟨68979189668364215499364447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91972252891152287332485929 68979189668364215499364447)
  ·
    refine ⟨103468784502546323249046671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68979189668364215499364447 103468784502546323249046671)
    ·
      refine ⟨155203176753819484873570007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103468784502546323249046671 155203176753819484873570007)
      ·
        refine ⟨232804765130729227310355011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155203176753819484873570007 232804765130729227310355011)
        ·
          refine ⟨349207147696093840965532517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232804765130729227310355011 349207147696093840965532517)
          ·
            refine ⟨65476340193017595181037347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 349207147696093840965532517 65476340193017595181037347)
            ·
              refine ⟨98214510289526392771556021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65476340193017595181037347 98214510289526392771556021)
              ·
                refine ⟨9207610339643099322333377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98214510289526392771556021 9207610339643099322333377)
                ·
                  refine ⟨6905707754732324491750033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9207610339643099322333377 6905707754732324491750033)
                  ·
                    refine ⟨5179280816049243368812525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6905707754732324491750033 5179280816049243368812525)
                    ·
                      refine ⟨1942230306018466263304697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5179280816049243368812525 1942230306018466263304697)
                      ·
                        rfl

theorem cell23_3782480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 3].length) (baseStart_3782480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782480 prefixEnd_3782480 := by exact prefixLift 3782480
  have htrace : WordTrace (prefixWord ++ tailWord_3782480) baseStart_3782480 baseEnd_3782480 := by
    simpa [prefixWord, tailWord_3782480, baseEnd_3782480] using wordTrace_append hprefix tailTrace_3782480
  have hstable : (prefixWord ++ tailWord_3782480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782480).length < 2 ^ (prefixWord ++ tailWord_3782480).sum := by decide
  have hdescent : baseEnd_3782480 < baseStart_3782480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782554 : List Nat := [3, 1, 1, 4, 2, 1, 2, 2, 2, 3, 2]
def baseStart_3782554 : Nat := 118140960795 + 3782554 * 2 ^ 59
def prefixEnd_3782554 : Nat := 4983230072969 + 3 ^ 40 * 3782554 * 2
def baseEnd_3782554 : Nat := 1942268303586898973779357

theorem tailTrace_3782554 : CollatzResearch.WordTrace tailWord_3782554 prefixEnd_3782554 1942268303586898973779357 := by
  unfold tailWord_3782554
  simp only [CollatzResearch.WordTrace]
  refine ⟨34490269584615085409230679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91974052225640227757948477 34490269584615085409230679)
  ·
    refine ⟨51735404376922628113846019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34490269584615085409230679 51735404376922628113846019)
    ·
      refine ⟨77603106565383942170769029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51735404376922628113846019 77603106565383942170769029)
      ·
        refine ⟨14550582481009489157019193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77603106565383942170769029 14550582481009489157019193)
        ·
          refine ⟨10912936860757116867764395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14550582481009489157019193 10912936860757116867764395)
          ·
            refine ⟨16369405291135675301646593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10912936860757116867764395 16369405291135675301646593)
            ·
              refine ⟨12277053968351756476234945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16369405291135675301646593 12277053968351756476234945)
              ·
                refine ⟨9207790476263817357176209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12277053968351756476234945 9207790476263817357176209)
                ·
                  refine ⟨6905842857197863017882157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9207790476263817357176209 6905842857197863017882157)
                  ·
                    refine ⟨2589691071449198631705809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6905842857197863017882157 2589691071449198631705809)
                    ·
                      refine ⟨1942268303586898973779357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2589691071449198631705809 1942268303586898973779357)
                      ·
                        rfl

theorem cell23_3782554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_3782554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782554 prefixEnd_3782554 := by exact prefixLift 3782554
  have htrace : WordTrace (prefixWord ++ tailWord_3782554) baseStart_3782554 baseEnd_3782554 := by
    simpa [prefixWord, tailWord_3782554, baseEnd_3782554] using wordTrace_append hprefix tailTrace_3782554
  have hstable : (prefixWord ++ tailWord_3782554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782554).length < 2 ^ (prefixWord ++ tailWord_3782554).sum := by decide
  have hdescent : baseEnd_3782554 < baseStart_3782554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782567 : List Nat := [1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_3782567 : Nat := 118140960795 + 3782567 * 2 ^ 59
def prefixEnd_3782567 : Nat := 4983230072969 + 3 ^ 40 * 3782567 * 2
def baseEnd_3782567 : Nat := 1942274978835407422916797

theorem tailTrace_3782567 : CollatzResearch.WordTrace tailWord_3782567 prefixEnd_3782567 1942274978835407422916797 := by
  unfold tailWord_3782567
  simp only [CollatzResearch.WordTrace]
  refine ⟨137961552487413244857145955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91974368324942163238097303 137961552487413244857145955)
  ·
    refine ⟨206942328731119867285718933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137961552487413244857145955 206942328731119867285718933)
    ·
      refine ⟨9700421659271243779018075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 206942328731119867285718933 9700421659271243779018075)
      ·
        refine ⟨14550632488906865668527113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9700421659271243779018075 14550632488906865668527113)
        ·
          refine ⟨10912974366680149251395335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14550632488906865668527113 10912974366680149251395335)
          ·
            refine ⟨16369461550020223877093003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10912974366680149251395335 16369461550020223877093003)
            ·
              refine ⟨24554192325030335815639505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16369461550020223877093003 24554192325030335815639505)
              ·
                refine ⟨18415644243772751861729629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24554192325030335815639505 18415644243772751861729629)
                ·
                  refine ⟨6905866591414781948148611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18415644243772751861729629 6905866591414781948148611)
                  ·
                    refine ⟨10358799887122172922222917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6905866591414781948148611 10358799887122172922222917)
                    ·
                      refine ⟨1942274978835407422916797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10358799887122172922222917 1942274978835407422916797)
                      ·
                        rfl

theorem cell23_3782567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_3782567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782567 prefixEnd_3782567 := by exact prefixLift 3782567
  have htrace : WordTrace (prefixWord ++ tailWord_3782567) baseStart_3782567 baseEnd_3782567 := by
    simpa [prefixWord, tailWord_3782567, baseEnd_3782567] using wordTrace_append hprefix tailTrace_3782567
  have hstable : (prefixWord ++ tailWord_3782567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782567).length < 2 ^ (prefixWord ++ tailWord_3782567).sum := by decide
  have hdescent : baseEnd_3782567 < baseStart_3782567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782577 : List Nat := [1, 2, 2, 4, 2, 2, 2, 1, 1, 6]
def baseStart_3782577 : Nat := 118140960795 + 3782577 * 2 ^ 59
def prefixEnd_3782577 : Nat := 4983230072969 + 3 ^ 40 * 3782577 * 2
def baseEnd_3782577 : Nat := 647426704547317461263917

theorem tailTrace_3782577 : CollatzResearch.WordTrace tailWord_3782577 prefixEnd_3782577 647426704547317461263917 := by
  unfold tailWord_3782577
  simp only [CollatzResearch.WordTrace]
  refine ⟨137961917217377016565009985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91974611478251344376673323 137961917217377016565009985)
  ·
    refine ⟨103471437913032762423757489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137961917217377016565009985 103471437913032762423757489)
    ·
      refine ⟨77603578434774571817818117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103471437913032762423757489 77603578434774571817818117)
      ·
        refine ⟨14550670956520232215840897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77603578434774571817818117 14550670956520232215840897)
        ·
          refine ⟨10913003217390174161880673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14550670956520232215840897 10913003217390174161880673)
          ·
            refine ⟨8184752413042630621410505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10913003217390174161880673 8184752413042630621410505)
            ·
              refine ⟨6138564309781972966057879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8184752413042630621410505 6138564309781972966057879)
              ·
                refine ⟨9207846464672959449086819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6138564309781972966057879 9207846464672959449086819)
                ·
                  refine ⟨13811769697009439173630229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9207846464672959449086819 13811769697009439173630229)
                  ·
                    refine ⟨647426704547317461263917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13811769697009439173630229 647426704547317461263917)
                    ·
                      rfl

theorem cell23_3782577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 6].length) (baseStart_3782577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782577 prefixEnd_3782577 := by exact prefixLift 3782577
  have htrace : WordTrace (prefixWord ++ tailWord_3782577) baseStart_3782577 baseEnd_3782577 := by
    simpa [prefixWord, tailWord_3782577, baseEnd_3782577] using wordTrace_append hprefix tailTrace_3782577
  have hstable : (prefixWord ++ tailWord_3782577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782577).length < 2 ^ (prefixWord ++ tailWord_3782577).sum := by decide
  have hdescent : baseEnd_3782577 < baseStart_3782577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782584 : List Nat := [2, 1, 2, 1, 2, 3, 3, 2, 3, 2, 2]
def baseStart_3782584 : Nat := 118140960795 + 3782584 * 2 ^ 59
def prefixEnd_3782584 : Nat := 4983230072969 + 3 ^ 40 * 3782584 * 2
def baseEnd_3782584 : Nat := 1942283708006533856404219

theorem tailTrace_3782584 : CollatzResearch.WordTrace tailWord_3782584 prefixEnd_3782584 1942283708006533856404219 := by
  unfold tailWord_3782584
  simp only [CollatzResearch.WordTrace]
  refine ⟨68981086264175828380257403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91974781685567771173676537 68981086264175828380257403)
  ·
    refine ⟨103471629396263742570386105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68981086264175828380257403 103471629396263742570386105)
    ·
      refine ⟨77603722047197806927789579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103471629396263742570386105 77603722047197806927789579)
      ·
        refine ⟨116405583070796710391684369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77603722047197806927789579 116405583070796710391684369)
        ·
          refine ⟨87304187303097532793763277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116405583070796710391684369 87304187303097532793763277)
          ·
            refine ⟨32739070238661574797661229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87304187303097532793763277 32739070238661574797661229)
            ·
              refine ⟨12277151339498090549122961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32739070238661574797661229 12277151339498090549122961)
              ·
                refine ⟨9207863504623567911842221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12277151339498090549122961 9207863504623567911842221)
                ·
                  refine ⟨3452948814233837966940833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9207863504623567911842221 3452948814233837966940833)
                  ·
                    refine ⟨2589711610675378475205625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3452948814233837966940833 2589711610675378475205625)
                    ·
                      refine ⟨1942283708006533856404219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2589711610675378475205625 1942283708006533856404219)
                      ·
                        rfl

theorem cell23_3782584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 3, 2, 2].length) (baseStart_3782584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782584 prefixEnd_3782584 := by exact prefixLift 3782584
  have htrace : WordTrace (prefixWord ++ tailWord_3782584) baseStart_3782584 baseEnd_3782584 := by
    simpa [prefixWord, tailWord_3782584, baseEnd_3782584] using wordTrace_append hprefix tailTrace_3782584
  have hstable : (prefixWord ++ tailWord_3782584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782584).length < 2 ^ (prefixWord ++ tailWord_3782584).sum := by decide
  have hdescent : baseEnd_3782584 < baseStart_3782584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782588 : List Nat := [2, 2, 2, 5, 1, 2, 1, 1, 2, 3, 2]
def baseStart_3782588 : Nat := 118140960795 + 3782588 * 2 ^ 59
def prefixEnd_3782588 : Nat := 4983230072969 + 3 ^ 40 * 3782588 * 2
def baseEnd_3782588 : Nat := 1942285761929151840754201

theorem tailTrace_3782588 : CollatzResearch.WordTrace tailWord_3782588 prefixEnd_3782588 1942285761929151840754201 := by
  unfold tailWord_3782588
  simp only [CollatzResearch.WordTrace]
  refine ⟨68981159210168582721830209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91974878946891443629106945 68981159210168582721830209)
  ·
    refine ⟨51735869407626437041372657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68981159210168582721830209 51735869407626437041372657)
    ·
      refine ⟨38801902055719827781029493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51735869407626437041372657 38801902055719827781029493)
      ·
        refine ⟨3637678317723733854471515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38801902055719827781029493 3637678317723733854471515)
        ·
          refine ⟨5456517476585600781707273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3637678317723733854471515 5456517476585600781707273)
          ·
            refine ⟨4092388107439200586280455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5456517476585600781707273 4092388107439200586280455)
            ·
              refine ⟨6138582161158800879420683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4092388107439200586280455 6138582161158800879420683)
              ·
                refine ⟨9207873241738201319131025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6138582161158800879420683 9207873241738201319131025)
                ·
                  refine ⟨6905904931303650989348269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9207873241738201319131025 6905904931303650989348269)
                  ·
                    refine ⟨2589714349238869121005601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6905904931303650989348269 2589714349238869121005601)
                    ·
                      refine ⟨1942285761929151840754201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2589714349238869121005601 1942285761929151840754201)
                      ·
                        rfl

theorem cell23_3782588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_3782588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782588 prefixEnd_3782588 := by exact prefixLift 3782588
  have htrace : WordTrace (prefixWord ++ tailWord_3782588) baseStart_3782588 baseEnd_3782588 := by
    simpa [prefixWord, tailWord_3782588, baseEnd_3782588] using wordTrace_append hprefix tailTrace_3782588
  have hstable : (prefixWord ++ tailWord_3782588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782588).length < 2 ^ (prefixWord ++ tailWord_3782588).sum := by decide
  have hdescent : baseEnd_3782588 < baseStart_3782588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782604 : List Nat := [2, 2, 1, 4, 1, 3, 1, 3, 1, 2, 3]
def baseStart_3782604 : Nat := 118140960795 + 3782604 * 2 ^ 59
def prefixEnd_3782604 : Nat := 4983230072969 + 3 ^ 40 * 3782604 * 2
def baseEnd_3782604 : Nat := 1942293977619623778154127

theorem tailTrace_3782604 : CollatzResearch.WordTrace tailWord_3782604 prefixEnd_3782604 1942293977619623778154127 := by
  unfold tailWord_3782604
  simp only [CollatzResearch.WordTrace]
  refine ⟨68981450994139600088121433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91975267992186133450828577 68981450994139600088121433)
  ·
    refine ⟨51736088245604700066091075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68981450994139600088121433 51736088245604700066091075)
    ·
      refine ⟨77604132368407050099136613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51736088245604700066091075 77604132368407050099136613)
      ·
        refine ⟨14550774819076321893588115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77604132368407050099136613 14550774819076321893588115)
        ·
          refine ⟨21826162228614482840382173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14550774819076321893588115 21826162228614482840382173)
          ·
            refine ⟨8184810835730431065143315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21826162228614482840382173 8184810835730431065143315)
            ·
              refine ⟨12277216253595646597714973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8184810835730431065143315 12277216253595646597714973)
              ·
                refine ⟨4603956095098367474143115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12277216253595646597714973 4603956095098367474143115)
                ·
                  refine ⟨6905934142647551211214673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4603956095098367474143115 6905934142647551211214673)
                  ·
                    refine ⟨5179450606985663408411005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6905934142647551211214673 5179450606985663408411005)
                    ·
                      refine ⟨1942293977619623778154127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5179450606985663408411005 1942293977619623778154127)
                      ·
                        rfl

theorem cell23_3782604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_3782604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782604 prefixEnd_3782604 := by exact prefixLift 3782604
  have htrace : WordTrace (prefixWord ++ tailWord_3782604) baseStart_3782604 baseEnd_3782604 := by
    simpa [prefixWord, tailWord_3782604, baseEnd_3782604] using wordTrace_append hprefix tailTrace_3782604
  have hstable : (prefixWord ++ tailWord_3782604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782604).length < 2 ^ (prefixWord ++ tailWord_3782604).sum := by decide
  have hdescent : baseEnd_3782604 < baseStart_3782604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782631 : List Nat := [1, 1, 5, 2, 4, 1, 1, 1, 1, 2, 4]
def baseStart_3782631 : Nat := 118140960795 + 3782631 * 2 ^ 59
def prefixEnd_3782631 : Nat := 4983230072969 + 3 ^ 40 * 3782631 * 2
def baseEnd_3782631 : Nat := 1942307841597295172516503

theorem tailTrace_3782631 : CollatzResearch.WordTrace tailWord_3782631 prefixEnd_3782631 1942307841597295172516503 := by
  unfold tailWord_3782631
  simp only [CollatzResearch.WordTrace]
  refine ⟨137963886759181383787475747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91975924506120922524983831 137963886759181383787475747)
  ·
    refine ⟨206945830138772075681213621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137963886759181383787475747 206945830138772075681213621)
    ·
      refine ⟨19401171575509882095113777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 206945830138772075681213621 19401171575509882095113777)
      ·
        refine ⟨14550878681632411571335333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19401171575509882095113777 14550878681632411571335333)
        ·
          refine ⟨2728289752806077169625375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14550878681632411571335333 2728289752806077169625375)
          ·
            refine ⟨4092434629209115754438063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2728289752806077169625375 4092434629209115754438063)
            ·
              refine ⟨6138651943813673631657095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4092434629209115754438063 6138651943813673631657095)
              ·
                refine ⟨9207977915720510447485643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6138651943813673631657095 9207977915720510447485643)
                ·
                  refine ⟨13811966873580765671228465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9207977915720510447485643 13811966873580765671228465)
                  ·
                    refine ⟨10358975155185574253421349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13811966873580765671228465 10358975155185574253421349)
                    ·
                      refine ⟨1942307841597295172516503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10358975155185574253421349 1942307841597295172516503)
                      ·
                        rfl

theorem cell23_3782631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_3782631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782631 prefixEnd_3782631 := by exact prefixLift 3782631
  have htrace : WordTrace (prefixWord ++ tailWord_3782631) baseStart_3782631 baseEnd_3782631 := by
    simpa [prefixWord, tailWord_3782631, baseEnd_3782631] using wordTrace_append hprefix tailTrace_3782631
  have hstable : (prefixWord ++ tailWord_3782631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782631).length < 2 ^ (prefixWord ++ tailWord_3782631).sum := by decide
  have hdescent : baseEnd_3782631 < baseStart_3782631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782640 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 4]
def baseStart_3782640 : Nat := 118140960795 + 3782640 * 2 ^ 59
def prefixEnd_3782640 : Nat := 4983230072969 + 3 ^ 40 * 3782640 * 2
def baseEnd_3782640 : Nat := 1942312462923185637303961

theorem tailTrace_3782640 : CollatzResearch.WordTrace tailWord_3782640 prefixEnd_3782640 1942312462923185637303961 := by
  unfold tailWord_3782640
  simp only [CollatzResearch.WordTrace]
  refine ⟨68982107508074389162276687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91976143344099185549702249 68982107508074389162276687)
  ·
    refine ⟨103473161262111583743415031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68982107508074389162276687 103473161262111583743415031)
    ·
      refine ⟨155209741893167375615122547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103473161262111583743415031 155209741893167375615122547)
      ·
        refine ⟨232814612839751063422683821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155209741893167375615122547 232814612839751063422683821)
        ·
          refine ⟨87305479814906648783506433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232814612839751063422683821 87305479814906648783506433)
          ·
            refine ⟨65479109861179986587629825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87305479814906648783506433 65479109861179986587629825)
            ·
              refine ⟨49109332395884989940722369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65479109861179986587629825 49109332395884989940722369)
              ·
                refine ⟨36831999296913742455541777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49109332395884989940722369 36831999296913742455541777)
                ·
                  refine ⟨27623999472685306841656333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36831999296913742455541777 27623999472685306841656333)
                  ·
                    refine ⟨10358999802256990065621125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27623999472685306841656333 10358999802256990065621125)
                    ·
                      refine ⟨1942312462923185637303961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10358999802256990065621125 1942312462923185637303961)
                      ·
                        rfl

theorem cell23_3782640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 4].length) (baseStart_3782640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782640 prefixEnd_3782640 := by exact prefixLift 3782640
  have htrace : WordTrace (prefixWord ++ tailWord_3782640) baseStart_3782640 baseEnd_3782640 := by
    simpa [prefixWord, tailWord_3782640, baseEnd_3782640] using wordTrace_append hprefix tailTrace_3782640
  have hstable : (prefixWord ++ tailWord_3782640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782640).length < 2 ^ (prefixWord ++ tailWord_3782640).sum := by decide
  have hdescent : baseEnd_3782640 < baseStart_3782640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782669 : List Nat := [1, 7, 1, 2, 2, 1, 1, 1, 3, 2, 2]
def baseStart_3782669 : Nat := 118140960795 + 3782669 * 2 ^ 59
def prefixEnd_3782669 : Nat := 4983230072969 + 3 ^ 40 * 3782669 * 2
def baseEnd_3782669 : Nat := 1942327353862166023841329

theorem tailTrace_3782669 : CollatzResearch.WordTrace tailWord_3782669 prefixEnd_3782669 1942327353862166023841329 := by
  unfold tailWord_3782669
  simp only [CollatzResearch.WordTrace]
  refine ⟨137965272733043716277359061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91976848488695810851572707 137965272733043716277359061)
  ·
    refine ⟨3233561079680712100250603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 137965272733043716277359061 3233561079680712100250603)
    ·
      refine ⟨4850341619521068150375905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3233561079680712100250603 4850341619521068150375905)
      ·
        refine ⟨3637756214640801112781929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4850341619521068150375905 3637756214640801112781929)
        ·
          refine ⟨2728317160980600834586447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3637756214640801112781929 2728317160980600834586447)
          ·
            refine ⟨4092475741470901251879671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2728317160980600834586447 4092475741470901251879671)
            ·
              refine ⟨6138713612206351877819507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4092475741470901251879671 6138713612206351877819507)
              ·
                refine ⟨9208070418309527816729261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6138713612206351877819507 9208070418309527816729261)
                ·
                  refine ⟨3453026406866072931273473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9208070418309527816729261 3453026406866072931273473)
                  ·
                    refine ⟨2589769805149554698455105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3453026406866072931273473 2589769805149554698455105)
                    ·
                      refine ⟨1942327353862166023841329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2589769805149554698455105 1942327353862166023841329)
                      ·
                        rfl

theorem cell23_3782669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_3782669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782669 prefixEnd_3782669 := by exact prefixLift 3782669
  have htrace : WordTrace (prefixWord ++ tailWord_3782669) baseStart_3782669 baseEnd_3782669 := by
    simpa [prefixWord, tailWord_3782669, baseEnd_3782669] using wordTrace_append hprefix tailTrace_3782669
  have hstable : (prefixWord ++ tailWord_3782669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782669).length < 2 ^ (prefixWord ++ tailWord_3782669).sum := by decide
  have hdescent : baseEnd_3782669 < baseStart_3782669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782691 : List Nat := [1, 1, 1, 4, 3, 1, 3, 3, 2, 2, 2]
def baseStart_3782691 : Nat := 118140960795 + 3782691 * 2 ^ 59
def prefixEnd_3782691 : Nat := 4983230072969 + 3 ^ 40 * 3782691 * 2
def baseEnd_3782691 : Nat := 1942338650436564937766227

theorem tailTrace_3782691 : CollatzResearch.WordTrace tailWord_3782691 prefixEnd_3782691 1942338650436564937766227 := by
  unfold tailWord_3782691
  simp only [CollatzResearch.WordTrace]
  refine ⟨137966075138964014034659927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91977383425976009356439951 137966075138964014034659927)
  ·
    refine ⟨206949112708446021051989891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137966075138964014034659927 206949112708446021051989891)
    ·
      refine ⟨310423669062669031577984837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206949112708446021051989891 310423669062669031577984837)
      ·
        refine ⟨58204437949250443420872157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 310423669062669031577984837 58204437949250443420872157)
        ·
          refine ⟨21826664230968916282827059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58204437949250443420872157 21826664230968916282827059)
          ·
            refine ⟨32739996346453374424240589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21826664230968916282827059 32739996346453374424240589)
            ·
              refine ⟨12277498629920015409090221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32739996346453374424240589 12277498629920015409090221)
              ·
                refine ⟨4604061986220005778408833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12277498629920015409090221 4604061986220005778408833)
                ·
                  refine ⟨3453046489665004333806625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4604061986220005778408833 3453046489665004333806625)
                  ·
                    refine ⟨2589784867248753250354969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3453046489665004333806625 2589784867248753250354969)
                    ·
                      refine ⟨1942338650436564937766227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2589784867248753250354969 1942338650436564937766227)
                      ·
                        rfl

theorem cell23_3782691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 2, 2, 2].length) (baseStart_3782691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782691 prefixEnd_3782691 := by exact prefixLift 3782691
  have htrace : WordTrace (prefixWord ++ tailWord_3782691) baseStart_3782691 baseEnd_3782691 := by
    simpa [prefixWord, tailWord_3782691, baseEnd_3782691] using wordTrace_append hprefix tailTrace_3782691
  have hstable : (prefixWord ++ tailWord_3782691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782691).length < 2 ^ (prefixWord ++ tailWord_3782691).sum := by decide
  have hdescent : baseEnd_3782691 < baseStart_3782691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782695 : List Nat := [1, 1, 7, 1, 2, 2, 1, 2, 1, 3, 2]
def baseStart_3782695 : Nat := 118140960795 + 3782695 * 2 ^ 59
def prefixEnd_3782695 : Nat := 4983230072969 + 3 ^ 40 * 3782695 * 2
def baseEnd_3782695 : Nat := 1942340704359182922116209

theorem tailTrace_3782695 : CollatzResearch.WordTrace tailWord_3782695 prefixEnd_3782695 1942340704359182922116209 := by
  unfold tailWord_3782695
  simp only [CollatzResearch.WordTrace]
  refine ⟨137966221030949522717805539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91977480687299681811870359 137966221030949522717805539)
  ·
    refine ⟨206949331546424284076708309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137966221030949522717805539 206949331546424284076708309)
    ·
      refine ⟨4850374958119319158047851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 206949331546424284076708309 4850374958119319158047851)
      ·
        refine ⟨7275562437178978737071777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4850374958119319158047851 7275562437178978737071777)
        ·
          refine ⟨5456671827884234052803833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7275562437178978737071777 5456671827884234052803833)
          ·
            refine ⟨4092503870913175539602875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5456671827884234052803833 4092503870913175539602875)
            ·
              refine ⟨6138755806369763309404313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4092503870913175539602875 6138755806369763309404313)
              ·
                refine ⟨4604066854777322482053235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6138755806369763309404313 4604066854777322482053235)
                ·
                  refine ⟨6906100282165983723079853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4604066854777322482053235 6906100282165983723079853)
                  ·
                    refine ⟨2589787605812243896154945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6906100282165983723079853 2589787605812243896154945)
                    ·
                      refine ⟨1942340704359182922116209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2589787605812243896154945 1942340704359182922116209)
                      ·
                        rfl

theorem cell23_3782695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_3782695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782695 prefixEnd_3782695 := by exact prefixLift 3782695
  have htrace : WordTrace (prefixWord ++ tailWord_3782695) baseStart_3782695 baseEnd_3782695 := by
    simpa [prefixWord, tailWord_3782695, baseEnd_3782695] using wordTrace_append hprefix tailTrace_3782695
  have hstable : (prefixWord ++ tailWord_3782695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782695).length < 2 ^ (prefixWord ++ tailWord_3782695).sum := by decide
  have hdescent : baseEnd_3782695 < baseStart_3782695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782708 : List Nat := [2, 5, 1, 2, 2, 1, 1, 2, 1, 4, 2]
def baseStart_3782708 : Nat := 118140960795 + 3782708 * 2 ^ 59
def prefixEnd_3782708 : Nat := 4983230072969 + 3 ^ 40 * 3782708 * 2
def baseEnd_3782708 : Nat := 1942347379607691371253649

theorem tailTrace_3782708 : CollatzResearch.WordTrace tailWord_3782708 prefixEnd_3782708 1942347379607691371253649 := by
  unfold tailWord_3782708
  simp only [CollatzResearch.WordTrace]
  refine ⟨68983347589951212969014389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91977796786601617292019185 68983347589951212969014389)
  ·
    refine ⟨6467188836557926215845099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68983347589951212969014389 6467188836557926215845099)
    ·
      refine ⟨9700783254836889323767649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6467188836557926215845099 9700783254836889323767649)
      ·
        refine ⟨7275587441127666992825737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9700783254836889323767649 7275587441127666992825737)
        ·
          refine ⟨5456690580845750244619303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7275587441127666992825737 5456690580845750244619303)
          ·
            refine ⟨8185035871268625366928955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5456690580845750244619303 8185035871268625366928955)
            ·
              refine ⟨12277553806902938050393433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8185035871268625366928955 12277553806902938050393433)
              ·
                refine ⟨9208165355177203537795075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12277553806902938050393433 9208165355177203537795075)
                ·
                  refine ⟨13812248032765805306692613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9208165355177203537795075 13812248032765805306692613)
                  ·
                    refine ⟨2589796506143588495004865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13812248032765805306692613 2589796506143588495004865)
                    ·
                      refine ⟨1942347379607691371253649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2589796506143588495004865 1942347379607691371253649)
                      ·
                        rfl

theorem cell23_3782708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_3782708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782708 prefixEnd_3782708 := by exact prefixLift 3782708
  have htrace : WordTrace (prefixWord ++ tailWord_3782708) baseStart_3782708 baseEnd_3782708 := by
    simpa [prefixWord, tailWord_3782708, baseEnd_3782708] using wordTrace_append hprefix tailTrace_3782708
  have hstable : (prefixWord ++ tailWord_3782708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782708).length < 2 ^ (prefixWord ++ tailWord_3782708).sum := by decide
  have hdescent : baseEnd_3782708 < baseStart_3782708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782727 : List Nat := [1, 1, 4, 1, 3, 1, 1, 4, 2, 5]
def baseStart_3782727 : Nat := 118140960795 + 3782727 * 2 ^ 59
def prefixEnd_3782727 : Nat := 4983230072969 + 3 ^ 40 * 3782727 * 2
def baseEnd_3782727 : Nat := 647452378580042265638687

theorem tailTrace_3782727 : CollatzResearch.WordTrace tailWord_3782727 prefixEnd_3782727 647452378580042265638687 := by
  unfold tailWord_3782727
  simp only [CollatzResearch.WordTrace]
  refine ⟨137967388166833592182970435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91978258777889061455313623 137967388166833592182970435)
  ·
    refine ⟨206951082250250388274455653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137967388166833592182970435 206951082250250388274455653)
    ·
      refine ⟨38803327921921947801460435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206951082250250388274455653 38803327921921947801460435)
      ·
        refine ⟨58204991882882921702190653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38803327921921947801460435 58204991882882921702190653)
        ·
          refine ⟨21826871956081095638321495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58204991882882921702190653 21826871956081095638321495)
          ·
            refine ⟨32740307934121643457482243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21826871956081095638321495 32740307934121643457482243)
            ·
              refine ⟨49110461901182465186223365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32740307934121643457482243 49110461901182465186223365)
              ·
                refine ⟨9208211606471712222416881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49110461901182465186223365 9208211606471712222416881)
                ·
                  refine ⟨6906158704853784166812661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9208211606471712222416881 6906158704853784166812661)
                  ·
                    refine ⟨647452378580042265638687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6906158704853784166812661 647452378580042265638687)
                    ·
                      rfl

theorem cell23_3782727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_3782727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782727 prefixEnd_3782727 := by exact prefixLift 3782727
  have htrace : WordTrace (prefixWord ++ tailWord_3782727) baseStart_3782727 baseEnd_3782727 := by
    simpa [prefixWord, tailWord_3782727, baseEnd_3782727] using wordTrace_append hprefix tailTrace_3782727
  have hstable : (prefixWord ++ tailWord_3782727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782727).length < 2 ^ (prefixWord ++ tailWord_3782727).sum := by decide
  have hdescent : baseEnd_3782727 < baseStart_3782727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782734 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2]
def baseStart_3782734 : Nat := 118140960795 + 3782734 * 2 ^ 59
def prefixEnd_3782734 : Nat := 4983230072969 + 3 ^ 40 * 3782734 * 2
def baseEnd_3782734 : Nat := 1942360730104708269528529

theorem tailTrace_3782734 : CollatzResearch.WordTrace tailWord_3782734 prefixEnd_3782734 1942360730104708269528529 := by
  unfold tailWord_3782734
  simp only [CollatzResearch.WordTrace]
  refine ⟨17245955434726029047309407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91978428985205488252316837 17245955434726029047309407)
  ·
    refine ⟨25868933152089043570964111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17245955434726029047309407 25868933152089043570964111)
    ·
      refine ⟨38803399728133565356446167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25868933152089043570964111 38803399728133565356446167)
      ·
        refine ⟨58205099592200348034669251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38803399728133565356446167 58205099592200348034669251)
        ·
          refine ⟨87307649388300522052003877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58205099592200348034669251 87307649388300522052003877)
          ·
            refine ⟨16370184260306347884750727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87307649388300522052003877 16370184260306347884750727)
            ·
              refine ⟨24555276390459521827126091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16370184260306347884750727 24555276390459521827126091)
              ·
                refine ⟨36832914585689282740689137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24555276390459521827126091 36832914585689282740689137)
                ·
                  refine ⟨27624685939266962055516853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36832914585689282740689137 27624685939266962055516853)
                  ·
                    refine ⟨2589814306806277692704705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27624685939266962055516853 2589814306806277692704705)
                    ·
                      refine ⟨1942360730104708269528529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2589814306806277692704705 1942360730104708269528529)
                      ·
                        rfl

theorem cell23_3782734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2].length) (baseStart_3782734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782734 prefixEnd_3782734 := by exact prefixLift 3782734
  have htrace : WordTrace (prefixWord ++ tailWord_3782734) baseStart_3782734 baseEnd_3782734 := by
    simpa [prefixWord, tailWord_3782734, baseEnd_3782734] using wordTrace_append hprefix tailTrace_3782734
  have hstable : (prefixWord ++ tailWord_3782734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782734).length < 2 ^ (prefixWord ++ tailWord_3782734).sum := by decide
  have hdescent : baseEnd_3782734 < baseStart_3782734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782764 : List Nat := [2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 4]
def baseStart_3782764 : Nat := 118140960795 + 3782764 * 2 ^ 59
def prefixEnd_3782764 : Nat := 4983230072969 + 3 ^ 40 * 3782764 * 2
def baseEnd_3782764 : Nat := 1942376134524343152153391

theorem tailTrace_3782764 : CollatzResearch.WordTrace tailWord_3782764 prefixEnd_3782764 1942376134524343152153391 := by
  unfold tailWord_3782764
  simp only [CollatzResearch.WordTrace]
  refine ⟨68984368833849773751033673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91979158445133031668044897 68984368833849773751033673)
  ·
    refine ⟨51738276625387330313275255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68984368833849773751033673 51738276625387330313275255)
    ·
      refine ⟨77607414938080995469912883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51738276625387330313275255 77607414938080995469912883)
      ·
        refine ⟨116411122407121493204869325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77607414938080995469912883 116411122407121493204869325)
        ·
          refine ⟨43654170902670559951825997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116411122407121493204869325 43654170902670559951825997)
          ·
            refine ⟨16370314088501459981934749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43654170902670559951825997 16370314088501459981934749)
            ·
              refine ⟨6138867783188047493225531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16370314088501459981934749 6138867783188047493225531)
              ·
                refine ⟨9208301674782071239838297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6138867783188047493225531 9208301674782071239838297)
                ·
                  refine ⟨6906226256086553429878723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9208301674782071239838297 6906226256086553429878723)
                  ·
                    refine ⟨10359339384129830144818085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6906226256086553429878723 10359339384129830144818085)
                    ·
                      refine ⟨1942376134524343152153391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10359339384129830144818085 1942376134524343152153391)
                      ·
                        rfl

theorem cell23_3782764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 4].length) (baseStart_3782764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782764 prefixEnd_3782764 := by exact prefixLift 3782764
  have htrace : WordTrace (prefixWord ++ tailWord_3782764) baseStart_3782764 baseEnd_3782764 := by
    simpa [prefixWord, tailWord_3782764, baseEnd_3782764] using wordTrace_append hprefix tailTrace_3782764
  have hstable : (prefixWord ++ tailWord_3782764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782764).length < 2 ^ (prefixWord ++ tailWord_3782764).sum := by decide
  have hdescent : baseEnd_3782764 < baseStart_3782764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782777 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 2, 1, 6]
def baseStart_3782777 : Nat := 118140960795 + 3782777 * 2 ^ 59
def prefixEnd_3782777 : Nat := 4983230072969 + 3 ^ 40 * 3782777 * 2
def baseEnd_3782777 : Nat := 1942382809772851601290831

theorem tailTrace_3782777 : CollatzResearch.WordTrace tailWord_3782777 prefixEnd_3782777 1942382809772851601290831 := by
  unfold tailWord_3782777
  simp only [CollatzResearch.WordTrace]
  refine ⟨137969211816652450722290585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91979474544434967148193723 137969211816652450722290585)
  ·
    refine ⟨103476908862489338041717939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137969211816652450722290585 103476908862489338041717939)
    ·
      refine ⟨155215363293734007062576909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103476908862489338041717939 155215363293734007062576909)
      ·
        refine ⟨58205761235150252648466341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155215363293734007062576909 58205761235150252648466341)
        ·
          refine ⟨10913580231590672371587439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58205761235150252648466341 10913580231590672371587439)
          ·
            refine ⟨16370370347386008557381159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10913580231590672371587439 16370370347386008557381159)
            ·
              refine ⟨24555555521079012836071739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16370370347386008557381159 24555555521079012836071739)
              ·
                refine ⟨36833333281618519254107609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24555555521079012836071739 36833333281618519254107609)
                ·
                  refine ⟨27624999961213889440580707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36833333281618519254107609 27624999961213889440580707)
                  ·
                    refine ⟨41437499941820834160871061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27624999961213889440580707 41437499941820834160871061)
                    ·
                      refine ⟨1942382809772851601290831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41437499941820834160871061 1942382809772851601290831)
                      ·
                        rfl

theorem cell23_3782777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_3782777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782777 prefixEnd_3782777 := by exact prefixLift 3782777
  have htrace : WordTrace (prefixWord ++ tailWord_3782777) baseStart_3782777 baseEnd_3782777 := by
    simpa [prefixWord, tailWord_3782777, baseEnd_3782777] using wordTrace_append hprefix tailTrace_3782777
  have hstable : (prefixWord ++ tailWord_3782777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782777).length < 2 ^ (prefixWord ++ tailWord_3782777).sum := by decide
  have hdescent : baseEnd_3782777 < baseStart_3782777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782787 : List Nat := [1, 1, 1, 3, 3, 4, 1, 1, 8]
def baseStart_3782787 : Nat := 118140960795 + 3782787 * 2 ^ 59
def prefixEnd_3782787 : Nat := 4983230072969 + 3 ^ 40 * 3782787 * 2
def baseEnd_3782787 : Nat := 215820882731044062462865

theorem tailTrace_3782787 : CollatzResearch.WordTrace tailWord_3782787 prefixEnd_3782787 215820882731044062462865 := by
  unfold tailWord_3782787
  simp only [CollatzResearch.WordTrace]
  refine ⟨137969576546616222430154615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91979717697744148286769743 137969576546616222430154615)
  ·
    refine ⟨206954364819924333645231923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137969576546616222430154615 206954364819924333645231923)
    ·
      refine ⟨310431547229886500467847885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206954364819924333645231923 310431547229886500467847885)
      ·
        refine ⟨116411830211207437675442957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310431547229886500467847885 116411830211207437675442957)
        ·
          refine ⟨43654436329202789128291109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116411830211207437675442957 43654436329202789128291109)
          ·
            refine ⟨8185206811725522961554583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43654436329202789128291109 8185206811725522961554583)
            ·
              refine ⟨12277810217588284442331875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8185206811725522961554583 12277810217588284442331875)
              ·
                refine ⟨18416715326382426663497813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12277810217588284442331875 18416715326382426663497813)
                ·
                  refine ⟨215820882731044062462865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18416715326382426663497813 215820882731044062462865)
                  ·
                    rfl

theorem cell23_3782787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 8].length) (baseStart_3782787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782787 prefixEnd_3782787 := by exact prefixLift 3782787
  have htrace : WordTrace (prefixWord ++ tailWord_3782787) baseStart_3782787 baseEnd_3782787 := by
    simpa [prefixWord, tailWord_3782787, baseEnd_3782787] using wordTrace_append hprefix tailTrace_3782787
  have hstable : (prefixWord ++ tailWord_3782787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782787).length < 2 ^ (prefixWord ++ tailWord_3782787).sum := by decide
  have hdescent : baseEnd_3782787 < baseStart_3782787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782791 : List Nat := [1, 1, 4, 2, 1, 1, 4, 4, 1, 4]
def baseStart_3782791 : Nat := 118140960795 + 3782791 * 2 ^ 59
def prefixEnd_3782791 : Nat := 4983230072969 + 3 ^ 40 * 3782791 * 2
def baseEnd_3782791 : Nat := 647463332834004848838589

theorem tailTrace_3782791 : CollatzResearch.WordTrace tailWord_3782791 prefixEnd_3782791 647463332834004848838589 := by
  unfold tailWord_3782791
  simp only [CollatzResearch.WordTrace]
  refine ⟨137969722438601731113300227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91979814959067820742200151 137969722438601731113300227)
  ·
    refine ⟨206954583657902596669950341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137969722438601731113300227 206954583657902596669950341)
    ·
      refine ⟨38803984435856736875615689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206954583657902596669950341 38803984435856736875615689)
      ·
        refine ⟨29102988326892552656711767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38803984435856736875615689 29102988326892552656711767)
        ·
          refine ⟨43654482490338828985067651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29102988326892552656711767 43654482490338828985067651)
          ·
            refine ⟨65481723735508243477601477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43654482490338828985067651 65481723735508243477601477)
            ·
              refine ⟨12277823200407795652050277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65481723735508243477601477 12277823200407795652050277)
              ·
                refine ⟨2302091850076461684759427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12277823200407795652050277 2302091850076461684759427)
                ·
                  refine ⟨3453137775114692527139141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2302091850076461684759427 3453137775114692527139141)
                  ·
                    refine ⟨647463332834004848838589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3453137775114692527139141 647463332834004848838589)
                    ·
                      rfl

theorem cell23_3782791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_3782791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782791 prefixEnd_3782791 := by exact prefixLift 3782791
  have htrace : WordTrace (prefixWord ++ tailWord_3782791) baseStart_3782791 baseEnd_3782791 := by
    simpa [prefixWord, tailWord_3782791, baseEnd_3782791] using wordTrace_append hprefix tailTrace_3782791
  have hstable : (prefixWord ++ tailWord_3782791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782791).length < 2 ^ (prefixWord ++ tailWord_3782791).sum := by decide
  have hdescent : baseEnd_3782791 < baseStart_3782791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782834 : List Nat := [3, 2, 1, 1, 1, 3, 1, 5, 1, 5]
def baseStart_3782834 : Nat := 118140960795 + 3782834 * 2 ^ 59
def prefixEnd_3782834 : Nat := 4983230072969 + 3 ^ 40 * 3782834 * 2
def baseEnd_3782834 : Nat := 647470692723385959426023

theorem tailTrace_3782834 : CollatzResearch.WordTrace tailWord_3782834 prefixEnd_3782834 647470692723385959426023 := by
  unfold tailWord_3782834
  simp only [CollatzResearch.WordTrace]
  refine ⟨34492822694361487364278889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91980860518297299638077037 34492822694361487364278889)
  ·
    refine ⟨25869617020771115523209167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34492822694361487364278889 25869617020771115523209167)
    ·
      refine ⟨38804425531156673284813751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25869617020771115523209167 38804425531156673284813751)
      ·
        refine ⟨58206638296735009927220627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38804425531156673284813751 58206638296735009927220627)
        ·
          refine ⟨87309957445102514890830941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58206638296735009927220627 87309957445102514890830941)
          ·
            refine ⟨32741234041913443084061603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87309957445102514890830941 32741234041913443084061603)
            ·
              refine ⟨49111851062870164626092405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32741234041913443084061603 49111851062870164626092405)
              ·
                refine ⟨4604236037144077933696163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49111851062870164626092405 4604236037144077933696163)
                ·
                  refine ⟨6906354055716116900544245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4604236037144077933696163 6906354055716116900544245)
                  ·
                    refine ⟨647470692723385959426023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6906354055716116900544245 647470692723385959426023)
                    ·
                      rfl

theorem cell23_3782834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_3782834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782834 prefixEnd_3782834 := by exact prefixLift 3782834
  have htrace : WordTrace (prefixWord ++ tailWord_3782834) baseStart_3782834 baseEnd_3782834 := by
    simpa [prefixWord, tailWord_3782834, baseEnd_3782834] using wordTrace_append hprefix tailTrace_3782834
  have hstable : (prefixWord ++ tailWord_3782834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782834).length < 2 ^ (prefixWord ++ tailWord_3782834).sum := by decide
  have hdescent : baseEnd_3782834 < baseStart_3782834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782841 : List Nat := [1, 2, 1, 4, 1, 2, 3, 2, 2, 3, 2]
def baseStart_3782841 : Nat := 118140960795 + 3782841 * 2 ^ 59
def prefixEnd_3782841 : Nat := 4983230072969 + 3 ^ 40 * 3782841 * 2
def baseEnd_3782841 : Nat := 1942415672534739350890537

theorem tailTrace_3782841 : CollatzResearch.WordTrace tailWord_3782841 prefixEnd_3782841 1942415672534739350890537 := by
  unfold tailWord_3782841
  simp only [CollatzResearch.WordTrace]
  refine ⟨137971546088420589652620377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91981030725613726435080251 137971546088420589652620377)
  ·
    refine ⟨103478659566315442239465283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137971546088420589652620377 103478659566315442239465283)
    ·
      refine ⟨155217989349473163359197925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103478659566315442239465283 155217989349473163359197925)
      ·
        refine ⟨29103373003026218129849611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155217989349473163359197925 29103373003026218129849611)
        ·
          refine ⟨43655059504539327194774417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29103373003026218129849611 43655059504539327194774417)
          ·
            refine ⟨32741294628404495396080813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43655059504539327194774417 32741294628404495396080813)
            ·
              refine ⟨12277985485651685773530305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32741294628404495396080813 12277985485651685773530305)
              ·
                refine ⟨9208489114238764330147729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12277985485651685773530305 9208489114238764330147729)
                ·
                  refine ⟨6906366835679073247610797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9208489114238764330147729 6906366835679073247610797)
                  ·
                    refine ⟨2589887563379652467854049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6906366835679073247610797 2589887563379652467854049)
                    ·
                      refine ⟨1942415672534739350890537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2589887563379652467854049 1942415672534739350890537)
                      ·
                        rfl

theorem cell23_3782841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_3782841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782841 prefixEnd_3782841 := by exact prefixLift 3782841
  have htrace : WordTrace (prefixWord ++ tailWord_3782841) baseStart_3782841 baseEnd_3782841 := by
    simpa [prefixWord, tailWord_3782841, baseEnd_3782841] using wordTrace_append hprefix tailTrace_3782841
  have hstable : (prefixWord ++ tailWord_3782841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782841).length < 2 ^ (prefixWord ++ tailWord_3782841).sum := by decide
  have hdescent : baseEnd_3782841 < baseStart_3782841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782848 : List Nat := [2, 1, 1, 2, 5, 3, 1, 1, 3, 1, 3]
def baseStart_3782848 : Nat := 118140960795 + 3782848 * 2 ^ 59
def prefixEnd_3782848 : Nat := 4983230072969 + 3 ^ 40 * 3782848 * 2
def baseEnd_3782848 : Nat := 1942419266899320823503005

theorem tailTrace_3782848 : CollatzResearch.WordTrace tailWord_3782848 prefixEnd_3782848 1942419266899320823503005 := by
  unfold tailWord_3782848
  simp only [CollatzResearch.WordTrace]
  refine ⟨68985900699697614924062599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91981200932930153232083465 68985900699697614924062599)
  ·
    refine ⟨103478851049546422386093899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68985900699697614924062599 103478851049546422386093899)
    ·
      refine ⟨155218276574319633579140849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103478851049546422386093899 155218276574319633579140849)
      ·
        refine ⟨116413707430739725184355637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155218276574319633579140849 116413707430739725184355637)
        ·
          refine ⟨10913785071631849236033341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116413707430739725184355637 10913785071631849236033341)
          ·
            refine ⟨4092669401861943463512503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10913785071631849236033341 4092669401861943463512503)
            ·
              refine ⟨6139004102792915195268755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4092669401861943463512503 6139004102792915195268755)
              ·
                refine ⟨9208506154189372792903133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6139004102792915195268755 9208506154189372792903133)
                ·
                  refine ⟨3453189807821014797338675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9208506154189372792903133 3453189807821014797338675)
                  ·
                    refine ⟨5179784711731522196008013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3453189807821014797338675 5179784711731522196008013)
                    ·
                      refine ⟨1942419266899320823503005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5179784711731522196008013 1942419266899320823503005)
                      ·
                        rfl

theorem cell23_3782848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 3, 1, 3].length) (baseStart_3782848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782848 prefixEnd_3782848 := by exact prefixLift 3782848
  have htrace : WordTrace (prefixWord ++ tailWord_3782848) baseStart_3782848 baseEnd_3782848 := by
    simpa [prefixWord, tailWord_3782848, baseEnd_3782848] using wordTrace_append hprefix tailTrace_3782848
  have hstable : (prefixWord ++ tailWord_3782848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782848).length < 2 ^ (prefixWord ++ tailWord_3782848).sum := by decide
  have hdescent : baseEnd_3782848 < baseStart_3782848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782857 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 3, 1, 5]
def baseStart_3782857 : Nat := 118140960795 + 3782857 * 2 ^ 59
def prefixEnd_3782857 : Nat := 4983230072969 + 3 ^ 40 * 3782857 * 2
def baseEnd_3782857 : Nat := 1942423888225211288290463

theorem tailTrace_3782857 : CollatzResearch.WordTrace tailWord_3782857 prefixEnd_3782857 1942423888225211288290463 := by
  unfold tailWord_3782857
  simp only [CollatzResearch.WordTrace]
  refine ⟨137972129656362624385202825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91981419770908416256801883 137972129656362624385202825)
  ·
    refine ⟨103479097242271968288902119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137972129656362624385202825 103479097242271968288902119)
    ·
      refine ⟨155218645863407952433353179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103479097242271968288902119 155218645863407952433353179)
      ·
        refine ⟨232827968795111928650029769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155218645863407952433353179 232827968795111928650029769)
        ·
          refine ⟨174620976596333946487522327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232827968795111928650029769 174620976596333946487522327)
          ·
            refine ⟨261931464894500919731283491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174620976596333946487522327 261931464894500919731283491)
            ·
              refine ⟨392897197341751379596925237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261931464894500919731283491 392897197341751379596925237)
              ·
                refine ⟨36834112250789191837211741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 392897197341751379596925237 36834112250789191837211741)
                ·
                  refine ⟨13812792094045946938954403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36834112250789191837211741 13812792094045946938954403)
                  ·
                    refine ⟨20719188141068920408431605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13812792094045946938954403 20719188141068920408431605)
                    ·
                      refine ⟨1942423888225211288290463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20719188141068920408431605 1942423888225211288290463)
                      ·
                        rfl

theorem cell23_3782857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 1, 5].length) (baseStart_3782857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782857 prefixEnd_3782857 := by exact prefixLift 3782857
  have htrace : WordTrace (prefixWord ++ tailWord_3782857) baseStart_3782857 baseEnd_3782857 := by
    simpa [prefixWord, tailWord_3782857, baseEnd_3782857] using wordTrace_append hprefix tailTrace_3782857
  have hstable : (prefixWord ++ tailWord_3782857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782857).length < 2 ^ (prefixWord ++ tailWord_3782857).sum := by decide
  have hdescent : baseEnd_3782857 < baseStart_3782857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782871 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 5, 2, 2]
def baseStart_3782871 : Nat := 118140960795 + 3782871 * 2 ^ 59
def prefixEnd_3782871 : Nat := 4983230072969 + 3 ^ 40 * 3782871 * 2
def baseEnd_3782871 : Nat := 1942431076954374233515399

theorem tailTrace_3782871 : CollatzResearch.WordTrace tailWord_3782871 prefixEnd_3782871 1942431076954374233515399 := by
  unfold tailWord_3782871
  simp only [CollatzResearch.WordTrace]
  refine ⟨137972640278311904776212467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91981760185541269850808311 137972640278311904776212467)
  ·
    refine ⟨206958960417467857164318701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137972640278311904776212467 206958960417467857164318701)
    ·
      refine ⟨77609610156550446436619513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206958960417467857164318701 77609610156550446436619513)
      ·
        refine ⟨58207207617412834827464635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77609610156550446436619513 58207207617412834827464635)
        ·
          refine ⟨87310811426119252241196953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58207207617412834827464635 87310811426119252241196953)
          ·
            refine ⟨65483108569589439180897715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87310811426119252241196953 65483108569589439180897715)
            ·
              refine ⟨98224662854384158771346573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65483108569589439180897715 98224662854384158771346573)
              ·
                refine ⟨36834248570394059539254965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98224662854384158771346573 36834248570394059539254965)
                ·
                  refine ⟨3453210803474443081805153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36834248570394059539254965 3453210803474443081805153)
                  ·
                    refine ⟨2589908102605832311353865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3453210803474443081805153 2589908102605832311353865)
                    ·
                      refine ⟨1942431076954374233515399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2589908102605832311353865 1942431076954374233515399)
                      ·
                        rfl

theorem cell23_3782871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 5, 2, 2].length) (baseStart_3782871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782871 prefixEnd_3782871 := by exact prefixLift 3782871
  have htrace : WordTrace (prefixWord ++ tailWord_3782871) baseStart_3782871 baseEnd_3782871 := by
    simpa [prefixWord, tailWord_3782871, baseEnd_3782871] using wordTrace_append hprefix tailTrace_3782871
  have hstable : (prefixWord ++ tailWord_3782871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782871).length < 2 ^ (prefixWord ++ tailWord_3782871).sum := by decide
  have hdescent : baseEnd_3782871 < baseStart_3782871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782888 : List Nat := [2, 1, 4, 1, 2, 3, 3, 1, 1, 1, 4]
def baseStart_3782888 : Nat := 118140960795 + 3782888 * 2 ^ 59
def prefixEnd_3782888 : Nat := 4983230072969 + 3 ^ 40 * 3782888 * 2
def baseEnd_3782888 : Nat := 1942439806125500667002821

theorem tailTrace_3782888 : CollatzResearch.WordTrace tailWord_3782888 prefixEnd_3782888 1942439806125500667002821 := by
  unfold tailWord_3782888
  simp only [CollatzResearch.WordTrace]
  refine ⟨68986630159625158339790659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91982173546166877786387545 68986630159625158339790659)
  ·
    refine ⟨103479945239437737509685989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68986630159625158339790659 103479945239437737509685989)
    ·
      refine ⟨19402489732394575783066123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103479945239437737509685989 19402489732394575783066123)
      ·
        refine ⟨29103734598591863674599185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19402489732394575783066123 29103734598591863674599185)
        ·
          refine ⟨21827800948943897755949389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29103734598591863674599185 21827800948943897755949389)
          ·
            refine ⟨8185425355853961658481021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21827800948943897755949389 8185425355853961658481021)
            ·
              refine ⟨3069534508445235621930383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8185425355853961658481021 3069534508445235621930383)
              ·
                refine ⟨4604301762667853432895575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3069534508445235621930383 4604301762667853432895575)
                ·
                  refine ⟨6906452644001780149343363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4604301762667853432895575 6906452644001780149343363)
                  ·
                    refine ⟨10359678966002670224015045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6906452644001780149343363 10359678966002670224015045)
                    ·
                      refine ⟨1942439806125500667002821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10359678966002670224015045 1942439806125500667002821)
                      ·
                        rfl

theorem cell23_3782888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_3782888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782888 prefixEnd_3782888 := by exact prefixLift 3782888
  have htrace : WordTrace (prefixWord ++ tailWord_3782888) baseStart_3782888 baseEnd_3782888 := by
    simpa [prefixWord, tailWord_3782888, baseEnd_3782888] using wordTrace_append hprefix tailTrace_3782888
  have hstable : (prefixWord ++ tailWord_3782888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782888).length < 2 ^ (prefixWord ++ tailWord_3782888).sum := by decide
  have hdescent : baseEnd_3782888 < baseStart_3782888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782898 : List Nat := [3, 2, 1, 3, 2, 2, 2, 2, 2, 4]
def baseStart_3782898 : Nat := 118140960795 + 3782898 * 2 ^ 59
def prefixEnd_3782898 : Nat := 4983230072969 + 3 ^ 40 * 3782898 * 2
def baseEnd_3782898 : Nat := 647481646977348542625925

theorem tailTrace_3782898 : CollatzResearch.WordTrace tailWord_3782898 prefixEnd_3782898 647481646977348542625925 := by
  unfold tailWord_3782898
  simp only [CollatzResearch.WordTrace]
  refine ⟨34493406262303522096861337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91982416699476058924963565 34493406262303522096861337)
  ·
    refine ⟨25870054696727641572646003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34493406262303522096861337 25870054696727641572646003)
    ·
      refine ⟨38805082045091462358969005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25870054696727641572646003 38805082045091462358969005)
      ·
        refine ⟨14551905766909298384613377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38805082045091462358969005 14551905766909298384613377)
        ·
          refine ⟨10913929325181973788460033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14551905766909298384613377 10913929325181973788460033)
          ·
            refine ⟨8185446993886480341345025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10913929325181973788460033 8185446993886480341345025)
            ·
              refine ⟨6139085245414860256008769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8185446993886480341345025 6139085245414860256008769)
              ·
                refine ⟨4604313934061145192006577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6139085245414860256008769 4604313934061145192006577)
                ·
                  refine ⟨3453235450545858894004933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4604313934061145192006577 3453235450545858894004933)
                  ·
                    refine ⟨647481646977348542625925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3453235450545858894004933 647481646977348542625925)
                    ·
                      rfl

theorem cell23_3782898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_3782898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782898 prefixEnd_3782898 := by exact prefixLift 3782898
  have htrace : WordTrace (prefixWord ++ tailWord_3782898) baseStart_3782898 baseEnd_3782898 := by
    simpa [prefixWord, tailWord_3782898, baseEnd_3782898] using wordTrace_append hprefix tailTrace_3782898
  have hstable : (prefixWord ++ tailWord_3782898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782898).length < 2 ^ (prefixWord ++ tailWord_3782898).sum := by decide
  have hdescent : baseEnd_3782898 < baseStart_3782898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782921 : List Nat := [1, 2, 1, 1, 3, 5, 2, 1, 1, 3, 3]
def baseStart_3782921 : Nat := 118140960795 + 3782921 * 2 ^ 59
def prefixEnd_3782921 : Nat := 4983230072969 + 3 ^ 40 * 3782921 * 2
def baseEnd_3782921 : Nat := 1942456750987099037890169

theorem tailTrace_3782921 : CollatzResearch.WordTrace tailWord_3782921 prefixEnd_3782921 1942456750987099037890169 := by
  unfold tailWord_3782921
  simp only [CollatzResearch.WordTrace]
  refine ⟨137974463928130763315532617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91982975952087175543688411 137974463928130763315532617)
  ·
    refine ⟨103480847946098072486649463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137974463928130763315532617 103480847946098072486649463)
    ·
      refine ⟨155221271919147108729974195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103480847946098072486649463 155221271919147108729974195)
      ·
        refine ⟨232831907878720663094961293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155221271919147108729974195 232831907878720663094961293)
        ·
          refine ⟨87311965454520248660610485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232831907878720663094961293 87311965454520248660610485)
          ·
            refine ⟨8185496761361273311932233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87311965454520248660610485 8185496761361273311932233)
            ·
              refine ⟨6139122571020954983949175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8185496761361273311932233 6139122571020954983949175)
              ·
                refine ⟨9208683856531432475923763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6139122571020954983949175 9208683856531432475923763)
                ·
                  refine ⟨13813025784797148713885645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9208683856531432475923763 13813025784797148713885645)
                  ·
                    refine ⟨5179884669298930767707117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13813025784797148713885645 5179884669298930767707117)
                    ·
                      refine ⟨1942456750987099037890169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5179884669298930767707117 1942456750987099037890169)
                      ·
                        rfl

theorem cell23_3782921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 3, 3].length) (baseStart_3782921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782921 prefixEnd_3782921 := by exact prefixLift 3782921
  have htrace : WordTrace (prefixWord ++ tailWord_3782921) baseStart_3782921 baseEnd_3782921 := by
    simpa [prefixWord, tailWord_3782921, baseEnd_3782921] using wordTrace_append hprefix tailTrace_3782921
  have hstable : (prefixWord ++ tailWord_3782921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782921).length < 2 ^ (prefixWord ++ tailWord_3782921).sum := by decide
  have hdescent : baseEnd_3782921 < baseStart_3782921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782942 : List Nat := [4, 3, 2, 1, 1, 1, 4, 1, 1, 2, 3]
def baseStart_3782942 : Nat := 118140960795 + 3782942 * 2 ^ 59
def prefixEnd_3782942 : Nat := 4983230072969 + 3 ^ 40 * 3782942 * 2
def baseEnd_3782942 : Nat := 1942467534080843455727573

theorem tailTrace_3782942 : CollatzResearch.WordTrace tailWord_3782942 prefixEnd_3782942 1942467534080843455727573 := by
  unfold tailWord_3782942
  simp only [CollatzResearch.WordTrace]
  refine ⟨17246903732631835487755885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91983486574036455934698053 17246903732631835487755885)
  ·
    refine ⟨6467588899736938307908457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17246903732631835487755885 6467588899736938307908457)
    ·
      refine ⟨4850691674802703730931343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6467588899736938307908457 4850691674802703730931343)
      ·
        refine ⟨7276037512204055596397015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4850691674802703730931343 7276037512204055596397015)
        ·
          refine ⟨10914056268306083394595523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7276037512204055596397015 10914056268306083394595523)
          ·
            refine ⟨16371084402459125091893285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10914056268306083394595523 16371084402459125091893285)
            ·
              refine ⟨3069578325461085954729991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16371084402459125091893285 3069578325461085954729991)
              ·
                refine ⟨4604367488191628932094987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3069578325461085954729991 4604367488191628932094987)
                ·
                  refine ⟨6906551232287443398142481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4604367488191628932094987 6906551232287443398142481)
                  ·
                    refine ⟨5179913424215582548606861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6906551232287443398142481 5179913424215582548606861)
                    ·
                      refine ⟨1942467534080843455727573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5179913424215582548606861 1942467534080843455727573)
                      ·
                        rfl

theorem cell23_3782942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_3782942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782942 prefixEnd_3782942 := by exact prefixLift 3782942
  have htrace : WordTrace (prefixWord ++ tailWord_3782942) baseStart_3782942 baseEnd_3782942 := by
    simpa [prefixWord, tailWord_3782942, baseEnd_3782942] using wordTrace_append hprefix tailTrace_3782942
  have hstable : (prefixWord ++ tailWord_3782942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782942).length < 2 ^ (prefixWord ++ tailWord_3782942).sum := by decide
  have hdescent : baseEnd_3782942 < baseStart_3782942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782984 : List Nat := [2, 1, 3, 1, 1, 2, 4, 2, 7]
def baseStart_3782984 : Nat := 118140960795 + 3782984 * 2 ^ 59
def prefixEnd_3782984 : Nat := 4983230072969 + 3 ^ 40 * 3782984 * 2
def baseEnd_3782984 : Nat := 215832122252036921266931

theorem tailTrace_3782984 : CollatzResearch.WordTrace tailWord_3782984 prefixEnd_3782984 215832122252036921266931 := by
  unfold tailWord_3782984
  simp only [CollatzResearch.WordTrace]
  refine ⟨68988380863451262537538003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91984507817935016716717337 68988380863451262537538003)
  ·
    refine ⟨103482571295176893806307005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68988380863451262537538003 103482571295176893806307005)
    ·
      refine ⟨38805964235691335177365127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103482571295176893806307005 38805964235691335177365127)
      ·
        refine ⟨58208946353537002766047691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38805964235691335177365127 58208946353537002766047691)
        ·
          refine ⟨87313419530305504149071537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58208946353537002766047691 87313419530305504149071537)
          ·
            refine ⟨65485064647729128111803653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87313419530305504149071537 65485064647729128111803653)
            ·
              refine ⟨12278449621449211520963185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65485064647729128111803653 12278449621449211520963185)
              ·
                refine ⟨9208837216086908640722389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12278449621449211520963185 9208837216086908640722389)
                ·
                  refine ⟨215832122252036921266931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9208837216086908640722389 215832122252036921266931)
                  ·
                    rfl

theorem cell23_3782984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 7].length) (baseStart_3782984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3782984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3782984 prefixEnd_3782984 := by exact prefixLift 3782984
  have htrace : WordTrace (prefixWord ++ tailWord_3782984) baseStart_3782984 baseEnd_3782984 := by
    simpa [prefixWord, tailWord_3782984, baseEnd_3782984] using wordTrace_append hprefix tailTrace_3782984
  have hstable : (prefixWord ++ tailWord_3782984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782984).length < 2 ^ (prefixWord ++ tailWord_3782984).sum := by decide
  have hdescent : baseEnd_3782984 < baseStart_3782984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783018 : List Nat := [3, 1, 3, 3, 1, 3, 1, 1, 7]
def baseStart_3783018 : Nat := 118140960795 + 3783018 * 2 ^ 59
def prefixEnd_3783018 : Nat := 4983230072969 + 3 ^ 40 * 3783018 * 2
def baseEnd_3783018 : Nat := 215834062067842795375247

theorem tailTrace_3783018 : CollatzResearch.WordTrace tailWord_3783018 prefixEnd_3783018 215834062067842795375247 := by
  unfold tailWord_3783018
  simp only [CollatzResearch.WordTrace]
  refine ⟨34494500452194837220453427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91985334539186232587875805 34494500452194837220453427)
  ·
    refine ⟨51741750678292255830680141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34494500452194837220453427 51741750678292255830680141)
    ·
      refine ⟨19403156504359595936505053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51741750678292255830680141 19403156504359595936505053)
      ·
        refine ⟨7276183689134848476189395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19403156504359595936505053 7276183689134848476189395)
        ·
          refine ⟨10914275533702272714284093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7276183689134848476189395 10914275533702272714284093)
          ·
            refine ⟨4092853325138352267856535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10914275533702272714284093 4092853325138352267856535)
            ·
              refine ⟨6139279987707528401784803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4092853325138352267856535 6139279987707528401784803)
              ·
                refine ⟨9208919981561292602677205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6139279987707528401784803 9208919981561292602677205)
                ·
                  refine ⟨215834062067842795375247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9208919981561292602677205 215834062067842795375247)
                  ·
                    rfl

theorem cell23_3783018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 7].length) (baseStart_3783018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783018 prefixEnd_3783018 := by exact prefixLift 3783018
  have htrace : WordTrace (prefixWord ++ tailWord_3783018) baseStart_3783018 baseEnd_3783018 := by
    simpa [prefixWord, tailWord_3783018, baseEnd_3783018] using wordTrace_append hprefix tailTrace_3783018
  have hstable : (prefixWord ++ tailWord_3783018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783018).length < 2 ^ (prefixWord ++ tailWord_3783018).sum := by decide
  have hdescent : baseEnd_3783018 < baseStart_3783018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783024 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 7]
def baseStart_3783024 : Nat := 118140960795 + 3783024 * 2 ^ 59
def prefixEnd_3783024 : Nat := 4983230072969 + 3 ^ 40 * 3783024 * 2
def baseEnd_3783024 : Nat := 1942509639494512134902195

theorem tailTrace_3783024 : CollatzResearch.WordTrace tailWord_3783024 prefixEnd_3783024 1942509639494512134902195 := by
  unfold tailWord_3783024
  simp only [CollatzResearch.WordTrace]
  refine ⟨68989110323378805953266063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91985480431171741271021417 68989110323378805953266063)
  ·
    refine ⟨103483665485068208929899095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68989110323378805953266063 103483665485068208929899095)
    ·
      refine ⟨155225498227602313394848643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103483665485068208929899095 155225498227602313394848643)
      ·
        refine ⟨232838247341403470092272965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155225498227602313394848643 232838247341403470092272965)
        ·
          refine ⟨43657171376513150642301181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232838247341403470092272965 43657171376513150642301181)
          ·
            refine ⟨16371439266192431490862943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43657171376513150642301181 16371439266192431490862943)
            ·
              refine ⟨24557158899288647236294415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16371439266192431490862943 24557158899288647236294415)
              ·
                refine ⟨36835738348932970854441623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24557158899288647236294415 36835738348932970854441623)
                ·
                  refine ⟨55253607523399456281662435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36835738348932970854441623 55253607523399456281662435)
                  ·
                    refine ⟨82880411285099184422493653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55253607523399456281662435 82880411285099184422493653)
                    ·
                      refine ⟨1942509639494512134902195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 82880411285099184422493653 1942509639494512134902195)
                      ·
                        rfl

theorem cell23_3783024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 7].length) (baseStart_3783024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783024 prefixEnd_3783024 := by exact prefixLift 3783024
  have htrace : WordTrace (prefixWord ++ tailWord_3783024) baseStart_3783024 baseEnd_3783024 := by
    simpa [prefixWord, tailWord_3783024, baseEnd_3783024] using wordTrace_append hprefix tailTrace_3783024
  have hstable : (prefixWord ++ tailWord_3783024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783024).length < 2 ^ (prefixWord ++ tailWord_3783024).sum := by decide
  have hdescent : baseEnd_3783024 < baseStart_3783024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783029 : List Nat := [1, 3, 4, 1, 2, 3, 2, 1, 2, 2, 2]
def baseStart_3783029 : Nat := 118140960795 + 3783029 * 2 ^ 59
def prefixEnd_3783029 : Nat := 4983230072969 + 3 ^ 40 * 3783029 * 2
def baseEnd_3783029 : Nat := 1942512206897784615339673

theorem tailTrace_3783029 : CollatzResearch.WordTrace tailWord_3783029 prefixEnd_3783029 1942512206897784615339673 := by
  unfold tailWord_3783029
  simp only [CollatzResearch.WordTrace]
  refine ⟨137978403011739497760464141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91985602007826331840309427 137978403011739497760464141)
  ·
    refine ⟨51741901129402311660174053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137978403011739497760464141 51741901129402311660174053)
    ·
      refine ⟨9701606461762933436282635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51741901129402311660174053 9701606461762933436282635)
      ·
        refine ⟨14552409692644400154423953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9701606461762933436282635 14552409692644400154423953)
        ·
          refine ⟨10914307269483300115817965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14552409692644400154423953 10914307269483300115817965)
          ·
            refine ⟨4092865226056237543431737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10914307269483300115817965 4092865226056237543431737)
            ·
              refine ⟨3069648919542178157573803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4092865226056237543431737 3069648919542178157573803)
              ·
                refine ⟨4604473379313267236360705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3069648919542178157573803 4604473379313267236360705)
                ·
                  refine ⟨3453355034484950427270529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4604473379313267236360705 3453355034484950427270529)
                  ·
                    refine ⟨2590016275863712820452897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3453355034484950427270529 2590016275863712820452897)
                    ·
                      refine ⟨1942512206897784615339673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2590016275863712820452897 1942512206897784615339673)
                      ·
                        rfl

theorem cell23_3783029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_3783029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783029 prefixEnd_3783029 := by exact prefixLift 3783029
  have htrace : WordTrace (prefixWord ++ tailWord_3783029) baseStart_3783029 baseEnd_3783029 := by
    simpa [prefixWord, tailWord_3783029, baseEnd_3783029] using wordTrace_append hprefix tailTrace_3783029
  have hstable : (prefixWord ++ tailWord_3783029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783029).length < 2 ^ (prefixWord ++ tailWord_3783029).sum := by decide
  have hdescent : baseEnd_3783029 < baseStart_3783029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783051 : List Nat := [1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 4]
def baseStart_3783051 : Nat := 118140960795 + 3783051 * 2 ^ 59
def prefixEnd_3783051 : Nat := 4983230072969 + 3 ^ 40 * 3783051 * 2
def baseEnd_3783051 : Nat := 1942523503472183529264571

theorem tailTrace_3783051 : CollatzResearch.WordTrace tailWord_3783051 prefixEnd_3783051 1942523503472183529264571 := by
  unfold tailWord_3783051
  simp only [CollatzResearch.WordTrace]
  refine ⟨137979205417659795517765007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91986136945106530345176671 137979205417659795517765007)
  ·
    refine ⟨206968808126489693276647511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137979205417659795517765007 206968808126489693276647511)
    ·
      refine ⟨310453212189734539914971267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206968808126489693276647511 310453212189734539914971267)
      ·
        refine ⟨465679818284601809872456901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310453212189734539914971267 465679818284601809872456901)
        ·
          refine ⟨87314965928362839351085669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 465679818284601809872456901 87314965928362839351085669)
          ·
            refine ⟨16371556111568032378328563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87314965928362839351085669 16371556111568032378328563)
            ·
              refine ⟨24557334167352048567492845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16371556111568032378328563 24557334167352048567492845)
              ·
                refine ⟨9209000312757018212809817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24557334167352048567492845 9209000312757018212809817)
                ·
                  refine ⟨6906750234567763659607363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9209000312757018212809817 6906750234567763659607363)
                  ·
                    refine ⟨10360125351851645489411045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6906750234567763659607363 10360125351851645489411045)
                    ·
                      refine ⟨1942523503472183529264571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10360125351851645489411045 1942523503472183529264571)
                      ·
                        rfl

theorem cell23_3783051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 4].length) (baseStart_3783051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783051 prefixEnd_3783051 := by exact prefixLift 3783051
  have htrace : WordTrace (prefixWord ++ tailWord_3783051) baseStart_3783051 baseEnd_3783051 := by
    simpa [prefixWord, tailWord_3783051, baseEnd_3783051] using wordTrace_append hprefix tailTrace_3783051
  have hstable : (prefixWord ++ tailWord_3783051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783051).length < 2 ^ (prefixWord ++ tailWord_3783051).sum := by decide
  have hdescent : baseEnd_3783051 < baseStart_3783051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783118 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3]
def baseStart_3783118 : Nat := 118140960795 + 3783118 * 2 ^ 59
def prefixEnd_3783118 : Nat := 4983230072969 + 3 ^ 40 * 3783118 * 2
def baseEnd_3783118 : Nat := 1942557906676034767126763

theorem tailTrace_3783118 : CollatzResearch.WordTrace tailWord_3783118 prefixEnd_3783118 1942557906676034767126763 := by
  unfold tailWord_3783118
  simp only [CollatzResearch.WordTrace]
  refine ⟨17247706138552133245056751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91987766072278043973636005 17247706138552133245056751)
  ·
    refine ⟨25871559207828199867585127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17247706138552133245056751 25871559207828199867585127)
    ·
      refine ⟨38807338811742299801377691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25871559207828199867585127 38807338811742299801377691)
      ·
        refine ⟨58211008217613449702066537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38807338811742299801377691 58211008217613449702066537)
        ·
          refine ⟨43658256163210087276549903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58211008217613449702066537 43658256163210087276549903)
          ·
            refine ⟨65487384244815130914824855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43658256163210087276549903 65487384244815130914824855)
            ·
              refine ⟨98231076367222696372237283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65487384244815130914824855 98231076367222696372237283)
              ·
                refine ⟨147346614550834044558355925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98231076367222696372237283 147346614550834044558355925)
                ·
                  refine ⟨3453436278535172919336467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 147346614550834044558355925 3453436278535172919336467)
                  ·
                    refine ⟨5180154417802759379004701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3453436278535172919336467 5180154417802759379004701)
                    ·
                      refine ⟨1942557906676034767126763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5180154417802759379004701 1942557906676034767126763)
                      ·
                        rfl

theorem cell23_3783118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_3783118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783118 prefixEnd_3783118 := by exact prefixLift 3783118
  have htrace : WordTrace (prefixWord ++ tailWord_3783118) baseStart_3783118 baseEnd_3783118 := by
    simpa [prefixWord, tailWord_3783118, baseEnd_3783118] using wordTrace_append hprefix tailTrace_3783118
  have hstable : (prefixWord ++ tailWord_3783118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783118).length < 2 ^ (prefixWord ++ tailWord_3783118).sum := by decide
  have hdescent : baseEnd_3783118 < baseStart_3783118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783128 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 4, 3, 2]
def baseStart_3783128 : Nat := 118140960795 + 3783128 * 2 ^ 59
def prefixEnd_3783128 : Nat := 4983230072969 + 3 ^ 40 * 3783128 * 2
def baseEnd_3783128 : Nat := 1942563041482579728001717

theorem tailTrace_3783128 : CollatzResearch.WordTrace tailWord_3783128 prefixEnd_3783128 1942563041482579728001717 := by
  unfold tailWord_3783128
  simp only [CollatzResearch.WordTrace]
  refine ⟨68991006919190418834159019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91988009225587225112212025 68991006919190418834159019)
  ·
    refine ⟨103486510378785628251238529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68991006919190418834159019 103486510378785628251238529)
    ·
      refine ⟨77614882784089221188428897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103486510378785628251238529 77614882784089221188428897)
      ·
        refine ⟨58211162088066915891321673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77614882784089221188428897 58211162088066915891321673)
        ·
          refine ⟨43658371566050186918491255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58211162088066915891321673 43658371566050186918491255)
          ·
            refine ⟨65487557349075280377736883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43658371566050186918491255 65487557349075280377736883)
            ·
              refine ⟨98231336023612920566605325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65487557349075280377736883 98231336023612920566605325)
              ·
                refine ⟨36836751008854845212476997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98231336023612920566605325 36836751008854845212476997)
                ·
                  refine ⟨6906890814160283477339437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36836751008854845212476997 6906890814160283477339437)
                  ·
                    refine ⟨2590084055310106304002289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6906890814160283477339437 2590084055310106304002289)
                    ·
                      refine ⟨1942563041482579728001717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2590084055310106304002289 1942563041482579728001717)
                      ·
                        rfl

theorem cell23_3783128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 4, 3, 2].length) (baseStart_3783128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783128 prefixEnd_3783128 := by exact prefixLift 3783128
  have htrace : WordTrace (prefixWord ++ tailWord_3783128) baseStart_3783128 baseEnd_3783128 := by
    simpa [prefixWord, tailWord_3783128, baseEnd_3783128] using wordTrace_append hprefix tailTrace_3783128
  have hstable : (prefixWord ++ tailWord_3783128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783128).length < 2 ^ (prefixWord ++ tailWord_3783128).sum := by decide
  have hdescent : baseEnd_3783128 < baseStart_3783128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783135 : List Nat := [1, 1, 2, 3, 3, 3, 2, 1, 3, 1, 3]
def baseStart_3783135 : Nat := 118140960795 + 3783135 * 2 ^ 59
def prefixEnd_3783135 : Nat := 4983230072969 + 3 ^ 40 * 3783135 * 2
def baseEnd_3783135 : Nat := 1942566635847161200614185

theorem tailTrace_3783135 : CollatzResearch.WordTrace tailWord_3783135 prefixEnd_3783135 1942566635847161200614185 := by
  unfold tailWord_3783135
  simp only [CollatzResearch.WordTrace]
  refine ⟨137982269149355477863822859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91988179432903651909215239 137982269149355477863822859)
  ·
    refine ⟨206973403724033216795734289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137982269149355477863822859 206973403724033216795734289)
    ·
      refine ⟨155230052793024912596800717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206973403724033216795734289 155230052793024912596800717)
      ·
        refine ⟨58211269797384342223800269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155230052793024912596800717 58211269797384342223800269)
        ·
          refine ⟨21829226174019128333925101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58211269797384342223800269 21829226174019128333925101)
          ·
            refine ⟨8185959815257173125221913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21829226174019128333925101 8185959815257173125221913)
            ·
              refine ⟨6139469861442879843916435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8185959815257173125221913 6139469861442879843916435)
              ·
                refine ⟨9209204792164319765874653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6139469861442879843916435 9209204792164319765874653)
                ·
                  refine ⟨3453451797061619912202995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9209204792164319765874653 3453451797061619912202995)
                  ·
                    refine ⟨5180177695592429868304493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3453451797061619912202995 5180177695592429868304493)
                    ·
                      refine ⟨1942566635847161200614185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5180177695592429868304493 1942566635847161200614185)
                      ·
                        rfl

theorem cell23_3783135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_3783135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783135 prefixEnd_3783135 := by exact prefixLift 3783135
  have htrace : WordTrace (prefixWord ++ tailWord_3783135) baseStart_3783135 baseEnd_3783135 := by
    simpa [prefixWord, tailWord_3783135, baseEnd_3783135] using wordTrace_append hprefix tailTrace_3783135
  have hstable : (prefixWord ++ tailWord_3783135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783135).length < 2 ^ (prefixWord ++ tailWord_3783135).sum := by decide
  have hdescent : baseEnd_3783135 < baseStart_3783135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783169 : List Nat := [1, 2, 4, 1, 3, 3, 1, 3, 1, 1, 3]
def baseStart_3783169 : Nat := 118140960795 + 3783169 * 2 ^ 59
def prefixEnd_3783169 : Nat := 4983230072969 + 3 ^ 40 * 3783169 * 2
def baseEnd_3783169 : Nat := 1942584094189414067589029

theorem tailTrace_3783169 : CollatzResearch.WordTrace tailWord_3783169 prefixEnd_3783169 1942584094189414067589029 := by
  unfold tailWord_3783169
  simp only [CollatzResearch.WordTrace]
  refine ⟨137983509231232301670560561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91989006154154867780373707 137983509231232301670560561)
  ·
    refine ⟨103487631923424226252920421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137983509231232301670560561 103487631923424226252920421)
    ·
      refine ⟨19403930985642042422422579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103487631923424226252920421 19403930985642042422422579)
      ·
        refine ⟨29105896478463063633633869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19403930985642042422422579 29105896478463063633633869)
        ·
          refine ⟨10914711179423648862612701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29105896478463063633633869 10914711179423648862612701)
          ·
            refine ⟨4093016692283868323479763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10914711179423648862612701 4093016692283868323479763)
            ·
              refine ⟨6139525038425802485219645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4093016692283868323479763 6139525038425802485219645)
              ·
                refine ⟨2302321889409675931957367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6139525038425802485219645 2302321889409675931957367)
                ·
                  refine ⟨3453482834114513897936051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2302321889409675931957367 3453482834114513897936051)
                  ·
                    refine ⟨5180224251171770846904077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3453482834114513897936051 5180224251171770846904077)
                    ·
                      refine ⟨1942584094189414067589029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5180224251171770846904077 1942584094189414067589029)
                      ·
                        rfl

theorem cell23_3783169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_3783169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783169 prefixEnd_3783169 := by exact prefixLift 3783169
  have htrace : WordTrace (prefixWord ++ tailWord_3783169) baseStart_3783169 baseEnd_3783169 := by
    simpa [prefixWord, tailWord_3783169, baseEnd_3783169] using wordTrace_append hprefix tailTrace_3783169
  have hstable : (prefixWord ++ tailWord_3783169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783169).length < 2 ^ (prefixWord ++ tailWord_3783169).sum := by decide
  have hdescent : baseEnd_3783169 < baseStart_3783169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783171 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 4]
def baseStart_3783171 : Nat := 118140960795 + 3783171 * 2 ^ 59
def prefixEnd_3783171 : Nat := 4983230072969 + 3 ^ 40 * 3783171 * 2
def baseEnd_3783171 : Nat := 1942585121150723059764019

theorem tailTrace_3783171 : CollatzResearch.WordTrace tailWord_3783171 prefixEnd_3783171 1942585121150723059764019 := by
  unfold tailWord_3783171
  simp only [CollatzResearch.WordTrace]
  refine ⟨137983582177225056012133367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91989054784816704008088911 137983582177225056012133367)
  ·
    refine ⟨206975373265837584018200051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137983582177225056012133367 206975373265837584018200051)
    ·
      refine ⟨310463059898756376027300077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206975373265837584018200051 310463059898756376027300077)
      ·
        refine ⟨116423647462033641010237529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310463059898756376027300077 116423647462033641010237529)
        ·
          refine ⟨87317735596525230757678147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116423647462033641010237529 87317735596525230757678147)
          ·
            refine ⟨130976603394787846136517221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87317735596525230757678147 130976603394787846136517221)
            ·
              refine ⟨24558113136522721150596979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130976603394787846136517221 24558113136522721150596979)
              ·
                refine ⟨36837169704784081725895469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24558113136522721150596979 36837169704784081725895469)
                ·
                  refine ⟨13813938639294030647210801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36837169704784081725895469 13813938639294030647210801)
                  ·
                    refine ⟨10360453979470522985408101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13813938639294030647210801 10360453979470522985408101)
                    ·
                      refine ⟨1942585121150723059764019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10360453979470522985408101 1942585121150723059764019)
                      ·
                        rfl

theorem cell23_3783171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_3783171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783171 prefixEnd_3783171 := by exact prefixLift 3783171
  have htrace : WordTrace (prefixWord ++ tailWord_3783171) baseStart_3783171 baseEnd_3783171 := by
    simpa [prefixWord, tailWord_3783171, baseEnd_3783171] using wordTrace_append hprefix tailTrace_3783171
  have hstable : (prefixWord ++ tailWord_3783171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783171).length < 2 ^ (prefixWord ++ tailWord_3783171).sum := by decide
  have hdescent : baseEnd_3783171 < baseStart_3783171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783178 : List Nat := [3, 1, 2, 2, 2, 1, 4, 1, 1, 1, 5]
def baseStart_3783178 : Nat := 118140960795 + 3783178 * 2 ^ 59
def prefixEnd_3783178 : Nat := 4983230072969 + 3 ^ 40 * 3783178 * 2
def baseEnd_3783178 : Nat := 1942588715515304532376487

theorem tailTrace_3783178 : CollatzResearch.WordTrace tailWord_3783178 prefixEnd_3783178 1942588715515304532376487 := by
  unfold tailWord_3783178
  simp only [CollatzResearch.WordTrace]
  refine ⟨34495959372049924051909547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91989224992133130805092125 34495959372049924051909547)
  ·
    refine ⟨51743939058074886077864321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34495959372049924051909547 51743939058074886077864321)
    ·
      refine ⟨38807954293556164558398241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51743939058074886077864321 38807954293556164558398241)
      ·
        refine ⟨29105965720167123418798681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38807954293556164558398241 29105965720167123418798681)
        ·
          refine ⟨21829474290125342564099011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29105965720167123418798681 21829474290125342564099011)
          ·
            refine ⟨32744211435188013846148517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21829474290125342564099011 32744211435188013846148517)
            ·
              refine ⟨6139539644097752596152847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32744211435188013846148517 6139539644097752596152847)
              ·
                refine ⟨9209309466146628894229271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6139539644097752596152847 9209309466146628894229271)
                ·
                  refine ⟨13813964199219943341343907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9209309466146628894229271 13813964199219943341343907)
                  ·
                    refine ⟨20720946298829915012015861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13813964199219943341343907 20720946298829915012015861)
                    ·
                      refine ⟨1942588715515304532376487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20720946298829915012015861 1942588715515304532376487)
                      ·
                        rfl

theorem cell23_3783178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_3783178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783178 prefixEnd_3783178 := by exact prefixLift 3783178
  have htrace : WordTrace (prefixWord ++ tailWord_3783178) baseStart_3783178 baseEnd_3783178 := by
    simpa [prefixWord, tailWord_3783178, baseEnd_3783178] using wordTrace_append hprefix tailTrace_3783178
  have hstable : (prefixWord ++ tailWord_3783178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783178).length < 2 ^ (prefixWord ++ tailWord_3783178).sum := by decide
  have hdescent : baseEnd_3783178 < baseStart_3783178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783192 : List Nat := [2, 1, 2, 3, 3, 1, 3, 1, 3, 2, 2]
def baseStart_3783192 : Nat := 118140960795 + 3783192 * 2 ^ 59
def prefixEnd_3783192 : Nat := 4983230072969 + 3 ^ 40 * 3783192 * 2
def baseEnd_3783192 : Nat := 1942595904244467477601423

theorem tailTrace_3783192 : CollatzResearch.WordTrace tailWord_3783192 prefixEnd_3783192 1942595904244467477601423 := by
  unfold tailWord_3783192
  simp only [CollatzResearch.WordTrace]
  refine ⟨68992174055074488299323915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91989565406765984399098553 68992174055074488299323915)
  ·
    refine ⟨103488261082611732448985873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68992174055074488299323915 103488261082611732448985873)
    ·
      refine ⟨77616195811958799336739405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103488261082611732448985873 77616195811958799336739405)
      ·
        refine ⟨29106073429484549751277277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77616195811958799336739405 29106073429484549751277277)
        ·
          refine ⟨10914777536056706156728979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29106073429484549751277277 10914777536056706156728979)
          ·
            refine ⟨16372166304085059235093469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10914777536056706156728979 16372166304085059235093469)
            ·
              refine ⟨6139562364031897213160051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16372166304085059235093469 6139562364031897213160051)
              ·
                refine ⟨9209343546047845819740077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6139562364031897213160051 9209343546047845819740077)
                ·
                  refine ⟨3453503829767942182402529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9209343546047845819740077 3453503829767942182402529)
                  ·
                    refine ⟨2590127872325956636801897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3453503829767942182402529 2590127872325956636801897)
                    ·
                      refine ⟨1942595904244467477601423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2590127872325956636801897 1942595904244467477601423)
                      ·
                        rfl

theorem cell23_3783192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_3783192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783192 prefixEnd_3783192 := by exact prefixLift 3783192
  have htrace : WordTrace (prefixWord ++ tailWord_3783192) baseStart_3783192 baseEnd_3783192 := by
    simpa [prefixWord, tailWord_3783192, baseEnd_3783192] using wordTrace_append hprefix tailTrace_3783192
  have hstable : (prefixWord ++ tailWord_3783192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783192).length < 2 ^ (prefixWord ++ tailWord_3783192).sum := by decide
  have hdescent : baseEnd_3783192 < baseStart_3783192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783201 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 2, 2, 6]
def baseStart_3783201 : Nat := 118140960795 + 3783201 * 2 ^ 59
def prefixEnd_3783201 : Nat := 4983230072969 + 3 ^ 40 * 3783201 * 2
def baseEnd_3783201 : Nat := 1942600525570357942388881

theorem tailTrace_3783201 : CollatzResearch.WordTrace tailWord_3783201 prefixEnd_3783201 1942600525570357942388881 := by
  unfold tailWord_3783201
  simp only [CollatzResearch.WordTrace]
  refine ⟨137984676367116371135725457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91989784244744247423816971 137984676367116371135725457)
  ·
    refine ⟨103488507275337278351794093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137984676367116371135725457 103488507275337278351794093)
    ·
      refine ⟨38808190228251479381922785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103488507275337278351794093 38808190228251479381922785)
      ·
        refine ⟨29106142671188609536442089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38808190228251479381922785 29106142671188609536442089)
        ·
          refine ⟨21829607003391457152331567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29106142671188609536442089 21829607003391457152331567)
          ·
            refine ⟨32744410505087185728497351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21829607003391457152331567 32744410505087185728497351)
            ·
              refine ⟨49116615757630778592746027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32744410505087185728497351 49116615757630778592746027)
              ·
                refine ⟨73674923636446167889119041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49116615757630778592746027 73674923636446167889119041)
                ·
                  refine ⟨55256192727334625916839281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73674923636446167889119041 55256192727334625916839281)
                  ·
                    refine ⟨41442144545500969437629461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55256192727334625916839281 41442144545500969437629461)
                    ·
                      refine ⟨1942600525570357942388881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41442144545500969437629461 1942600525570357942388881)
                      ·
                        rfl

theorem cell23_3783201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_3783201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783201 prefixEnd_3783201 := by exact prefixLift 3783201
  have htrace : WordTrace (prefixWord ++ tailWord_3783201) baseStart_3783201 baseEnd_3783201 := by
    simpa [prefixWord, tailWord_3783201, baseEnd_3783201] using wordTrace_append hprefix tailTrace_3783201
  have hstable : (prefixWord ++ tailWord_3783201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783201).length < 2 ^ (prefixWord ++ tailWord_3783201).sum := by decide
  have hdescent : baseEnd_3783201 < baseStart_3783201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783235 : List Nat := [1, 1, 1, 3, 1, 2, 1, 7, 1, 3, 2]
def baseStart_3783235 : Nat := 118140960795 + 3783235 * 2 ^ 59
def prefixEnd_3783235 : Nat := 4983230072969 + 3 ^ 40 * 3783235 * 2
def baseEnd_3783235 : Nat := 1942617983912610809363725

theorem tailTrace_3783235 : CollatzResearch.WordTrace tailWord_3783235 prefixEnd_3783235 1942617983912610809363725 := by
  unfold tailWord_3783235
  simp only [CollatzResearch.WordTrace]
  refine ⟨137985916448993194942463159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91990610965995463294975439 137985916448993194942463159)
  ·
    refine ⟨206978874673489792413694739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137985916448993194942463159 206978874673489792413694739)
    ·
      refine ⟨310468312010234688620542109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206978874673489792413694739 310468312010234688620542109)
      ·
        refine ⟨116425617003838008232703291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310468312010234688620542109 116425617003838008232703291)
        ·
          refine ⟨174638425505757012349054937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116425617003838008232703291 174638425505757012349054937)
          ·
            refine ⟨130978819129317759261791203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174638425505757012349054937 130978819129317759261791203)
            ·
              refine ⟨196468228693976638892686805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130978819129317759261791203 196468228693976638892686805)
              ·
                refine ⟨4604724110015077474047347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 196468228693976638892686805 4604724110015077474047347)
                ·
                  refine ⟨6907086165022616211071021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4604724110015077474047347 6907086165022616211071021)
                  ·
                    refine ⟨2590157311883481079151633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6907086165022616211071021 2590157311883481079151633)
                    ·
                      refine ⟨1942617983912610809363725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2590157311883481079151633 1942617983912610809363725)
                      ·
                        rfl

theorem cell23_3783235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 3, 2].length) (baseStart_3783235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783235 prefixEnd_3783235 := by exact prefixLift 3783235
  have htrace : WordTrace (prefixWord ++ tailWord_3783235) baseStart_3783235 baseEnd_3783235 := by
    simpa [prefixWord, tailWord_3783235, baseEnd_3783235] using wordTrace_append hprefix tailTrace_3783235
  have hstable : (prefixWord ++ tailWord_3783235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783235).length < 2 ^ (prefixWord ++ tailWord_3783235).sum := by decide
  have hdescent : baseEnd_3783235 < baseStart_3783235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783236 : List Nat := [2, 3, 5, 1, 1, 1, 2, 2, 2, 4]
def baseStart_3783236 : Nat := 118140960795 + 3783236 * 2 ^ 59
def prefixEnd_3783236 : Nat := 4983230072969 + 3 ^ 40 * 3783236 * 2
def baseEnd_3783236 : Nat := 647539499131088435150407

theorem tailTrace_3783236 : CollatzResearch.WordTrace tailWord_3783236 prefixEnd_3783236 647539499131088435150407 := by
  unfold tailWord_3783236
  simp only [CollatzResearch.WordTrace]
  refine ⟨68992976460994786056624781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91990635281326381408833041 68992976460994786056624781)
  ·
    refine ⟨25872366172873044771234293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68992976460994786056624781 25872366172873044771234293)
    ·
      refine ⟨2425534328706847947303215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25872366172873044771234293 2425534328706847947303215)
      ·
        refine ⟨3638301493060271920954823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2425534328706847947303215 3638301493060271920954823)
        ·
          refine ⟨5457452239590407881432235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3638301493060271920954823 5457452239590407881432235)
          ·
            refine ⟨8186178359385611822148353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5457452239590407881432235 8186178359385611822148353)
            ·
              refine ⟨6139633769539208866611265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8186178359385611822148353 6139633769539208866611265)
              ·
                refine ⟨4604725327154406649958449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6139633769539208866611265 4604725327154406649958449)
                ·
                  refine ⟨3453543995365804987468837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4604725327154406649958449 3453543995365804987468837)
                  ·
                    refine ⟨647539499131088435150407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3453543995365804987468837 647539499131088435150407)
                    ·
                      rfl

theorem cell23_3783236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_3783236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783236 prefixEnd_3783236 := by exact prefixLift 3783236
  have htrace : WordTrace (prefixWord ++ tailWord_3783236) baseStart_3783236 baseEnd_3783236 := by
    simpa [prefixWord, tailWord_3783236, baseEnd_3783236] using wordTrace_append hprefix tailTrace_3783236
  have hstable : (prefixWord ++ tailWord_3783236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783236).length < 2 ^ (prefixWord ++ tailWord_3783236).sum := by decide
  have hdescent : baseEnd_3783236 < baseStart_3783236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783242 : List Nat := [3, 1, 2, 1, 1, 5, 2, 2, 2, 1, 3]
def baseStart_3783242 : Nat := 118140960795 + 3783242 * 2 ^ 59
def prefixEnd_3783242 : Nat := 4983230072969 + 3 ^ 40 * 3783242 * 2
def baseEnd_3783242 : Nat := 1942621578277192281976193

theorem tailTrace_3783242 : CollatzResearch.WordTrace tailWord_3783242 prefixEnd_3783242 1942621578277192281976193 := by
  unfold tailWord_3783242
  simp only [CollatzResearch.WordTrace]
  refine ⟨34496542939991958784491995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91990781173311890091978653 34496542939991958784491995)
  ·
    refine ⟨51744814409987938176737993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34496542939991958784491995 51744814409987938176737993)
    ·
      refine ⟨38808610807490953632553495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51744814409987938176737993 38808610807490953632553495)
      ·
        refine ⟨58212916211236430448830243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38808610807490953632553495 58212916211236430448830243)
        ·
          refine ⟨87319374316854645673245365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58212916211236430448830243 87319374316854645673245365)
          ·
            refine ⟨8186191342205123031866753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87319374316854645673245365 8186191342205123031866753)
            ·
              refine ⟨6139643506653842273900065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8186191342205123031866753 6139643506653842273900065)
              ·
                refine ⟨4604732629990381705425049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6139643506653842273900065 4604732629990381705425049)
                ·
                  refine ⟨3453549472492786279068787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4604732629990381705425049 3453549472492786279068787)
                  ·
                    refine ⟨5180324208739179418603181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3453549472492786279068787 5180324208739179418603181)
                    ·
                      refine ⟨1942621578277192281976193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5180324208739179418603181 1942621578277192281976193)
                      ·
                        rfl

theorem cell23_3783242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_3783242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783242 prefixEnd_3783242 := by exact prefixLift 3783242
  have htrace : WordTrace (prefixWord ++ tailWord_3783242) baseStart_3783242 baseEnd_3783242 := by
    simpa [prefixWord, tailWord_3783242, baseEnd_3783242] using wordTrace_append hprefix tailTrace_3783242
  have hstable : (prefixWord ++ tailWord_3783242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783242).length < 2 ^ (prefixWord ++ tailWord_3783242).sum := by decide
  have hdescent : baseEnd_3783242 < baseStart_3783242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783265 : List Nat := [1, 2, 3, 1, 1, 4, 1, 3, 1, 4, 2]
def baseStart_3783265 : Nat := 118140960795 + 3783265 * 2 ^ 59
def prefixEnd_3783265 : Nat := 4983230072969 + 3 ^ 40 * 3783265 * 2
def baseEnd_3783265 : Nat := 1942633388332245691988587

theorem tailTrace_3783265 : CollatzResearch.WordTrace tailWord_3783265 prefixEnd_3783265 1942633388332245691988587 := by
  unfold tailWord_3783265
  simp only [CollatzResearch.WordTrace]
  refine ⟨137987010638884510066055249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91991340425923006710703499 137987010638884510066055249)
  ·
    refine ⟨103490257979163382549541437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137987010638884510066055249 103490257979163382549541437)
    ·
      refine ⟨38808846742186268456078039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103490257979163382549541437 38808846742186268456078039)
      ·
        refine ⟨58213270113279402684117059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38808846742186268456078039 58213270113279402684117059)
        ·
          refine ⟨87319905169919104026175589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58213270113279402684117059 87319905169919104026175589)
          ·
            refine ⟨16372482219359832004907923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87319905169919104026175589 16372482219359832004907923)
            ·
              refine ⟨24558723329039748007361885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16372482219359832004907923 24558723329039748007361885)
              ·
                refine ⟨9209521248389905502760707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24558723329039748007361885 9209521248389905502760707)
                ·
                  refine ⟨13814281872584858254141061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9209521248389905502760707 13814281872584858254141061)
                  ·
                    refine ⟨2590177851109660922651449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13814281872584858254141061 2590177851109660922651449)
                    ·
                      refine ⟨1942633388332245691988587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2590177851109660922651449 1942633388332245691988587)
                      ·
                        rfl

theorem cell23_3783265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 4, 2].length) (baseStart_3783265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783265 prefixEnd_3783265 := by exact prefixLift 3783265
  have htrace : WordTrace (prefixWord ++ tailWord_3783265) baseStart_3783265 baseEnd_3783265 := by
    simpa [prefixWord, tailWord_3783265, baseEnd_3783265] using wordTrace_append hprefix tailTrace_3783265
  have hstable : (prefixWord ++ tailWord_3783265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783265).length < 2 ^ (prefixWord ++ tailWord_3783265).sum := by decide
  have hdescent : baseEnd_3783265 < baseStart_3783265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783268 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 2, 4, 3]
def baseStart_3783268 : Nat := 118140960795 + 3783268 * 2 ^ 59
def prefixEnd_3783268 : Nat := 4983230072969 + 3 ^ 40 * 3783268 * 2
def baseEnd_3783268 : Nat := 1942634928774209180251073

theorem tailTrace_3783268 : CollatzResearch.WordTrace tailWord_3783268 prefixEnd_3783268 1942634928774209180251073 := by
  unfold tailWord_3783268
  simp only [CollatzResearch.WordTrace]
  refine ⟨68993560028936820789207229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91991413371915761052276305 68993560028936820789207229)
  ·
    refine ⟨25872585010851307795952711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68993560028936820789207229 25872585010851307795952711)
    ·
      refine ⟨38808877516276961693929067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25872585010851307795952711 38808877516276961693929067)
      ·
        refine ⟨58213316274415442540893601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38808877516276961693929067 58213316274415442540893601)
        ·
          refine ⟨43659987205811581905670201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58213316274415442540893601 43659987205811581905670201)
          ·
            refine ⟨32744990404358686429252651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43659987205811581905670201 32744990404358686429252651)
            ·
              refine ⟨49117485606538029643878977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32744990404358686429252651 49117485606538029643878977)
              ·
                refine ⟨36838114204903522232909233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49117485606538029643878977 36838114204903522232909233)
                ·
                  refine ⟨27628585653677641674681925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36838114204903522232909233 27628585653677641674681925)
                  ·
                    refine ⟨5180359810064557814002861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27628585653677641674681925 5180359810064557814002861)
                    ·
                      refine ⟨1942634928774209180251073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5180359810064557814002861 1942634928774209180251073)
                      ·
                        rfl

theorem cell23_3783268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_3783268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783268 prefixEnd_3783268 := by exact prefixLift 3783268
  have htrace : WordTrace (prefixWord ++ tailWord_3783268) baseStart_3783268 baseEnd_3783268 := by
    simpa [prefixWord, tailWord_3783268, baseEnd_3783268] using wordTrace_append hprefix tailTrace_3783268
  have hstable : (prefixWord ++ tailWord_3783268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783268).length < 2 ^ (prefixWord ++ tailWord_3783268).sum := by decide
  have hdescent : baseEnd_3783268 < baseStart_3783268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783281 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 3, 2, 7]
def baseStart_3783281 : Nat := 118140960795 + 3783281 * 2 ^ 59
def prefixEnd_3783281 : Nat := 4983230072969 + 3 ^ 40 * 3783281 * 2
def baseEnd_3783281 : Nat := 1942641604022717629388513

theorem tailTrace_3783281 : CollatzResearch.WordTrace tailWord_3783281 prefixEnd_3783281 1942641604022717629388513 := by
  unfold tailWord_3783281
  simp only [CollatzResearch.WordTrace]
  refine ⟨137987594206826544798637697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91991729471217696532425131 137987594206826544798637697)
  ·
    refine ⟨103490695655119908598978273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137987594206826544798637697 103490695655119908598978273)
    ·
      refine ⟨77618021741339931449233705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103490695655119908598978273 77618021741339931449233705)
      ·
        refine ⟨58213516306004948586925279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77618021741339931449233705 58213516306004948586925279)
        ·
          refine ⟨87320274459007422880387919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58213516306004948586925279 87320274459007422880387919)
          ·
            refine ⟨130980411688511134320581879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87320274459007422880387919 130980411688511134320581879)
            ·
              refine ⟨196470617532766701480872819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130980411688511134320581879 196470617532766701480872819)
              ·
                refine ⟨294705926299150052221309229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196470617532766701480872819 294705926299150052221309229)
                ·
                  refine ⟨110514722362181269582990961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294705926299150052221309229 110514722362181269582990961)
                  ·
                    refine ⟨82886041771635952187243221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110514722362181269582990961 82886041771635952187243221)
                    ·
                      refine ⟨1942641604022717629388513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 82886041771635952187243221 1942641604022717629388513)
                      ·
                        rfl

theorem cell23_3783281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_3783281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783281 prefixEnd_3783281 := by exact prefixLift 3783281
  have htrace : WordTrace (prefixWord ++ tailWord_3783281) baseStart_3783281 baseEnd_3783281 := by
    simpa [prefixWord, tailWord_3783281, baseEnd_3783281] using wordTrace_append hprefix tailTrace_3783281
  have hstable : (prefixWord ++ tailWord_3783281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783281).length < 2 ^ (prefixWord ++ tailWord_3783281).sum := by decide
  have hdescent : baseEnd_3783281 < baseStart_3783281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783325 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 2, 5, 2]
def baseStart_3783325 : Nat := 118140960795 + 3783325 * 2 ^ 59
def prefixEnd_3783325 : Nat := 4983230072969 + 3 ^ 40 * 3783325 * 2
def baseEnd_3783325 : Nat := 1942664197171515457238311

theorem tailTrace_3783325 : CollatzResearch.WordTrace tailWord_3783325 prefixEnd_3783325 1942664197171515457238311 := by
  unfold tailWord_3783325
  simp only [CollatzResearch.WordTrace]
  refine ⟨137989199018667140313239429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91992799345778093542159619 137989199018667140313239429)
  ·
    refine ⟨25872974816000088808732393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137989199018667140313239429 25872974816000088808732393)
    ·
      refine ⟨19404731112000066606549295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25872974816000088808732393 19404731112000066606549295)
      ·
        refine ⟨29107096668000099909823943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19404731112000066606549295 29107096668000099909823943)
        ·
          refine ⟨43660645002000149864735915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29107096668000099909823943 43660645002000149864735915)
          ·
            refine ⟨65490967503000224797103873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43660645002000149864735915 65490967503000224797103873)
            ·
              refine ⟨49118225627250168597827905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65490967503000224797103873 49118225627250168597827905)
              ·
                refine ⟨36838669220437626448370929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49118225627250168597827905 36838669220437626448370929)
                ·
                  refine ⟨27629001915328219836278197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36838669220437626448370929 27629001915328219836278197)
                  ·
                    refine ⟨2590218929562020609651081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27629001915328219836278197 2590218929562020609651081)
                    ·
                      refine ⟨1942664197171515457238311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2590218929562020609651081 1942664197171515457238311)
                      ·
                        rfl

theorem cell23_3783325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_3783325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783325 prefixEnd_3783325 := by exact prefixLift 3783325
  have htrace : WordTrace (prefixWord ++ tailWord_3783325) baseStart_3783325 baseEnd_3783325 := by
    simpa [prefixWord, tailWord_3783325, baseEnd_3783325] using wordTrace_append hprefix tailTrace_3783325
  have hstable : (prefixWord ++ tailWord_3783325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783325).length < 2 ^ (prefixWord ++ tailWord_3783325).sum := by decide
  have hdescent : baseEnd_3783325 < baseStart_3783325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783415 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 3, 5, 2]
def baseStart_3783415 : Nat := 118140960795 + 3783415 * 2 ^ 59
def prefixEnd_3783415 : Nat := 4983230072969 + 3 ^ 40 * 3783415 * 2
def baseEnd_3783415 : Nat := 1942710410430420105112897

theorem tailTrace_3783415 : CollatzResearch.WordTrace tailWord_3783415 prefixEnd_3783415 1942710410430420105112897 := by
  unfold tailWord_3783415
  simp only [CollatzResearch.WordTrace]
  refine ⟨137992481588341085684015699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91994987725560723789343799 137992481588341085684015699)
  ·
    refine ⟨206988722382511628526023549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137992481588341085684015699 206988722382511628526023549)
    ·
      refine ⟨77620770893441860697258831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206988722382511628526023549 77620770893441860697258831)
      ·
        refine ⟨116431156340162791045888247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77620770893441860697258831 116431156340162791045888247)
        ·
          refine ⟨174646734510244186568832371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116431156340162791045888247 174646734510244186568832371)
          ·
            refine ⟨261970101765366279853248557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174646734510244186568832371 261970101765366279853248557)
            ·
              refine ⟨98238788162012354944968209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261970101765366279853248557 98238788162012354944968209)
              ·
                refine ⟨73679091121509266208726157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98238788162012354944968209 73679091121509266208726157)
                ·
                  refine ⟨27629659170565974828272309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73679091121509266208726157 27629659170565974828272309)
                  ·
                    refine ⟨2590280547240560140150529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27629659170565974828272309 2590280547240560140150529)
                    ·
                      refine ⟨1942710410430420105112897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2590280547240560140150529 1942710410430420105112897)
                      ·
                        rfl

theorem cell23_3783415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 5, 2].length) (baseStart_3783415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783415 prefixEnd_3783415 := by exact prefixLift 3783415
  have htrace : WordTrace (prefixWord ++ tailWord_3783415) baseStart_3783415 baseEnd_3783415 := by
    simpa [prefixWord, tailWord_3783415, baseEnd_3783415] using wordTrace_append hprefix tailTrace_3783415
  have hstable : (prefixWord ++ tailWord_3783415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783415).length < 2 ^ (prefixWord ++ tailWord_3783415).sum := by decide
  have hdescent : baseEnd_3783415 < baseStart_3783415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783445 : List Nat := [1, 3, 2, 1, 2, 2, 1, 3, 3, 1, 4]
def baseStart_3783445 : Nat := 118140960795 + 3783445 * 2 ^ 59
def prefixEnd_3783445 : Nat := 4983230072969 + 3 ^ 40 * 3783445 * 2
def baseEnd_3783445 : Nat := 1942725814850054987737759

theorem tailTrace_3783445 : CollatzResearch.WordTrace tailWord_3783445 prefixEnd_3783445 1942725814850054987737759 := by
  unfold tailWord_3783445
  simp only [CollatzResearch.WordTrace]
  refine ⟨137993575778232400807607789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91995717185488267205071859 137993575778232400807607789)
  ·
    refine ⟨51747590916837150302852921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137993575778232400807607789 51747590916837150302852921)
    ·
      refine ⟨38810693187627862727139691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51747590916837150302852921 38810693187627862727139691)
      ·
        refine ⟨58216039781441794090709537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38810693187627862727139691 58216039781441794090709537)
        ·
          refine ⟨43662029836081345568032153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58216039781441794090709537 43662029836081345568032153)
          ·
            refine ⟨32746522377061009176024115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43662029836081345568032153 32746522377061009176024115)
            ·
              refine ⟨49119783565591513764036173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32746522377061009176024115 49119783565591513764036173)
              ·
                refine ⟨18419918837096817661513565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49119783565591513764036173 18419918837096817661513565)
                ·
                  refine ⟨6907469563911306623067587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18419918837096817661513565 6907469563911306623067587)
                  ·
                    refine ⟨10361204345866959934601381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6907469563911306623067587 10361204345866959934601381)
                    ·
                      refine ⟨1942725814850054987737759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10361204345866959934601381 1942725814850054987737759)
                      ·
                        rfl

theorem cell23_3783445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_3783445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783445 prefixEnd_3783445 := by exact prefixLift 3783445
  have htrace : WordTrace (prefixWord ++ tailWord_3783445) baseStart_3783445 baseEnd_3783445 := by
    simpa [prefixWord, tailWord_3783445, baseEnd_3783445] using wordTrace_append hprefix tailTrace_3783445
  have hstable : (prefixWord ++ tailWord_3783445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783445).length < 2 ^ (prefixWord ++ tailWord_3783445).sum := by decide
  have hdescent : baseEnd_3783445 < baseStart_3783445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783455 : List Nat := [1, 1, 2, 4, 2, 2, 2, 2, 1, 6]
def baseStart_3783455 : Nat := 118140960795 + 3783455 * 2 ^ 59
def prefixEnd_3783455 : Nat := 4983230072969 + 3 ^ 40 * 3783455 * 2
def baseEnd_3783455 : Nat := 647576983218866649537571

theorem tailTrace_3783455 : CollatzResearch.WordTrace tailWord_3783455 prefixEnd_3783455 647576983218866649537571 := by
  unfold tailWord_3783455
  simp only [CollatzResearch.WordTrace]
  refine ⟨137993940508196172515471819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91995960338797448343647879 137993940508196172515471819)
  ·
    refine ⟨206990910762294258773207729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137993940508196172515471819 206990910762294258773207729)
    ·
      refine ⟨155243183071720694079905797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206990910762294258773207729 155243183071720694079905797)
      ·
        refine ⟨29108096825947630139982337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155243183071720694079905797 29108096825947630139982337)
        ·
          refine ⟨21831072619460722604986753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29108096825947630139982337 21831072619460722604986753)
          ·
            refine ⟨16373304464595541953740065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21831072619460722604986753 16373304464595541953740065)
            ·
              refine ⟨12279978348446656465305049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16373304464595541953740065 12279978348446656465305049)
              ·
                refine ⟨9209983761334992348978787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12279978348446656465305049 9209983761334992348978787)
                ·
                  refine ⟨13814975642002488523468181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9209983761334992348978787 13814975642002488523468181)
                  ·
                    refine ⟨647576983218866649537571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13814975642002488523468181 647576983218866649537571)
                    ·
                      rfl

theorem cell23_3783455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 6].length) (baseStart_3783455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783455 prefixEnd_3783455 := by exact prefixLift 3783455
  have htrace : WordTrace (prefixWord ++ tailWord_3783455) baseStart_3783455 baseEnd_3783455 := by
    simpa [prefixWord, tailWord_3783455, baseEnd_3783455] using wordTrace_append hprefix tailTrace_3783455
  have hstable : (prefixWord ++ tailWord_3783455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783455).length < 2 ^ (prefixWord ++ tailWord_3783455).sum := by decide
  have hdescent : baseEnd_3783455 < baseStart_3783455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783456 : List Nat := [2, 1, 1, 5, 1, 3, 2, 3, 1, 1, 3]
def baseStart_3783456 : Nat := 118140960795 + 3783456 * 2 ^ 59
def prefixEnd_3783456 : Nat := 4983230072969 + 3 ^ 40 * 3783456 * 2
def baseEnd_3783456 : Nat := 1942731463137254444700209

theorem tailTrace_3783456 : CollatzResearch.WordTrace tailWord_3783456 prefixEnd_3783456 1942731463137254444700209 := by
  unfold tailWord_3783456
  simp only [CollatzResearch.WordTrace]
  refine ⟨68996988490596274843129111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91995984654128366457505481 68996988490596274843129111)
  ·
    refine ⟨103495482735894412264693667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68996988490596274843129111 103495482735894412264693667)
    ·
      refine ⟨155243224103841618397040501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103495482735894412264693667 155243224103841618397040501)
      ·
        refine ⟨14554052259735151724722547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155243224103841618397040501 14554052259735151724722547)
        ·
          refine ⟨21831078389602727587083821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14554052259735151724722547 21831078389602727587083821)
          ·
            refine ⟨8186654396101022845156433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21831078389602727587083821 8186654396101022845156433)
            ·
              refine ⟨6139990797075767133867325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8186654396101022845156433 6139990797075767133867325)
              ·
                refine ⟨2302496548903412675200247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6139990797075767133867325 2302496548903412675200247)
                ·
                  refine ⟨3453744823355119012800371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2302496548903412675200247 3453744823355119012800371)
                  ·
                    refine ⟨5180617235032678519200557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3453744823355119012800371 5180617235032678519200557)
                    ·
                      refine ⟨1942731463137254444700209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5180617235032678519200557 1942731463137254444700209)
                      ·
                        rfl

theorem cell23_3783456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_3783456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783456 prefixEnd_3783456 := by exact prefixLift 3783456
  have htrace : WordTrace (prefixWord ++ tailWord_3783456) baseStart_3783456 baseEnd_3783456 := by
    simpa [prefixWord, tailWord_3783456, baseEnd_3783456] using wordTrace_append hprefix tailTrace_3783456
  have hstable : (prefixWord ++ tailWord_3783456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783456).length < 2 ^ (prefixWord ++ tailWord_3783456).sum := by decide
  have hdescent : baseEnd_3783456 < baseStart_3783456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783468 : List Nat := [2, 2, 1, 1, 1, 4, 12]
def baseStart_3783468 : Nat := 118140960795 + 3783468 * 2 ^ 59
def prefixEnd_3783468 : Nat := 4983230072969 + 3 ^ 40 * 3783468 * 2
def baseEnd_3783468 : Nat := 23984415122285288861113

theorem tailTrace_3783468 : CollatzResearch.WordTrace tailWord_3783468 prefixEnd_3783468 23984415122285288861113 := by
  unfold tailWord_3783468
  simp only [CollatzResearch.WordTrace]
  refine ⟨68997207328574537867847529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91996276438099383823796705 68997207328574537867847529)
  ·
    refine ⟨51747905496430903400885647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68997207328574537867847529 51747905496430903400885647)
    ·
      refine ⟨77621858244646355101328471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51747905496430903400885647 77621858244646355101328471)
      ·
        refine ⟨116432787366969532651992707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77621858244646355101328471 116432787366969532651992707)
        ·
          refine ⟨174649181050454298977989061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116432787366969532651992707 174649181050454298977989061)
          ·
            refine ⟨32746721446960181058372949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174649181050454298977989061 32746721446960181058372949)
            ·
              refine ⟨23984415122285288861113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 32746721446960181058372949 23984415122285288861113)
              ·
                rfl

theorem cell23_3783468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 12].length) (baseStart_3783468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783468 prefixEnd_3783468 := by exact prefixLift 3783468
  have htrace : WordTrace (prefixWord ++ tailWord_3783468) baseStart_3783468 baseEnd_3783468 := by
    simpa [prefixWord, tailWord_3783468, baseEnd_3783468] using wordTrace_append hprefix tailTrace_3783468
  have hstable : (prefixWord ++ tailWord_3783468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783468).length < 2 ^ (prefixWord ++ tailWord_3783468).sum := by decide
  have hdescent : baseEnd_3783468 < baseStart_3783468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783479 : List Nat := [1, 1, 3, 1, 2, 1, 6, 1, 3, 2, 2]
def baseStart_3783479 : Nat := 118140960795 + 3783479 * 2 ^ 59
def prefixEnd_3783479 : Nat := 4983230072969 + 3 ^ 40 * 3783479 * 2
def baseEnd_3783479 : Nat := 1942743273192307854712603

theorem tailTrace_3783479 : CollatzResearch.WordTrace tailWord_3783479 prefixEnd_3783479 1942743273192307854712603 := by
  unfold tailWord_3783479
  simp only [CollatzResearch.WordTrace]
  refine ⟨137994815860109224614345491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91996543906739483076230327 137994815860109224614345491)
  ·
    refine ⟨206992223790163836921518237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137994815860109224614345491 206992223790163836921518237)
    ·
      refine ⟨77622083921311438845569339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206992223790163836921518237 77622083921311438845569339)
      ·
        refine ⟨116433125881967158268354009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77622083921311438845569339 116433125881967158268354009)
        ·
          refine ⟨87324844411475368701265507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116433125881967158268354009 87324844411475368701265507)
          ·
            refine ⟨130987266617213053051898261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87324844411475368701265507 130987266617213053051898261)
            ·
              refine ⟨6140028122681861861807731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130987266617213053051898261 6140028122681861861807731)
              ·
                refine ⟨9210042184022792792711597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6140028122681861861807731 9210042184022792792711597)
                ·
                  refine ⟨3453765819008547297266849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9210042184022792792711597 3453765819008547297266849)
                  ·
                    refine ⟨2590324364256410472950137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3453765819008547297266849 2590324364256410472950137)
                    ·
                      refine ⟨1942743273192307854712603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2590324364256410472950137 1942743273192307854712603)
                      ·
                        rfl

theorem cell23_3783479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 3, 2, 2].length) (baseStart_3783479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783479 prefixEnd_3783479 := by exact prefixLift 3783479
  have htrace : WordTrace (prefixWord ++ tailWord_3783479) baseStart_3783479 baseEnd_3783479 := by
    simpa [prefixWord, tailWord_3783479, baseEnd_3783479] using wordTrace_append hprefix tailTrace_3783479
  have hstable : (prefixWord ++ tailWord_3783479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783479).length < 2 ^ (prefixWord ++ tailWord_3783479).sum := by decide
  have hdescent : baseEnd_3783479 < baseStart_3783479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783482 : List Nat := [3, 1, 1, 1, 6, 1, 1, 2, 1, 1, 5]
def baseStart_3783482 : Nat := 118140960795 + 3783482 * 2 ^ 59
def prefixEnd_3783482 : Nat := 4983230072969 + 3 ^ 40 * 3783482 * 2
def baseEnd_3783482 : Nat := 1942744813634271342975089

theorem tailTrace_3783482 : CollatzResearch.WordTrace tailWord_3783482 prefixEnd_3783482 1942744813634271342975089 := by
  unfold tailWord_3783482
  simp only [CollatzResearch.WordTrace]
  refine ⟨34498731319774589031676175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91996616852732237417803133 34498731319774589031676175)
  ·
    refine ⟨51748096979661883547514263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34498731319774589031676175 51748096979661883547514263)
    ·
      refine ⟨77622145469492825321271395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51748096979661883547514263 77622145469492825321271395)
      ·
        refine ⟨116433218204239237981907093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77622145469492825321271395 116433218204239237981907093)
        ·
          refine ⟨5457807103323714280401895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 116433218204239237981907093 5457807103323714280401895)
          ·
            refine ⟨8186710654985571420602843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5457807103323714280401895 8186710654985571420602843)
            ·
              refine ⟨12280065982478357130904265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8186710654985571420602843 12280065982478357130904265)
              ·
                refine ⟨9210049486858767848178199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12280065982478357130904265 9210049486858767848178199)
                ·
                  refine ⟨13815074230288151772267299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9210049486858767848178199 13815074230288151772267299)
                  ·
                    refine ⟨20722611345432227658400949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13815074230288151772267299 20722611345432227658400949)
                    ·
                      refine ⟨1942744813634271342975089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20722611345432227658400949 1942744813634271342975089)
                      ·
                        rfl

theorem cell23_3783482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 1, 1, 5].length) (baseStart_3783482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783482 prefixEnd_3783482 := by exact prefixLift 3783482
  have htrace : WordTrace (prefixWord ++ tailWord_3783482) baseStart_3783482 baseEnd_3783482 := by
    simpa [prefixWord, tailWord_3783482, baseEnd_3783482] using wordTrace_append hprefix tailTrace_3783482
  have hstable : (prefixWord ++ tailWord_3783482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783482).length < 2 ^ (prefixWord ++ tailWord_3783482).sum := by decide
  have hdescent : baseEnd_3783482 < baseStart_3783482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783513 : List Nat := [1, 2, 1, 2, 2, 6, 1, 3, 1, 2, 2]
def baseStart_3783513 : Nat := 118140960795 + 3783513 * 2 ^ 59
def prefixEnd_3783513 : Nat := 4983230072969 + 3 ^ 40 * 3783513 * 2
def baseEnd_3783513 : Nat := 1942760731534560721687447

theorem tailTrace_3783513 : CollatzResearch.WordTrace tailWord_3783513 prefixEnd_3783513 1942760731534560721687447 := by
  unfold tailWord_3783513
  simp only [CollatzResearch.WordTrace]
  refine ⟨137996055941986048421083193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91997370627990698947388795 137996055941986048421083193)
  ·
    refine ⟨103497041956489536315812395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137996055941986048421083193 103497041956489536315812395)
    ·
      refine ⟨155245562934734304473718593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103497041956489536315812395 155245562934734304473718593)
      ·
        refine ⟨116434172201050728355288945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155245562934734304473718593 116434172201050728355288945)
        ·
          refine ⟨87325629150788046266466709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116434172201050728355288945 87325629150788046266466709)
          ·
            refine ⟨4093388866443189668740627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 87325629150788046266466709 4093388866443189668740627)
            ·
              refine ⟨6140083299664784503110941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4093388866443189668740627 6140083299664784503110941)
              ·
                refine ⟨2302531237374294188666603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6140083299664784503110941 2302531237374294188666603)
                ·
                  refine ⟨3453796856061441282999905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2302531237374294188666603 3453796856061441282999905)
                  ·
                    refine ⟨2590347642046080962249929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3453796856061441282999905 2590347642046080962249929)
                    ·
                      refine ⟨1942760731534560721687447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2590347642046080962249929 1942760731534560721687447)
                      ·
                        rfl

theorem cell23_3783513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 3, 1, 2, 2].length) (baseStart_3783513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783513 prefixEnd_3783513 := by exact prefixLift 3783513
  have htrace : WordTrace (prefixWord ++ tailWord_3783513) baseStart_3783513 baseEnd_3783513 := by
    simpa [prefixWord, tailWord_3783513, baseEnd_3783513] using wordTrace_append hprefix tailTrace_3783513
  have hstable : (prefixWord ++ tailWord_3783513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783513).length < 2 ^ (prefixWord ++ tailWord_3783513).sum := by decide
  have hdescent : baseEnd_3783513 < baseStart_3783513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783550 : List Nat := [4, 2, 3, 1, 3, 1, 1, 2, 1, 2, 3]
def baseStart_3783550 : Nat := 118140960795 + 3783550 * 2 ^ 59
def prefixEnd_3783550 : Nat := 4983230072969 + 3 ^ 40 * 3783550 * 2
def baseEnd_3783550 : Nat := 1942779730318777076924777

theorem tailTrace_3783550 : CollatzResearch.WordTrace tailWord_3783550 prefixEnd_3783550 1942779730318777076924777 := by
  unfold tailWord_3783550
  simp only [CollatzResearch.WordTrace]
  refine ⟨17249675680356500467522513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91998270295234669160120069 17249675680356500467522513)
  ·
    refine ⟨12937256760267375350641885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17249675680356500467522513 12937256760267375350641885)
    ·
      refine ⟨4851471285100265756490707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12937256760267375350641885 4851471285100265756490707)
      ·
        refine ⟨7277206927650398634736061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4851471285100265756490707 7277206927650398634736061)
        ·
          refine ⟨2728952597868899488026023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7277206927650398634736061 2728952597868899488026023)
          ·
            refine ⟨4093428896803349232039035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2728952597868899488026023 4093428896803349232039035)
            ·
              refine ⟨6140143345205023848058553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4093428896803349232039035 6140143345205023848058553)
              ·
                refine ⟨4605107508903767886043915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6140143345205023848058553 4605107508903767886043915)
                ·
                  refine ⟨6907661263355651829065873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4605107508903767886043915 6907661263355651829065873)
                  ·
                    refine ⟨5180745947516738871799405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6907661263355651829065873 5180745947516738871799405)
                    ·
                      refine ⟨1942779730318777076924777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5180745947516738871799405 1942779730318777076924777)
                      ·
                        rfl

theorem cell23_3783550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_3783550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783550 prefixEnd_3783550 := by exact prefixLift 3783550
  have htrace : WordTrace (prefixWord ++ tailWord_3783550) baseStart_3783550 baseEnd_3783550 := by
    simpa [prefixWord, tailWord_3783550, baseEnd_3783550] using wordTrace_append hprefix tailTrace_3783550
  have hstable : (prefixWord ++ tailWord_3783550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783550).length < 2 ^ (prefixWord ++ tailWord_3783550).sum := by decide
  have hdescent : baseEnd_3783550 < baseStart_3783550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783555 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 5]
def baseStart_3783555 : Nat := 118140960795 + 3783555 * 2 ^ 59
def prefixEnd_3783555 : Nat := 4983230072969 + 3 ^ 40 * 3783555 * 2
def baseEnd_3783555 : Nat := 1942782297722049557362253

theorem tailTrace_3783555 : CollatzResearch.WordTrace tailWord_3783555 prefixEnd_3783555 1942782297722049557362253 := by
  unfold tailWord_3783555
  simp only [CollatzResearch.WordTrace]
  refine ⟨137997587807833889594112119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91998391871889259729408079 137997587807833889594112119)
  ·
    refine ⟨206996381711750834391168179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137997587807833889594112119 206996381711750834391168179)
    ·
      refine ⟨310494572567626251586752269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206996381711750834391168179 310494572567626251586752269)
      ·
        refine ⟨116435464712859844345032101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310494572567626251586752269 116435464712859844345032101)
        ·
          refine ⟨21831649633661220814693519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116435464712859844345032101 21831649633661220814693519)
          ·
            refine ⟨32747474450491831222040279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21831649633661220814693519 32747474450491831222040279)
            ·
              refine ⟨49121211675737746833060419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32747474450491831222040279 49121211675737746833060419)
              ·
                refine ⟨73681817513606620249590629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49121211675737746833060419 73681817513606620249590629)
                ·
                  refine ⟨13815340783801241296798243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73681817513606620249590629 13815340783801241296798243)
                  ·
                    refine ⟨20723011175701861945197365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13815340783801241296798243 20723011175701861945197365)
                    ·
                      refine ⟨1942782297722049557362253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20723011175701861945197365 1942782297722049557362253)
                      ·
                        rfl

theorem cell23_3783555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_3783555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783555 prefixEnd_3783555 := by exact prefixLift 3783555
  have htrace : WordTrace (prefixWord ++ tailWord_3783555) baseStart_3783555 baseEnd_3783555 := by
    simpa [prefixWord, tailWord_3783555, baseEnd_3783555] using wordTrace_append hprefix tailTrace_3783555
  have hstable : (prefixWord ++ tailWord_3783555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783555).length < 2 ^ (prefixWord ++ tailWord_3783555).sum := by decide
  have hdescent : baseEnd_3783555 < baseStart_3783555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783572 : List Nat := [2, 4, 2, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_3783572 : Nat := 118140960795 + 3783572 * 2 ^ 59
def prefixEnd_3783572 : Nat := 4983230072969 + 3 ^ 40 * 3783572 * 2
def baseEnd_3783572 : Nat := 1942791026893175990849675

theorem tailTrace_3783572 : CollatzResearch.WordTrace tailWord_3783572 prefixEnd_3783572 1942791026893175990849675 := by
  unfold tailWord_3783572
  simp only [CollatzResearch.WordTrace]
  refine ⟨68999103924386150748740485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91998805232514867664987313 68999103924386150748740485)
  ·
    refine ⟨12937331985822403265388841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68999103924386150748740485 12937331985822403265388841)
    ·
      refine ⟨9702998989366802449041631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12937331985822403265388841 9702998989366802449041631)
      ·
        refine ⟨14554498484050203673562447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9702998989366802449041631 14554498484050203673562447)
        ·
          refine ⟨21831747726075305510343671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14554498484050203673562447 21831747726075305510343671)
          ·
            refine ⟨32747621589112958265515507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21831747726075305510343671 32747621589112958265515507)
            ·
              refine ⟨49121432383669437398273261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32747621589112958265515507 49121432383669437398273261)
              ·
                refine ⟨18420537143876039024352473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49121432383669437398273261 18420537143876039024352473)
                ·
                  refine ⟨13815402857907029268264355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18420537143876039024352473 13815402857907029268264355)
                  ·
                    refine ⟨20723104286860543902396533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13815402857907029268264355 20723104286860543902396533)
                    ·
                      refine ⟨1942791026893175990849675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20723104286860543902396533 1942791026893175990849675)
                      ·
                        rfl

theorem cell23_3783572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_3783572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783572 prefixEnd_3783572 := by exact prefixLift 3783572
  have htrace : WordTrace (prefixWord ++ tailWord_3783572) baseStart_3783572 baseEnd_3783572 := by
    simpa [prefixWord, tailWord_3783572, baseEnd_3783572] using wordTrace_append hprefix tailTrace_3783572
  have hstable : (prefixWord ++ tailWord_3783572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783572).length < 2 ^ (prefixWord ++ tailWord_3783572).sum := by decide
  have hdescent : baseEnd_3783572 < baseStart_3783572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783615 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 5]
def baseStart_3783615 : Nat := 118140960795 + 3783615 * 2 ^ 59
def prefixEnd_3783615 : Nat := 4983230072969 + 3 ^ 40 * 3783615 * 2
def baseEnd_3783615 : Nat := 1942813106561319322611977

theorem tailTrace_3783615 : CollatzResearch.WordTrace tailWord_3783615 prefixEnd_3783615 1942813106561319322611977 := by
  unfold tailWord_3783615
  simp only [CollatzResearch.WordTrace]
  refine ⟨137999776187616519841296299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91999850791744346560864199 137999776187616519841296299)
  ·
    refine ⟨206999664281424779761944449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137999776187616519841296299 206999664281424779761944449)
    ·
      refine ⟨155249748211068584821458337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206999664281424779761944449 155249748211068584821458337)
      ·
        refine ⟨116437311158301438616093753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155249748211068584821458337 116437311158301438616093753)
        ·
          refine ⟨87327983368726078962070315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116437311158301438616093753 87327983368726078962070315)
          ·
            refine ⟨130991975053089118443105473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87327983368726078962070315 130991975053089118443105473)
            ·
              refine ⟨98243981289816838832329105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130991975053089118443105473 98243981289816838832329105)
              ·
                refine ⟨73682985967362629124246829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98243981289816838832329105 73682985967362629124246829)
                ·
                  refine ⟨27631119737760985921592561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73682985967362629124246829 27631119737760985921592561)
                  ·
                    refine ⟨20723339803320739441194421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27631119737760985921592561 20723339803320739441194421)
                    ·
                      refine ⟨1942813106561319322611977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20723339803320739441194421 1942813106561319322611977)
                      ·
                        rfl

theorem cell23_3783615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_3783615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783615 prefixEnd_3783615 := by exact prefixLift 3783615
  have htrace : WordTrace (prefixWord ++ tailWord_3783615) baseStart_3783615 baseEnd_3783615 := by
    simpa [prefixWord, tailWord_3783615, baseEnd_3783615] using wordTrace_append hprefix tailTrace_3783615
  have hstable : (prefixWord ++ tailWord_3783615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783615).length < 2 ^ (prefixWord ++ tailWord_3783615).sum := by decide
  have hdescent : baseEnd_3783615 < baseStart_3783615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783716 : List Nat := [2, 3, 1, 4, 1, 1, 4, 1, 6]
def baseStart_3783716 : Nat := 118140960795 + 3783716 * 2 ^ 59
def prefixEnd_3783716 : Nat := 4983230072969 + 3 ^ 40 * 3783716 * 2
def baseEnd_3783716 : Nat := 215873885345269269716557

theorem tailTrace_3783716 : CollatzResearch.WordTrace tailWord_3783716 prefixEnd_3783716 215873885345269269716557 := by
  unfold tailWord_3783716
  simp only [CollatzResearch.WordTrace]
  refine ⟨69001729980125307045361501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92002306640167076060482001 69001729980125307045361501)
  ·
    refine ⟨25875648742546990142010563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69001729980125307045361501 25875648742546990142010563)
    ·
      refine ⟨38813473113820485213015845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25875648742546990142010563 38813473113820485213015845)
      ·
        refine ⟨7277526208841340977440471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38813473113820485213015845 7277526208841340977440471)
        ·
          refine ⟨10916289313262011466160707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7277526208841340977440471 10916289313262011466160707)
          ·
            refine ⟨16374433969893017199241061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10916289313262011466160707 16374433969893017199241061)
            ·
              refine ⟨3070206369354940724857699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16374433969893017199241061 3070206369354940724857699)
              ·
                refine ⟨4605309554032411087286549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3070206369354940724857699 4605309554032411087286549)
                ·
                  refine ⟨215873885345269269716557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4605309554032411087286549 215873885345269269716557)
                  ·
                    rfl

theorem cell23_3783716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 6].length) (baseStart_3783716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783716 prefixEnd_3783716 := by exact prefixLift 3783716
  have htrace : WordTrace (prefixWord ++ tailWord_3783716) baseStart_3783716 baseEnd_3783716 := by
    simpa [prefixWord, tailWord_3783716, baseEnd_3783716] using wordTrace_append hprefix tailTrace_3783716
  have hstable : (prefixWord ++ tailWord_3783716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783716).length < 2 ^ (prefixWord ++ tailWord_3783716).sum := by decide
  have hdescent : baseEnd_3783716 < baseStart_3783716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783726 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 5, 1, 3]
def baseStart_3783726 : Nat := 118140960795 + 3783726 * 2 ^ 59
def prefixEnd_3783726 : Nat := 4983230072969 + 3 ^ 40 * 3783726 * 2
def baseEnd_3783726 : Nat := 1942870102913968388323967

theorem tailTrace_3783726 : CollatzResearch.WordTrace tailWord_3783726 prefixEnd_3783726 1942870102913968388323967 := by
  unfold tailWord_3783726
  simp only [CollatzResearch.WordTrace]
  refine ⟨17250478086276798224823379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92002549793476257199058021 17250478086276798224823379)
  ·
    refine ⟨25875717129415197337235069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17250478086276798224823379 25875717129415197337235069)
    ·
      refine ⟨9703393923530699001463151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25875717129415197337235069 9703393923530699001463151)
      ·
        refine ⟨14555090885296048502194727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9703393923530699001463151 14555090885296048502194727)
        ·
          refine ⟨21832636327944072753292091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14555090885296048502194727 21832636327944072753292091)
          ·
            refine ⟨32748954491916109129938137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21832636327944072753292091 32748954491916109129938137)
            ·
              refine ⟨24561715868937081847453603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32748954491916109129938137 24561715868937081847453603)
              ·
                refine ⟨36842573803405622771180405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24561715868937081847453603 36842573803405622771180405)
                ·
                  refine ⟨3453991294069277134798163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36842573803405622771180405 3453991294069277134798163)
                  ·
                    refine ⟨5180986941103915702197245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3453991294069277134798163 5180986941103915702197245)
                    ·
                      refine ⟨1942870102913968388323967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5180986941103915702197245 1942870102913968388323967)
                      ·
                        rfl

theorem cell23_3783726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_3783726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783726 prefixEnd_3783726 := by exact prefixLift 3783726
  have htrace : WordTrace (prefixWord ++ tailWord_3783726) baseStart_3783726 baseEnd_3783726 := by
    simpa [prefixWord, tailWord_3783726, baseEnd_3783726] using wordTrace_append hprefix tailTrace_3783726
  have hstable : (prefixWord ++ tailWord_3783726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783726).length < 2 ^ (prefixWord ++ tailWord_3783726).sum := by decide
  have hdescent : baseEnd_3783726 < baseStart_3783726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783736 : List Nat := [2, 1, 2, 1, 5, 1, 1, 3, 2, 3, 2]
def baseStart_3783736 : Nat := 118140960795 + 3783736 * 2 ^ 59
def prefixEnd_3783736 : Nat := 4983230072969 + 3 ^ 40 * 3783736 * 2
def baseEnd_3783736 : Nat := 1942875237720513349198921

theorem tailTrace_3783736 : CollatzResearch.WordTrace tailWord_3783736 prefixEnd_3783736 1942875237720513349198921 := by
  unfold tailWord_3783736
  simp only [CollatzResearch.WordTrace]
  refine ⟨69002094710089078753225531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92002792946785438337634041 69002094710089078753225531)
  ·
    refine ⟨103503142065133618129838297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69002094710089078753225531 103503142065133618129838297)
    ·
      refine ⟨77627356548850213597378723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103503142065133618129838297 77627356548850213597378723)
      ·
        refine ⟨116441034823275320396068085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77627356548850213597378723 116441034823275320396068085)
        ·
          refine ⟨10916347014682061287131383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116441034823275320396068085 10916347014682061287131383)
          ·
            refine ⟨16374520522023091930697075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10916347014682061287131383 16374520522023091930697075)
            ·
              refine ⟨24561780783034637896045613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16374520522023091930697075 24561780783034637896045613)
              ·
                refine ⟨9210667793637989211017105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24561780783034637896045613 9210667793637989211017105)
                ·
                  refine ⟨6908000845228491908262829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9210667793637989211017105 6908000845228491908262829)
                  ·
                    refine ⟨2590500316960684465598561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6908000845228491908262829 2590500316960684465598561)
                    ·
                      refine ⟨1942875237720513349198921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2590500316960684465598561 1942875237720513349198921)
                      ·
                        rfl

theorem cell23_3783736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 2, 3, 2].length) (baseStart_3783736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783736 prefixEnd_3783736 := by exact prefixLift 3783736
  have htrace : WordTrace (prefixWord ++ tailWord_3783736) baseStart_3783736 baseEnd_3783736 := by
    simpa [prefixWord, tailWord_3783736, baseEnd_3783736] using wordTrace_append hprefix tailTrace_3783736
  have hstable : (prefixWord ++ tailWord_3783736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783736).length < 2 ^ (prefixWord ++ tailWord_3783736).sum := by decide
  have hdescent : baseEnd_3783736 < baseStart_3783736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783749 : List Nat := [1, 3, 1, 1, 1, 3, 2, 5, 1, 1, 4]
def baseStart_3783749 : Nat := 118140960795 + 3783749 * 2 ^ 59
def prefixEnd_3783749 : Nat := 4983230072969 + 3 ^ 40 * 3783749 * 2
def baseEnd_3783749 : Nat := 1942881912969021798336361

theorem tailTrace_3783749 : CollatzResearch.WordTrace tailWord_3783749 prefixEnd_3783749 1942881912969021798336361 := by
  unfold tailWord_3783749
  simp only [CollatzResearch.WordTrace]
  refine ⟨138004663569131060726674301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92003109046087373817782867 138004663569131060726674301)
  ·
    refine ⟨51751748838424147772502863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138004663569131060726674301 51751748838424147772502863)
    ·
      refine ⟨77627623257636221658754295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51751748838424147772502863 77627623257636221658754295)
      ·
        refine ⟨116441434886454332488131443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77627623257636221658754295 116441434886454332488131443)
        ·
          refine ⟨174662152329681498732197165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116441434886454332488131443 174662152329681498732197165)
          ·
            refine ⟨65498307123630562024573937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174662152329681498732197165 65498307123630562024573937)
            ·
              refine ⟨49123730342722921518430453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65498307123630562024573937 49123730342722921518430453)
              ·
                refine ⟨4605349719630273892352855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49123730342722921518430453 4605349719630273892352855)
                ·
                  refine ⟨6908024579445410838529283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4605349719630273892352855 6908024579445410838529283)
                  ·
                    refine ⟨10362036869168116257793925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6908024579445410838529283 10362036869168116257793925)
                    ·
                      refine ⟨1942881912969021798336361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10362036869168116257793925 1942881912969021798336361)
                      ·
                        rfl

theorem cell23_3783749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 1, 4].length) (baseStart_3783749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783749 prefixEnd_3783749 := by exact prefixLift 3783749
  have htrace : WordTrace (prefixWord ++ tailWord_3783749) baseStart_3783749 baseEnd_3783749 := by
    simpa [prefixWord, tailWord_3783749, baseEnd_3783749] using wordTrace_append hprefix tailTrace_3783749
  have hstable : (prefixWord ++ tailWord_3783749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783749).length < 2 ^ (prefixWord ++ tailWord_3783749).sum := by decide
  have hdescent : baseEnd_3783749 < baseStart_3783749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783783 : List Nat := [1, 1, 5, 1, 1, 4, 1, 2, 3, 2, 2]
def baseStart_3783783 : Nat := 118140960795 + 3783783 * 2 ^ 59
def prefixEnd_3783783 : Nat := 4983230072969 + 3 ^ 40 * 3783783 * 2
def baseEnd_3783783 : Nat := 1942899371311274665311205

theorem tailTrace_3783783 : CollatzResearch.WordTrace tailWord_3783783 prefixEnd_3783783 1942899371311274665311205 := by
  unfold tailWord_3783783
  simp only [CollatzResearch.WordTrace]
  refine ⟨138005903651007884533412003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92003935767338589688941335 138005903651007884533412003)
  ·
    refine ⟨207008855476511826800118005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138005903651007884533412003 207008855476511826800118005)
    ·
      refine ⟨19407080200922983762511063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 207008855476511826800118005 19407080200922983762511063)
      ·
        refine ⟨29110620301384475643766595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19407080200922983762511063 29110620301384475643766595)
        ·
          refine ⟨43665930452076713465649893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29110620301384475643766595 43665930452076713465649893)
          ·
            refine ⟨8187361959764383774809355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43665930452076713465649893 8187361959764383774809355)
            ·
              refine ⟨12281042939646575662214033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8187361959764383774809355 12281042939646575662214033)
              ·
                refine ⟨9210782204734931746660525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12281042939646575662214033 9210782204734931746660525)
                ·
                  refine ⟨3454043326775599404997697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9210782204734931746660525 3454043326775599404997697)
                  ·
                    refine ⟨2590532495081699553748273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3454043326775599404997697 2590532495081699553748273)
                    ·
                      refine ⟨1942899371311274665311205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2590532495081699553748273 1942899371311274665311205)
                      ·
                        rfl

theorem cell23_3783783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_3783783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783783 prefixEnd_3783783 := by exact prefixLift 3783783
  have htrace : WordTrace (prefixWord ++ tailWord_3783783) baseStart_3783783 baseEnd_3783783 := by
    simpa [prefixWord, tailWord_3783783, baseEnd_3783783] using wordTrace_append hprefix tailTrace_3783783
  have hstable : (prefixWord ++ tailWord_3783783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783783).length < 2 ^ (prefixWord ++ tailWord_3783783).sum := by decide
  have hdescent : baseEnd_3783783 < baseStart_3783783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783786 : List Nat := [3, 1, 3, 2, 2, 1, 2, 1, 3, 2, 3]
def baseStart_3783786 : Nat := 118140960795 + 3783786 * 2 ^ 59
def prefixEnd_3783786 : Nat := 4983230072969 + 3 ^ 40 * 3783786 * 2
def baseEnd_3783786 : Nat := 1942900911753238153573691

theorem tailTrace_3783786 : CollatzResearch.WordTrace tailWord_3783786 prefixEnd_3783786 1942900911753238153573691 := by
  unfold tailWord_3783786
  simp only [CollatzResearch.WordTrace]
  refine ⟨34501503267499254011442803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92004008713331344030514141 34501503267499254011442803)
  ·
    refine ⟨51752254901248881017164205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34501503267499254011442803 51752254901248881017164205)
    ·
      refine ⟨19407095587968330381436577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51752254901248881017164205 19407095587968330381436577)
      ·
        refine ⟨14555321690976247786077433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19407095587968330381436577 14555321690976247786077433)
        ·
          refine ⟨10916491268232185839558075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14555321690976247786077433 10916491268232185839558075)
          ·
            refine ⟨16374736902348278759337113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10916491268232185839558075 16374736902348278759337113)
            ·
              refine ⟨12281052676761209069502835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16374736902348278759337113 12281052676761209069502835)
              ·
                refine ⟨18421579015141813604254253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12281052676761209069502835 18421579015141813604254253)
                ·
                  refine ⟨6908092130678180101595345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18421579015141813604254253 6908092130678180101595345)
                  ·
                    refine ⟨5181069098008635076196509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6908092130678180101595345 5181069098008635076196509)
                    ·
                      refine ⟨1942900911753238153573691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5181069098008635076196509 1942900911753238153573691)
                      ·
                        rfl

theorem cell23_3783786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_3783786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783786 prefixEnd_3783786 := by exact prefixLift 3783786
  have htrace : WordTrace (prefixWord ++ tailWord_3783786) baseStart_3783786 baseEnd_3783786 := by
    simpa [prefixWord, tailWord_3783786, baseEnd_3783786] using wordTrace_append hprefix tailTrace_3783786
  have hstable : (prefixWord ++ tailWord_3783786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783786).length < 2 ^ (prefixWord ++ tailWord_3783786).sum := by decide
  have hdescent : baseEnd_3783786 < baseStart_3783786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783797 : List Nat := [1, 3, 4, 3, 2, 1, 2, 1, 1, 5]
def baseStart_3783797 : Nat := 118140960795 + 3783797 * 2 ^ 59
def prefixEnd_3783797 : Nat := 4983230072969 + 3 ^ 40 * 3783797 * 2
def baseEnd_3783797 : Nat := 647635520013479203512047

theorem tailTrace_3783797 : CollatzResearch.WordTrace tailWord_3783797 prefixEnd_3783797 647635520013479203512047 := by
  unfold tailWord_3783797
  simp only [CollatzResearch.WordTrace]
  refine ⟨138006414272957164924421645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92004276181971443282947763 138006414272957164924421645)
  ·
    refine ⟨51752405352358936846658117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138006414272957164924421645 51752405352358936846658117)
    ·
      refine ⟨9703576003567300658748397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51752405352358936846658117 9703576003567300658748397)
      ·
        refine ⟨3638841001337737747030649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9703576003567300658748397 3638841001337737747030649)
        ·
          refine ⟨2729130751003303310272987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3638841001337737747030649 2729130751003303310272987)
          ·
            refine ⟨4093696126504954965409481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2729130751003303310272987 4093696126504954965409481)
            ·
              refine ⟨3070272094878716224057111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4093696126504954965409481 3070272094878716224057111)
              ·
                refine ⟨4605408142318074336085667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3070272094878716224057111 4605408142318074336085667)
                ·
                  refine ⟨6908112213477111504128501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4605408142318074336085667 6908112213477111504128501)
                  ·
                    refine ⟨647635520013479203512047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6908112213477111504128501 647635520013479203512047)
                    ·
                      rfl

theorem cell23_3783797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_3783797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783797 prefixEnd_3783797 := by exact prefixLift 3783797
  have htrace : WordTrace (prefixWord ++ tailWord_3783797) baseStart_3783797 baseEnd_3783797 := by
    simpa [prefixWord, tailWord_3783797, baseEnd_3783797] using wordTrace_append hprefix tailTrace_3783797
  have hstable : (prefixWord ++ tailWord_3783797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783797).length < 2 ^ (prefixWord ++ tailWord_3783797).sum := by decide
  have hdescent : baseEnd_3783797 < baseStart_3783797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783799 : List Nat := [1, 1, 3, 1, 1, 4, 1, 4, 1, 3, 3]
def baseStart_3783799 : Nat := 118140960795 + 3783799 * 2 ^ 59
def prefixEnd_3783799 : Nat := 4983230072969 + 3 ^ 40 * 3783799 * 2
def baseEnd_3783799 : Nat := 1942907587001746602711131

theorem tailTrace_3783799 : CollatzResearch.WordTrace tailWord_3783799 prefixEnd_3783799 1942907587001746602711131 := by
  unfold tailWord_3783799
  simp only [CollatzResearch.WordTrace]
  refine ⟨138006487218949919265994451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92004324812633279510662967 138006487218949919265994451)
  ·
    refine ⟨207009730828424878898991677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138006487218949919265994451 207009730828424878898991677)
    ·
      refine ⟨77628649060659329587121879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207009730828424878898991677 77628649060659329587121879)
      ·
        refine ⟨116442973590988994380682819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77628649060659329587121879 116442973590988994380682819)
        ·
          refine ⟨174664460386483491571024229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116442973590988994380682819 174664460386483491571024229)
          ·
            refine ⟨32749586322465654669567043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174664460386483491571024229 32749586322465654669567043)
            ·
              refine ⟨49124379483698482004350565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32749586322465654669567043 49124379483698482004350565)
              ·
                refine ⟨9210821153193465375815731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49124379483698482004350565 9210821153193465375815731)
                ·
                  refine ⟨13816231729790198063723597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9210821153193465375815731 13816231729790198063723597)
                  ·
                    refine ⟨5181086898671324273896349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13816231729790198063723597 5181086898671324273896349)
                    ·
                      refine ⟨1942907587001746602711131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5181086898671324273896349 1942907587001746602711131)
                      ·
                        rfl

theorem cell23_3783799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 3, 3].length) (baseStart_3783799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783799 prefixEnd_3783799 := by exact prefixLift 3783799
  have htrace : WordTrace (prefixWord ++ tailWord_3783799) baseStart_3783799 baseEnd_3783799 := by
    simpa [prefixWord, tailWord_3783799, baseEnd_3783799] using wordTrace_append hprefix tailTrace_3783799
  have hstable : (prefixWord ++ tailWord_3783799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783799).length < 2 ^ (prefixWord ++ tailWord_3783799).sum := by decide
  have hdescent : baseEnd_3783799 < baseStart_3783799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783869 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 4, 2, 4]
def baseStart_3783869 : Nat := 118140960795 + 3783869 * 2 ^ 59
def prefixEnd_3783869 : Nat := 4983230072969 + 3 ^ 40 * 3783869 * 2
def baseEnd_3783869 : Nat := 1942943530647561328835809

theorem tailTrace_3783869 : CollatzResearch.WordTrace tailWord_3783869 prefixEnd_3783869 1942943530647561328835809 := by
  unfold tailWord_3783869
  simp only [CollatzResearch.WordTrace]
  refine ⟨138009040328696321221042661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92006026885797547480695107 138009040328696321221042661)
  ·
    refine ⟨25876695061630560228945499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138009040328696321221042661 25876695061630560228945499)
    ·
      refine ⟨38815042592445840343418249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25876695061630560228945499 38815042592445840343418249)
      ·
        refine ⟨29111281944334380257563687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38815042592445840343418249 29111281944334380257563687)
        ·
          refine ⟨43666922916501570386345531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29111281944334380257563687 43666922916501570386345531)
          ·
            refine ⟨65500384374752355579518297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43666922916501570386345531 65500384374752355579518297)
            ·
              refine ⟨49125288281064266684638723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65500384374752355579518297 49125288281064266684638723)
              ·
                refine ⟨73687932421596400026958085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49125288281064266684638723 73687932421596400026958085)
                ·
                  refine ⟨13816487329049325005054641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73687932421596400026958085 13816487329049325005054641)
                  ·
                    refine ⟨10362365496786993753790981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13816487329049325005054641 10362365496786993753790981)
                    ·
                      refine ⟨1942943530647561328835809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10362365496786993753790981 1942943530647561328835809)
                      ·
                        rfl

theorem cell23_3783869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_3783869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783869 prefixEnd_3783869 := by exact prefixLift 3783869
  have htrace : WordTrace (prefixWord ++ tailWord_3783869) baseStart_3783869 baseEnd_3783869 := by
    simpa [prefixWord, tailWord_3783869, baseEnd_3783869] using wordTrace_append hprefix tailTrace_3783869
  have hstable : (prefixWord ++ tailWord_3783869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783869).length < 2 ^ (prefixWord ++ tailWord_3783869).sum := by decide
  have hdescent : baseEnd_3783869 < baseStart_3783869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783889 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 1, 5, 3]
def baseStart_3783889 : Nat := 118140960795 + 3783889 * 2 ^ 59
def prefixEnd_3783889 : Nat := 4983230072969 + 3 ^ 40 * 3783889 * 2
def baseEnd_3783889 : Nat := 1942953800260651250585717

theorem tailTrace_3783889 : CollatzResearch.WordTrace tailWord_3783889 prefixEnd_3783889 1942953800260651250585717 := by
  unfold tailWord_3783889
  simp only [CollatzResearch.WordTrace]
  refine ⟨138009769788623864636770721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92006513192415909757847147 138009769788623864636770721)
  ·
    refine ⟨103507327341467898477578041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138009769788623864636770721 103507327341467898477578041)
    ·
      refine ⟨77630495506100923858183531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103507327341467898477578041 77630495506100923858183531)
      ·
        refine ⟨116445743259151385787275297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77630495506100923858183531 116445743259151385787275297)
        ·
          refine ⟨87334307444363539340456473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116445743259151385787275297 87334307444363539340456473)
          ·
            refine ⟨65500730583272654505342355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87334307444363539340456473 65500730583272654505342355)
            ·
              refine ⟨98251095874908981758013533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65500730583272654505342355 98251095874908981758013533)
              ·
                refine ⟨36844160953090868159255075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98251095874908981758013533 36844160953090868159255075)
                ·
                  refine ⟨55266241429636302238882613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36844160953090868159255075 55266241429636302238882613)
                  ·
                    refine ⟨5181210134028403334895245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55266241429636302238882613 5181210134028403334895245)
                    ·
                      refine ⟨1942953800260651250585717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5181210134028403334895245 1942953800260651250585717)
                      ·
                        rfl

theorem cell23_3783889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 5, 3].length) (baseStart_3783889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783889 prefixEnd_3783889 := by exact prefixLift 3783889
  have htrace : WordTrace (prefixWord ++ tailWord_3783889) baseStart_3783889 baseEnd_3783889 := by
    simpa [prefixWord, tailWord_3783889, baseEnd_3783889] using wordTrace_append hprefix tailTrace_3783889
  have hstable : (prefixWord ++ tailWord_3783889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783889).length < 2 ^ (prefixWord ++ tailWord_3783889).sum := by decide
  have hdescent : baseEnd_3783889 < baseStart_3783889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783890 : List Nat := [3, 2, 2, 2, 1, 1, 3, 3, 2, 2, 2]
def baseStart_3783890 : Nat := 118140960795 + 3783890 * 2 ^ 59
def prefixEnd_3783890 : Nat := 4983230072969 + 3 ^ 40 * 3783890 * 2
def baseEnd_3783890 : Nat := 1942954313741305746673213

theorem tailTrace_3783890 : CollatzResearch.WordTrace tailWord_3783890 prefixEnd_3783890 1942954313741305746673213 := by
  unfold tailWord_3783890
  simp only [CollatzResearch.WordTrace]
  refine ⟨34502451565405060451889281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92006537507746827871704749 34502451565405060451889281)
  ·
    refine ⟨25876838674053795338916961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34502451565405060451889281 25876838674053795338916961)
    ·
      refine ⟨19407629005540346504187721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25876838674053795338916961 19407629005540346504187721)
      ·
        refine ⟨14555721754155259878140791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19407629005540346504187721 14555721754155259878140791)
        ·
          refine ⟨21833582631232889817211187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14555721754155259878140791 21833582631232889817211187)
          ·
            refine ⟨32750373946849334725816781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21833582631232889817211187 32750373946849334725816781)
            ·
              refine ⟨12281390230068500522181293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32750373946849334725816781 12281390230068500522181293)
              ·
                refine ⟨4605521336275687695817985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12281390230068500522181293 4605521336275687695817985)
                ·
                  refine ⟨3454141002206765771863489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4605521336275687695817985 3454141002206765771863489)
                  ·
                    refine ⟨2590605751655074328897617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3454141002206765771863489 2590605751655074328897617)
                    ·
                      refine ⟨1942954313741305746673213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2590605751655074328897617 1942954313741305746673213)
                      ·
                        rfl

theorem cell23_3783890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_3783890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783890 prefixEnd_3783890 := by exact prefixLift 3783890
  have htrace : WordTrace (prefixWord ++ tailWord_3783890) baseStart_3783890 baseEnd_3783890 := by
    simpa [prefixWord, tailWord_3783890, baseEnd_3783890] using wordTrace_append hprefix tailTrace_3783890
  have hstable : (prefixWord ++ tailWord_3783890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783890).length < 2 ^ (prefixWord ++ tailWord_3783890).sum := by decide
  have hdescent : baseEnd_3783890 < baseStart_3783890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783894 : List Nat := [5, 2, 1, 2, 2, 2, 1, 2, 1, 3, 2]
def baseStart_3783894 : Nat := 118140960795 + 3783894 * 2 ^ 59
def prefixEnd_3783894 : Nat := 4983230072969 + 3 ^ 40 * 3783894 * 2
def baseEnd_3783894 : Nat := 1942956367663923731023195

theorem tailTrace_3783894 : CollatzResearch.WordTrace tailWord_3783894 prefixEnd_3783894 1942956367663923731023195 := by
  unfold tailWord_3783894
  simp only [CollatzResearch.WordTrace]
  refine ⟨8625622009600359405668921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92006634769070500327135157 8625622009600359405668921)
  ·
    refine ⟨6469216507200269554251691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8625622009600359405668921 6469216507200269554251691)
    ·
      refine ⟨9703824760800404331377537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6469216507200269554251691 9703824760800404331377537)
      ·
        refine ⟨7277868570600303248533153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9703824760800404331377537 7277868570600303248533153)
        ·
          refine ⟨5458401427950227436399865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7277868570600303248533153 5458401427950227436399865)
          ·
            refine ⟨4093801070962670577299899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5458401427950227436399865 4093801070962670577299899)
            ·
              refine ⟨6140701606444005865949849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4093801070962670577299899 6140701606444005865949849)
              ·
                refine ⟨4605526204833004399462387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6140701606444005865949849 4605526204833004399462387)
                ·
                  refine ⟨6908289307249506599193581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4605526204833004399462387 6908289307249506599193581)
                  ·
                    refine ⟨2590608490218564974697593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6908289307249506599193581 2590608490218564974697593)
                    ·
                      refine ⟨1942956367663923731023195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2590608490218564974697593 1942956367663923731023195)
                      ·
                        rfl

theorem cell23_3783894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_3783894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783894 prefixEnd_3783894 := by exact prefixLift 3783894
  have htrace : WordTrace (prefixWord ++ tailWord_3783894) baseStart_3783894 baseEnd_3783894 := by
    simpa [prefixWord, tailWord_3783894, baseEnd_3783894] using wordTrace_append hprefix tailTrace_3783894
  have hstable : (prefixWord ++ tailWord_3783894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783894).length < 2 ^ (prefixWord ++ tailWord_3783894).sum := by decide
  have hdescent : baseEnd_3783894 < baseStart_3783894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783969 : List Nat := [1, 2, 3, 2, 1, 1, 1, 4, 8]
def baseStart_3783969 : Nat := 118140960795 + 3783969 * 2 ^ 59
def prefixEnd_3783969 : Nat := 4983230072969 + 3 ^ 40 * 3783969 * 2
def baseEnd_3783969 : Nat := 215888319857001215287261

theorem tailTrace_3783969 : CollatzResearch.WordTrace tailWord_3783969 prefixEnd_3783969 215888319857001215287261 := by
  unfold tailWord_3783969
  simp only [CollatzResearch.WordTrace]
  refine ⟨138012687628334038299682961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92008458418889358866455307 138012687628334038299682961)
  ·
    refine ⟨103509515721250528724762221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138012687628334038299682961 103509515721250528724762221)
    ·
      refine ⟨38816068395468948271785833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103509515721250528724762221 38816068395468948271785833)
      ·
        refine ⟨29112051296601711203839375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38816068395468948271785833 29112051296601711203839375)
        ·
          refine ⟨43668076944902566805759063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29112051296601711203839375 43668076944902566805759063)
          ·
            refine ⟨65502115417353850208638595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43668076944902566805759063 65502115417353850208638595)
            ·
              refine ⟨98253173126030775312957893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65502115417353850208638595 98253173126030775312957893)
              ·
                refine ⟨18422469961130770371179605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98253173126030775312957893 18422469961130770371179605)
                ·
                  refine ⟨215888319857001215287261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18422469961130770371179605 215888319857001215287261)
                  ·
                    rfl

theorem cell23_3783969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 8].length) (baseStart_3783969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783969 prefixEnd_3783969 := by exact prefixLift 3783969
  have htrace : WordTrace (prefixWord ++ tailWord_3783969) baseStart_3783969 baseEnd_3783969 := by
    simpa [prefixWord, tailWord_3783969, baseEnd_3783969] using wordTrace_append hprefix tailTrace_3783969
  have hstable : (prefixWord ++ tailWord_3783969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783969).length < 2 ^ (prefixWord ++ tailWord_3783969).sum := by decide
  have hdescent : baseEnd_3783969 < baseStart_3783969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783976 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_3783976 : Nat := 118140960795 + 3783976 * 2 ^ 59
def prefixEnd_3783976 : Nat := 4983230072969 + 3 ^ 40 * 3783976 * 2
def baseEnd_3783976 : Nat := 1942998473077592410197817

theorem tailTrace_3783976 : CollatzResearch.WordTrace tailWord_3783976 prefixEnd_3783976 1942998473077592410197817 := by
  unfold tailWord_3783976
  simp only [CollatzResearch.WordTrace]
  refine ⟨69006471469654339247593891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92008628626205785663458521 69006471469654339247593891)
  ·
    refine ⟨103509707204481508871390837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69006471469654339247593891 103509707204481508871390837)
    ·
      refine ⟨9704035050420141456692891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103509707204481508871390837 9704035050420141456692891)
      ·
        refine ⟨14556052575630212185039337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9704035050420141456692891 14556052575630212185039337)
        ·
          refine ⟨10917039431722659138779503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14556052575630212185039337 10917039431722659138779503)
          ·
            refine ⟨16375559147583988708169255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10917039431722659138779503 16375559147583988708169255)
            ·
              refine ⟨24563338721375983062253883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16375559147583988708169255 24563338721375983062253883)
              ·
                refine ⟨36845008082063974593380825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24563338721375983062253883 36845008082063974593380825)
                ·
                  refine ⟨27633756061547980945035619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36845008082063974593380825 27633756061547980945035619)
                  ·
                    refine ⟨41450634092321971417553429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27633756061547980945035619 41450634092321971417553429)
                    ·
                      refine ⟨1942998473077592410197817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41450634092321971417553429 1942998473077592410197817)
                      ·
                        rfl

theorem cell23_3783976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_3783976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783976 prefixEnd_3783976 := by exact prefixLift 3783976
  have htrace : WordTrace (prefixWord ++ tailWord_3783976) baseStart_3783976 baseEnd_3783976 := by
    simpa [prefixWord, tailWord_3783976, baseEnd_3783976] using wordTrace_append hprefix tailTrace_3783976
  have hstable : (prefixWord ++ tailWord_3783976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783976).length < 2 ^ (prefixWord ++ tailWord_3783976).sum := by decide
  have hdescent : baseEnd_3783976 < baseStart_3783976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783986 : List Nat := [3, 2, 1, 1, 4, 2, 1, 1, 8]
def baseStart_3783986 : Nat := 118140960795 + 3783986 * 2 ^ 59
def prefixEnd_3783986 : Nat := 4983230072969 + 3 ^ 40 * 3783986 * 2
def baseEnd_3783986 : Nat := 215889289764904152341419

theorem tailTrace_3783986 : CollatzResearch.WordTrace tailWord_3783986 prefixEnd_3783986 215889289764904152341419 := by
  unfold tailWord_3783986
  simp only [CollatzResearch.WordTrace]
  refine ⟨34503326917318112550762953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92008871779514966802034541 34503326917318112550762953)
  ·
    refine ⟨25877495187988584413072215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34503326917318112550762953 25877495187988584413072215)
    ·
      refine ⟨38816242781982876619608323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25877495187988584413072215 38816242781982876619608323)
      ·
        refine ⟨58224364172974314929412485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38816242781982876619608323 58224364172974314929412485)
        ·
          refine ⟨10917068282432684049264841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58224364172974314929412485 10917068282432684049264841)
          ·
            refine ⟨8187801211824513036948631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10917068282432684049264841 8187801211824513036948631)
            ·
              refine ⟨12281701817736769555422947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8187801211824513036948631 12281701817736769555422947)
              ·
                refine ⟨18422552726605154333134421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12281701817736769555422947 18422552726605154333134421)
                ·
                  refine ⟨215889289764904152341419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18422552726605154333134421 215889289764904152341419)
                  ·
                    rfl

theorem cell23_3783986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 8].length) (baseStart_3783986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3783986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3783986 prefixEnd_3783986 := by exact prefixLift 3783986
  have htrace : WordTrace (prefixWord ++ tailWord_3783986) baseStart_3783986 baseEnd_3783986 := by
    simpa [prefixWord, tailWord_3783986, baseEnd_3783986] using wordTrace_append hprefix tailTrace_3783986
  have hstable : (prefixWord ++ tailWord_3783986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783986).length < 2 ^ (prefixWord ++ tailWord_3783986).sum := by decide
  have hdescent : baseEnd_3783986 < baseStart_3783986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784009 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 2, 1, 7]
def baseStart_3784009 : Nat := 118140960795 + 3784009 * 2 ^ 59
def prefixEnd_3784009 : Nat := 4983230072969 + 3 ^ 40 * 3784009 * 2
def baseEnd_3784009 : Nat := 1943015417939190781085165

theorem tailTrace_3784009 : CollatzResearch.WordTrace tailWord_3784009 prefixEnd_3784009 1943015417939190781085165 := by
  unfold tailWord_3784009
  simp only [CollatzResearch.WordTrace]
  refine ⟨138014146548189125131139081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92009431032126083420759387 138014146548189125131139081)
  ·
    refine ⟨103510609911141843848354311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138014146548189125131139081 103510609911141843848354311)
    ·
      refine ⟨155265914866712765772531467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103510609911141843848354311 155265914866712765772531467)
      ·
        refine ⟨232898872300069148658797201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155265914866712765772531467 232898872300069148658797201)
        ·
          refine ⟨174674154225051861494097901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232898872300069148658797201 174674154225051861494097901)
          ·
            refine ⟨65502807834394448060286713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174674154225051861494097901 65502807834394448060286713)
            ·
              refine ⟨49127105875795836045215035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65502807834394448060286713 49127105875795836045215035)
              ·
                refine ⟨73690658813693754067822553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49127105875795836045215035 73690658813693754067822553)
                ·
                  refine ⟨55267994110270315550866915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73690658813693754067822553 55267994110270315550866915)
                  ·
                    refine ⟨82901991165405473326300373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55267994110270315550866915 82901991165405473326300373)
                    ·
                      refine ⟨1943015417939190781085165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 82901991165405473326300373 1943015417939190781085165)
                      ·
                        rfl

theorem cell23_3784009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 1, 7].length) (baseStart_3784009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784009 prefixEnd_3784009 := by exact prefixLift 3784009
  have htrace : WordTrace (prefixWord ++ tailWord_3784009) baseStart_3784009 baseEnd_3784009 := by
    simpa [prefixWord, tailWord_3784009, baseEnd_3784009] using wordTrace_append hprefix tailTrace_3784009
  have hstable : (prefixWord ++ tailWord_3784009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784009).length < 2 ^ (prefixWord ++ tailWord_3784009).sum := by decide
  have hdescent : baseEnd_3784009 < baseStart_3784009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784023 : List Nat := [1, 1, 3, 2, 3, 2, 2, 1, 1, 5, 2]
def baseStart_3784023 : Nat := 118140960795 + 3784023 * 2 ^ 59
def prefixEnd_3784023 : Nat := 4983230072969 + 3 ^ 40 * 3784023 * 2
def baseEnd_3784023 : Nat := 1943022606668353726310101

theorem tailTrace_3784023 : CollatzResearch.WordTrace tailWord_3784023 prefixEnd_3784023 1943022606668353726310101 := by
  unfold tailWord_3784023
  simp only [CollatzResearch.WordTrace]
  refine ⟨138014657170138405522148723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92009771446758937014765815 138014657170138405522148723)
  ·
    refine ⟨207021985755207608283223085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138014657170138405522148723 207021985755207608283223085)
    ·
      refine ⟨77633244658202853106208657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207021985755207608283223085 77633244658202853106208657)
      ·
        refine ⟨58224933493652139829656493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77633244658202853106208657 58224933493652139829656493)
        ·
          refine ⟨21834350060119552436121185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58224933493652139829656493 21834350060119552436121185)
          ·
            refine ⟨16375762545089664327090889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21834350060119552436121185 16375762545089664327090889)
            ·
              refine ⟨12281821908817248245318167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16375762545089664327090889 12281821908817248245318167)
              ·
                refine ⟨18422732863225872367977251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12281821908817248245318167 18422732863225872367977251)
                ·
                  refine ⟨27634099294838808551965877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18422732863225872367977251 27634099294838808551965877)
                  ·
                    refine ⟨2590696808891138301746801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27634099294838808551965877 2590696808891138301746801)
                    ·
                      refine ⟨1943022606668353726310101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2590696808891138301746801 1943022606668353726310101)
                      ·
                        rfl

theorem cell23_3784023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 5, 2].length) (baseStart_3784023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784023 prefixEnd_3784023 := by exact prefixLift 3784023
  have htrace : WordTrace (prefixWord ++ tailWord_3784023) baseStart_3784023 baseEnd_3784023 := by
    simpa [prefixWord, tailWord_3784023, baseEnd_3784023] using wordTrace_append hprefix tailTrace_3784023
  have hstable : (prefixWord ++ tailWord_3784023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784023).length < 2 ^ (prefixWord ++ tailWord_3784023).sum := by decide
  have hdescent : baseEnd_3784023 < baseStart_3784023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784047 : List Nat := [1, 1, 2, 1, 3, 1, 7, 2, 1, 1, 3]
def baseStart_3784047 : Nat := 118140960795 + 3784047 * 2 ^ 59
def prefixEnd_3784047 : Nat := 4983230072969 + 3 ^ 40 * 3784047 * 2
def baseEnd_3784047 : Nat := 1943034930204061632409991

theorem tailTrace_3784047 : CollatzResearch.WordTrace tailWord_3784047 prefixEnd_3784047 1943034930204061632409991 := by
  unfold tailWord_3784047
  simp only [CollatzResearch.WordTrace]
  refine ⟨138015532522051457621022395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92010355014700971747348263 138015532522051457621022395)
  ·
    refine ⟨207023298783077186431533593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138015532522051457621022395 207023298783077186431533593)
    ·
      refine ⟨155267474087307889823650195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207023298783077186431533593 155267474087307889823650195)
      ·
        refine ⟨232901211130961834735475293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155267474087307889823650195 232901211130961834735475293)
        ·
          refine ⟨87337954174110688025803235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232901211130961834735475293 87337954174110688025803235)
          ·
            refine ⟨131006931261166032038704853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87337954174110688025803235 131006931261166032038704853)
            ·
              refine ⟨3070474951433578875907145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 131006931261166032038704853 3070474951433578875907145)
              ·
                refine ⟨2302856213575184156930359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3070474951433578875907145 2302856213575184156930359)
                ·
                  refine ⟨3454284320362776235395539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2302856213575184156930359 3454284320362776235395539)
                  ·
                    refine ⟨5181426480544164353093309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3454284320362776235395539 5181426480544164353093309)
                    ·
                      refine ⟨1943034930204061632409991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5181426480544164353093309 1943034930204061632409991)
                      ·
                        rfl

theorem cell23_3784047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 2, 1, 1, 3].length) (baseStart_3784047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784047 prefixEnd_3784047 := by exact prefixLift 3784047
  have htrace : WordTrace (prefixWord ++ tailWord_3784047) baseStart_3784047 baseEnd_3784047 := by
    simpa [prefixWord, tailWord_3784047, baseEnd_3784047] using wordTrace_append hprefix tailTrace_3784047
  have hstable : (prefixWord ++ tailWord_3784047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784047).length < 2 ^ (prefixWord ++ tailWord_3784047).sum := by decide
  have hdescent : baseEnd_3784047 < baseStart_3784047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784087 : List Nat := [1, 1, 3, 3, 1, 1, 1, 7, 1, 2, 2]
def baseStart_3784087 : Nat := 118140960795 + 3784087 * 2 ^ 59
def prefixEnd_3784087 : Nat := 4983230072969 + 3 ^ 40 * 3784087 * 2
def baseEnd_3784087 : Nat := 1943055469430241475909807

theorem tailTrace_3784087 : CollatzResearch.WordTrace tailWord_3784087 prefixEnd_3784087 1943055469430241475909807 := by
  unfold tailWord_3784087
  simp only [CollatzResearch.WordTrace]
  refine ⟨138016991441906544452478515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92011327627937696301652343 138016991441906544452478515)
  ·
    refine ⟨207025487162859816678717773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138016991441906544452478515 207025487162859816678717773)
    ·
      refine ⟨77634557686072431254519165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207025487162859816678717773 77634557686072431254519165)
      ·
        refine ⟨29112959132277161720444687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77634557686072431254519165 29112959132277161720444687)
        ·
          refine ⟨43669438698415742580667031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29112959132277161720444687 43669438698415742580667031)
          ·
            refine ⟨65504158047623613871000547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43669438698415742580667031 65504158047623613871000547)
            ·
              refine ⟨98256237071435420806500821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65504158047623613871000547 98256237071435420806500821)
              ·
                refine ⟨2302880556361767675152363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 98256237071435420806500821 2302880556361767675152363)
                ·
                  refine ⟨3454320834542651512728545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2302880556361767675152363 3454320834542651512728545)
                  ·
                    refine ⟨2590740625906988634546409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3454320834542651512728545 2590740625906988634546409)
                    ·
                      refine ⟨1943055469430241475909807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2590740625906988634546409 1943055469430241475909807)
                      ·
                        rfl

theorem cell23_3784087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_3784087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784087 prefixEnd_3784087 := by exact prefixLift 3784087
  have htrace : WordTrace (prefixWord ++ tailWord_3784087) baseStart_3784087 baseEnd_3784087 := by
    simpa [prefixWord, tailWord_3784087, baseEnd_3784087] using wordTrace_append hprefix tailTrace_3784087
  have hstable : (prefixWord ++ tailWord_3784087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784087).length < 2 ^ (prefixWord ++ tailWord_3784087).sum := by decide
  have hdescent : baseEnd_3784087 < baseStart_3784087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784103 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 3, 3, 3]
def baseStart_3784103 : Nat := 118140960795 + 3784103 * 2 ^ 59
def prefixEnd_3784103 : Nat := 4983230072969 + 3 ^ 40 * 3784103 * 2
def baseEnd_3784103 : Nat := 1943063685120713413309733

theorem tailTrace_3784103 : CollatzResearch.WordTrace tailWord_3784103 prefixEnd_3784103 1943063685120713413309733 := by
  unfold tailWord_3784103
  simp only [CollatzResearch.WordTrace]
  refine ⟨138017575009848579185060963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92011716673232386123373975 138017575009848579185060963)
  ·
    refine ⟨207026362514772868777591445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138017575009848579185060963 207026362514772868777591445)
    ·
      refine ⟨9704360742879978223949599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 207026362514772868777591445 9704360742879978223949599)
      ·
        refine ⟨14556541114319967335924399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9704360742879978223949599 14556541114319967335924399)
        ·
          refine ⟨21834811671479951003886599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14556541114319967335924399 21834811671479951003886599)
          ·
            refine ⟨32752217507219926505829899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21834811671479951003886599 32752217507219926505829899)
            ·
              refine ⟨49128326260829889758744849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32752217507219926505829899 49128326260829889758744849)
              ·
                refine ⟨36846244695622417319058637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49128326260829889758744849 36846244695622417319058637)
                ·
                  refine ⟨13817341760858406494646989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36846244695622417319058637 13817341760858406494646989)
                  ·
                    refine ⟨5181503160321902435492621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13817341760858406494646989 5181503160321902435492621)
                    ·
                      refine ⟨1943063685120713413309733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5181503160321902435492621 1943063685120713413309733)
                      ·
                        rfl

theorem cell23_3784103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_3784103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784103 prefixEnd_3784103 := by exact prefixLift 3784103
  have htrace : WordTrace (prefixWord ++ tailWord_3784103) baseStart_3784103 baseEnd_3784103 := by
    simpa [prefixWord, tailWord_3784103, baseEnd_3784103] using wordTrace_append hprefix tailTrace_3784103
  have hstable : (prefixWord ++ tailWord_3784103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784103).length < 2 ^ (prefixWord ++ tailWord_3784103).sum := by decide
  have hdescent : baseEnd_3784103 < baseStart_3784103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784120 : List Nat := [2, 1, 2, 1, 2, 2, 4, 3, 2, 1, 3]
def baseStart_3784120 : Nat := 118140960795 + 3784120 * 2 ^ 59
def prefixEnd_3784120 : Nat := 4983230072969 + 3 ^ 40 * 3784120 * 2
def baseEnd_3784120 : Nat := 1943072414291839846797155

theorem tailTrace_3784120 : CollatzResearch.WordTrace tailWord_3784120 prefixEnd_3784120 1943072414291839846797155 := by
  unfold tailWord_3784120
  simp only [CollatzResearch.WordTrace]
  refine ⟨69009097525393495544214907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92012130033857994058953209 69009097525393495544214907)
  ·
    refine ⟨103513646288090243316322361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69009097525393495544214907 103513646288090243316322361)
    ·
      refine ⟨77635234716067682487241771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103513646288090243316322361 77635234716067682487241771)
      ·
        refine ⟨116452852074101523730862657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77635234716067682487241771 116452852074101523730862657)
        ·
          refine ⟨87339639055576142798146993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116452852074101523730862657 87339639055576142798146993)
          ·
            refine ⟨65504729291682107098610245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87339639055576142798146993 65504729291682107098610245)
            ·
              refine ⟨12282136742190395080989421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65504729291682107098610245 12282136742190395080989421)
              ·
                refine ⟨4605801278321398155371033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12282136742190395080989421 4605801278321398155371033)
                ·
                  refine ⟨3454350958741048616528275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4605801278321398155371033 3454350958741048616528275)
                  ·
                    refine ⟨5181526438111572924792413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3454350958741048616528275 5181526438111572924792413)
                    ·
                      refine ⟨1943072414291839846797155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5181526438111572924792413 1943072414291839846797155)
                      ·
                        rfl

theorem cell23_3784120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 2, 1, 3].length) (baseStart_3784120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784120 prefixEnd_3784120 := by exact prefixLift 3784120
  have htrace : WordTrace (prefixWord ++ tailWord_3784120) baseStart_3784120 baseEnd_3784120 := by
    simpa [prefixWord, tailWord_3784120, baseEnd_3784120] using wordTrace_append hprefix tailTrace_3784120
  have hstable : (prefixWord ++ tailWord_3784120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784120).length < 2 ^ (prefixWord ++ tailWord_3784120).sum := by decide
  have hdescent : baseEnd_3784120 < baseStart_3784120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784136 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 1, 8]
def baseStart_3784136 : Nat := 118140960795 + 3784136 * 2 ^ 59
def prefixEnd_3784136 : Nat := 4983230072969 + 3 ^ 40 * 3784136 * 2
def baseEnd_3784136 : Nat := 647693543327437261399027

theorem tailTrace_3784136 : CollatzResearch.WordTrace tailWord_3784136 prefixEnd_3784136 647693543327437261399027 := by
  unfold tailWord_3784136
  simp only [CollatzResearch.WordTrace]
  refine ⟨69009389309364512910506131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92012519079152683880674841 69009389309364512910506131)
  ·
    refine ⟨103514083964046769365759197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69009389309364512910506131 103514083964046769365759197)
    ·
      refine ⟨38817781486517538512159699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103514083964046769365759197 38817781486517538512159699)
      ·
        refine ⟨58226672229776307768239549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38817781486517538512159699 58226672229776307768239549)
        ·
          refine ⟨21835002086166115413089831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58226672229776307768239549 21835002086166115413089831)
          ·
            refine ⟨32752503129249173119634747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21835002086166115413089831 32752503129249173119634747)
            ·
              refine ⟨49128754693873759679452121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32752503129249173119634747 49128754693873759679452121)
              ·
                refine ⟨36846566020405319759589091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49128754693873759679452121 36846566020405319759589091)
                ·
                  refine ⟨55269849030607979639383637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36846566020405319759589091 55269849030607979639383637)
                  ·
                    refine ⟨647693543327437261399027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55269849030607979639383637 647693543327437261399027)
                    ·
                      rfl

theorem cell23_3784136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_3784136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784136 prefixEnd_3784136 := by exact prefixLift 3784136
  have htrace : WordTrace (prefixWord ++ tailWord_3784136) baseStart_3784136 baseEnd_3784136 := by
    simpa [prefixWord, tailWord_3784136, baseEnd_3784136] using wordTrace_append hprefix tailTrace_3784136
  have hstable : (prefixWord ++ tailWord_3784136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784136).length < 2 ^ (prefixWord ++ tailWord_3784136).sum := by decide
  have hdescent : baseEnd_3784136 < baseStart_3784136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784177 : List Nat := [1, 2, 2, 2, 3, 4, 1, 1, 1, 4, 2]
def baseStart_3784177 : Nat := 118140960795 + 3784177 * 2 ^ 59
def prefixEnd_3784177 : Nat := 4983230072969 + 3 ^ 40 * 3784177 * 2
def baseEnd_3784177 : Nat := 1943101682689146123784393

theorem tailTrace_3784177 : CollatzResearch.WordTrace tailWord_3784177 prefixEnd_3784177 1943101682689146123784393 := by
  unfold tailWord_3784177
  simp only [CollatzResearch.WordTrace]
  refine ⟨138020274011580489823254785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92013516007720326548836523 138020274011580489823254785)
  ·
    refine ⟨103515205508685367367441089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138020274011580489823254785 103515205508685367367441089)
    ·
      refine ⟨77636404131514025525580817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103515205508685367367441089 77636404131514025525580817)
      ·
        refine ⟨58227303098635519144185613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77636404131514025525580817 58227303098635519144185613)
        ·
          refine ⟨21835238661988319679069605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58227303098635519144185613 21835238661988319679069605)
          ·
            refine ⟨4094107249122809939825551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21835238661988319679069605 4094107249122809939825551)
            ·
              refine ⟨6141160873684214909738327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4094107249122809939825551 6141160873684214909738327)
              ·
                refine ⟨9211741310526322364607491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6141160873684214909738327 9211741310526322364607491)
                ·
                  refine ⟨13817611965789483546911237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9211741310526322364607491 13817611965789483546911237)
                  ·
                    refine ⟨2590802243585528165045857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13817611965789483546911237 2590802243585528165045857)
                    ·
                      refine ⟨1943101682689146123784393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2590802243585528165045857 1943101682689146123784393)
                      ·
                        rfl

theorem cell23_3784177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 4, 2].length) (baseStart_3784177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784177 prefixEnd_3784177 := by exact prefixLift 3784177
  have htrace : WordTrace (prefixWord ++ tailWord_3784177) baseStart_3784177 baseEnd_3784177 := by
    simpa [prefixWord, tailWord_3784177, baseEnd_3784177] using wordTrace_append hprefix tailTrace_3784177
  have hstable : (prefixWord ++ tailWord_3784177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784177).length < 2 ^ (prefixWord ++ tailWord_3784177).sum := by decide
  have hdescent : baseEnd_3784177 < baseStart_3784177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784194 : List Nat := [3, 4, 1, 2, 1, 1, 1, 2, 4, 2, 2]
def baseStart_3784194 : Nat := 118140960795 + 3784194 * 2 ^ 59
def prefixEnd_3784194 : Nat := 4983230072969 + 3 ^ 40 * 3784194 * 2
def baseEnd_3784194 : Nat := 1943110411860272557271815

theorem tailTrace_3784194 : CollatzResearch.WordTrace tailWord_3784194 prefixEnd_3784194 1943110411860272557271815 := by
  unfold tailWord_3784194
  simp only [CollatzResearch.WordTrace]
  refine ⟨34505223513129725431655909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92013929368345934484415757 34505223513129725431655909)
  ·
    refine ⟨6469729408711823518435483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34505223513129725431655909 6469729408711823518435483)
    ·
      refine ⟨9704594113067735277653225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6469729408711823518435483 9704594113067735277653225)
      ·
        refine ⟨7278445584800801458239919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9704594113067735277653225 7278445584800801458239919)
        ·
          refine ⟨10917668377201202187359879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7278445584800801458239919 10917668377201202187359879)
          ·
            refine ⟨16376502565801803281039819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10917668377201202187359879 16376502565801803281039819)
            ·
              refine ⟨24564753848702704921559729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16376502565801803281039819 24564753848702704921559729)
              ·
                refine ⟨18423565386527028691169797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24564753848702704921559729 18423565386527028691169797)
                ·
                  refine ⟨3454418509973817879594337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18423565386527028691169797 3454418509973817879594337)
                  ·
                    refine ⟨2590813882480363409695753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3454418509973817879594337 2590813882480363409695753)
                    ·
                      refine ⟨1943110411860272557271815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2590813882480363409695753 1943110411860272557271815)
                      ·
                        rfl

theorem cell23_3784194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_3784194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784194 prefixEnd_3784194 := by exact prefixLift 3784194
  have htrace : WordTrace (prefixWord ++ tailWord_3784194) baseStart_3784194 baseEnd_3784194 := by
    simpa [prefixWord, tailWord_3784194, baseEnd_3784194] using wordTrace_append hprefix tailTrace_3784194
  have hstable : (prefixWord ++ tailWord_3784194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784194).length < 2 ^ (prefixWord ++ tailWord_3784194).sum := by decide
  have hdescent : baseEnd_3784194 < baseStart_3784194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784200 : List Nat := [2, 1, 3, 2, 1, 1, 5, 3, 5]
def baseStart_3784200 : Nat := 118140960795 + 3784200 * 2 ^ 59
def prefixEnd_3784200 : Nat := 4983230072969 + 3 ^ 40 * 3784200 * 2
def baseEnd_3784200 : Nat := 215901499193799948199643

theorem tailTrace_3784200 : CollatzResearch.WordTrace tailWord_3784200 prefixEnd_3784200 215901499193799948199643 := by
  unfold tailWord_3784200
  simp only [CollatzResearch.WordTrace]
  refine ⟨69010556445248582375671027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92014075260331443167561369 69010556445248582375671027)
  ·
    refine ⟨103515834667872873563506541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69010556445248582375671027 103515834667872873563506541)
    ·
      refine ⟨38818438000452327586314953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103515834667872873563506541 38818438000452327586314953)
      ·
        refine ⟨29113828500339245689736215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38818438000452327586314953 29113828500339245689736215)
        ·
          refine ⟨43670742750508868534604323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29113828500339245689736215 43670742750508868534604323)
          ·
            refine ⟨65506114125763302801906485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43670742750508868534604323 65506114125763302801906485)
            ·
              refine ⟨6141198199290309637678733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65506114125763302801906485 6141198199290309637678733)
              ·
                refine ⟨2302949324733866114129525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6141198199290309637678733 2302949324733866114129525)
                ·
                  refine ⟨215901499193799948199643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2302949324733866114129525 215901499193799948199643)
                  ·
                    rfl

theorem cell23_3784200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 3, 5].length) (baseStart_3784200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784200 prefixEnd_3784200 := by exact prefixLift 3784200
  have htrace : WordTrace (prefixWord ++ tailWord_3784200) baseStart_3784200 baseEnd_3784200 := by
    simpa [prefixWord, tailWord_3784200, baseEnd_3784200] using wordTrace_append hprefix tailTrace_3784200
  have hstable : (prefixWord ++ tailWord_3784200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784200).length < 2 ^ (prefixWord ++ tailWord_3784200).sum := by decide
  have hdescent : baseEnd_3784200 < baseStart_3784200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784213 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 4, 5]
def baseStart_3784213 : Nat := 118140960795 + 3784213 * 2 ^ 59
def prefixEnd_3784213 : Nat := 4983230072969 + 3 ^ 40 * 3784213 * 2
def baseEnd_3784213 : Nat := 647706722664235994311409

theorem tailTrace_3784213 : CollatzResearch.WordTrace tailWord_3784213 prefixEnd_3784213 647706722664235994311409 := by
  unfold tailWord_3784213
  simp only [CollatzResearch.WordTrace]
  refine ⟨138021587039450067971565293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92014391359633378647710195 138021587039450067971565293)
  ·
    refine ⟨51758095139793775489336985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138021587039450067971565293 51758095139793775489336985)
    ·
      refine ⟨38818571354845331617002739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51758095139793775489336985 38818571354845331617002739)
      ·
        refine ⟨58227857032267997425504109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38818571354845331617002739 58227857032267997425504109)
        ·
          refine ⟨21835446387100499034564041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58227857032267997425504109 21835446387100499034564041)
          ·
            refine ⟨16376584790325374275923031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21835446387100499034564041 16376584790325374275923031)
            ·
              refine ⟨24564877185488061413884547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16376584790325374275923031 24564877185488061413884547)
              ·
                refine ⟨36847315778232092120826821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24564877185488061413884547 36847315778232092120826821)
                ·
                  refine ⟨6908871708418517272655029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36847315778232092120826821 6908871708418517272655029)
                  ·
                    refine ⟨647706722664235994311409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6908871708418517272655029 647706722664235994311409)
                    ·
                      rfl

theorem cell23_3784213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_3784213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784213 prefixEnd_3784213 := by exact prefixLift 3784213
  have htrace : WordTrace (prefixWord ++ tailWord_3784213) baseStart_3784213 baseEnd_3784213 := by
    simpa [prefixWord, tailWord_3784213, baseEnd_3784213] using wordTrace_append hprefix tailTrace_3784213
  have hstable : (prefixWord ++ tailWord_3784213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784213).length < 2 ^ (prefixWord ++ tailWord_3784213).sum := by decide
  have hdescent : baseEnd_3784213 < baseStart_3784213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784220 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 2, 5, 2]
def baseStart_3784220 : Nat := 118140960795 + 3784220 * 2 ^ 59
def prefixEnd_3784220 : Nat := 4983230072969 + 3 ^ 40 * 3784220 * 2
def baseEnd_3784220 : Nat := 1943123762357289455546695

theorem tailTrace_3784220 : CollatzResearch.WordTrace tailWord_3784220 prefixEnd_3784220 1943123762357289455546695 := by
  unfold tailWord_3784220
  simp only [CollatzResearch.WordTrace]
  refine ⟨69010921175212354083535057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92014561566949805444713409 69010921175212354083535057)
  ·
    refine ⟨51758190881409265562651293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69010921175212354083535057 51758190881409265562651293)
    ·
      refine ⟨19409321580528474585994235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51758190881409265562651293 19409321580528474585994235)
      ·
        refine ⟨29113982370792711878991353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19409321580528474585994235 29113982370792711878991353)
        ·
          refine ⟨21835486778094533909243515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29113982370792711878991353 21835486778094533909243515)
          ·
            refine ⟨32753230167141800863865273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21835486778094533909243515 32753230167141800863865273)
            ·
              refine ⟨24564922625356350647898955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32753230167141800863865273 24564922625356350647898955)
              ·
                refine ⟨36847383938034525971848433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24564922625356350647898955 36847383938034525971848433)
                ·
                  refine ⟨27635537953525894478886325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36847383938034525971848433 27635537953525894478886325)
                  ·
                    refine ⟨2590831683143052607395593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27635537953525894478886325 2590831683143052607395593)
                    ·
                      refine ⟨1943123762357289455546695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2590831683143052607395593 1943123762357289455546695)
                      ·
                        rfl

theorem cell23_3784220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_3784220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784220 prefixEnd_3784220 := by exact prefixLift 3784220
  have htrace : WordTrace (prefixWord ++ tailWord_3784220) baseStart_3784220 baseEnd_3784220 := by
    simpa [prefixWord, tailWord_3784220, baseEnd_3784220] using wordTrace_append hprefix tailTrace_3784220
  have hstable : (prefixWord ++ tailWord_3784220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784220).length < 2 ^ (prefixWord ++ tailWord_3784220).sum := by decide
  have hdescent : baseEnd_3784220 < baseStart_3784220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784222 : List Nat := [4, 3, 3, 1, 2, 1, 2, 1, 2, 1, 3]
def baseStart_3784222 : Nat := 118140960795 + 3784222 * 2 ^ 59
def prefixEnd_3784222 : Nat := 4983230072969 + 3 ^ 40 * 3784222 * 2
def baseEnd_3784222 : Nat := 1943124789318598447721687

theorem tailTrace_3784222 : CollatzResearch.WordTrace tailWord_3784222 prefixEnd_3784222 1943124789318598447721687 := by
  unfold tailWord_3784222
  simp only [CollatzResearch.WordTrace]
  refine ⟨17252739412052182813580365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92014610197611641672428613 17252739412052182813580365)
  ·
    refine ⟨6469777279519568555092637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17252739412052182813580365 6469777279519568555092637)
    ·
      refine ⟨2426166479819838208159739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6469777279519568555092637 2426166479819838208159739)
      ·
        refine ⟨3639249719729757312239609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2426166479819838208159739 3639249719729757312239609)
        ·
          refine ⟨2729437289797317984179707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3639249719729757312239609 2729437289797317984179707)
          ·
            refine ⟨4094155934695976976269561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2729437289797317984179707 4094155934695976976269561)
            ·
              refine ⟨3070616951021982732202171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4094155934695976976269561 3070616951021982732202171)
              ·
                refine ⟨4605925426532974098303257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3070616951021982732202171 4605925426532974098303257)
                ·
                  refine ⟨3454444069899730573727443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4605925426532974098303257 3454444069899730573727443)
                  ·
                    refine ⟨5181666104849595860591165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3454444069899730573727443 5181666104849595860591165)
                    ·
                      refine ⟨1943124789318598447721687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5181666104849595860591165 1943124789318598447721687)
                      ·
                        rfl

theorem cell23_3784222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_3784222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784222 prefixEnd_3784222 := by exact prefixLift 3784222
  have htrace : WordTrace (prefixWord ++ tailWord_3784222) baseStart_3784222 baseEnd_3784222 := by
    simpa [prefixWord, tailWord_3784222, baseEnd_3784222] using wordTrace_append hprefix tailTrace_3784222
  have hstable : (prefixWord ++ tailWord_3784222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784222).length < 2 ^ (prefixWord ++ tailWord_3784222).sum := by decide
  have hdescent : baseEnd_3784222 < baseStart_3784222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784250 : List Nat := [3, 1, 1, 1, 3, 2, 4, 1, 2, 1, 4]
def baseStart_3784250 : Nat := 118140960795 + 3784250 * 2 ^ 59
def prefixEnd_3784250 : Nat := 4983230072969 + 3 ^ 40 * 3784250 * 2
def baseEnd_3784250 : Nat := 1943139166776924338171557

theorem tailTrace_3784250 : CollatzResearch.WordTrace tailWord_3784250 prefixEnd_3784250 1943139166776924338171557 := by
  unfold tailWord_3784250
  simp only [CollatzResearch.WordTrace]
  refine ⟨34505734135079005822665551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92015291026877348860441469 34505734135079005822665551)
  ·
    refine ⟨51758601202618508733998327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34505734135079005822665551 51758601202618508733998327)
    ·
      refine ⟨77637901803927763100997491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51758601202618508733998327 77637901803927763100997491)
      ·
        refine ⟨116456852705891644651496237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77637901803927763100997491 116456852705891644651496237)
        ·
          refine ⟨43671319764709366744311089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116456852705891644651496237 43671319764709366744311089)
          ·
            refine ⟨32753489823532025058233317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43671319764709366744311089 32753489823532025058233317)
            ·
              refine ⟨6141279341912254698418747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32753489823532025058233317 6141279341912254698418747)
              ·
                refine ⟨9211919012868382047628121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6141279341912254698418747 9211919012868382047628121)
                ·
                  refine ⟨6908939259651286535721091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9211919012868382047628121 6908939259651286535721091)
                  ·
                    refine ⟨10363408889476929803581637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6908939259651286535721091 10363408889476929803581637)
                    ·
                      refine ⟨1943139166776924338171557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10363408889476929803581637 1943139166776924338171557)
                      ·
                        rfl

theorem cell23_3784250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 2, 1, 4].length) (baseStart_3784250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784250 prefixEnd_3784250 := by exact prefixLift 3784250
  have htrace : WordTrace (prefixWord ++ tailWord_3784250) baseStart_3784250 baseEnd_3784250 := by
    simpa [prefixWord, tailWord_3784250, baseEnd_3784250] using wordTrace_append hprefix tailTrace_3784250
  have hstable : (prefixWord ++ tailWord_3784250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784250).length < 2 ^ (prefixWord ++ tailWord_3784250).sum := by decide
  have hdescent : baseEnd_3784250 < baseStart_3784250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784320 : List Nat := [2, 1, 1, 2, 1, 4, 3, 3, 1, 5]
def baseStart_3784320 : Nat := 118140960795 + 3784320 * 2 ^ 59
def prefixEnd_3784320 : Nat := 4983230072969 + 3 ^ 40 * 3784320 * 2
def baseEnd_3784320 : Nat := 647725036807579688098745

theorem tailTrace_3784320 : CollatzResearch.WordTrace tailWord_3784320 prefixEnd_3784320 647725036807579688098745 := by
  unfold tailWord_3784320
  simp only [CollatzResearch.WordTrace]
  refine ⟨69012744825031212622855207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92016993100041616830473609 69012744825031212622855207)
  ·
    refine ⟨103519117237546818934282811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69012744825031212622855207 103519117237546818934282811)
    ·
      refine ⟨155278675856320228401424217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103519117237546818934282811 155278675856320228401424217)
      ·
        refine ⟨116459006892240171301068163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155278675856320228401424217 116459006892240171301068163)
        ·
          refine ⟨174688510338360256951602245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116459006892240171301068163 174688510338360256951602245)
          ·
            refine ⟨32754095688442548178425421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174688510338360256951602245 32754095688442548178425421)
            ·
              refine ⟨12282785883165955566909533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32754095688442548178425421 12282785883165955566909533)
              ·
                refine ⟨4606044706187233337591075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12282785883165955566909533 4606044706187233337591075)
                ·
                  refine ⟨6909067059280850006386613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4606044706187233337591075 6909067059280850006386613)
                  ·
                    refine ⟨647725036807579688098745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6909067059280850006386613 647725036807579688098745)
                    ·
                      rfl

theorem cell23_3784320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 1, 5].length) (baseStart_3784320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784320 prefixEnd_3784320 := by exact prefixLift 3784320
  have htrace : WordTrace (prefixWord ++ tailWord_3784320) baseStart_3784320 baseEnd_3784320 := by
    simpa [prefixWord, tailWord_3784320, baseEnd_3784320] using wordTrace_append hprefix tailTrace_3784320
  have hstable : (prefixWord ++ tailWord_3784320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784320).length < 2 ^ (prefixWord ++ tailWord_3784320).sum := by decide
  have hdescent : baseEnd_3784320 < baseStart_3784320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784324 : List Nat := [2, 3, 2, 1, 5, 1, 1, 2, 6]
def baseStart_3784324 : Nat := 118140960795 + 3784324 * 2 ^ 59
def prefixEnd_3784324 : Nat := 4983230072969 + 3 ^ 40 * 3784324 * 2
def baseEnd_3784324 : Nat := 215908573816150783182913

theorem tailTrace_3784324 : CollatzResearch.WordTrace tailWord_3784324 prefixEnd_3784324 215908573816150783182913 := by
  unfold tailWord_3784324
  simp only [CollatzResearch.WordTrace]
  refine ⟨69012817771023966964428013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92017090361365289285904017 69012817771023966964428013)
  ·
    refine ⟨25879806664133987611660505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69012817771023966964428013 25879806664133987611660505)
    ·
      refine ⟨19409854998100490708745379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25879806664133987611660505 19409854998100490708745379)
      ·
        refine ⟨29114782497150736063118069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19409854998100490708745379 29114782497150736063118069)
        ·
          refine ⟨2729510859107881505917319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29114782497150736063118069 2729510859107881505917319)
          ·
            refine ⟨4094266288661822258875979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2729510859107881505917319 4094266288661822258875979)
            ·
              refine ⟨6141399432992733388313969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4094266288661822258875979 6141399432992733388313969)
              ·
                refine ⟨4606049574744550041235477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6141399432992733388313969 4606049574744550041235477)
                ·
                  refine ⟨215908573816150783182913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4606049574744550041235477 215908573816150783182913)
                  ·
                    rfl

theorem cell23_3784324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 6].length) (baseStart_3784324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784324 prefixEnd_3784324 := by exact prefixLift 3784324
  have htrace : WordTrace (prefixWord ++ tailWord_3784324) baseStart_3784324 baseEnd_3784324 := by
    simpa [prefixWord, tailWord_3784324, baseEnd_3784324] using wordTrace_append hprefix tailTrace_3784324
  have hstable : (prefixWord ++ tailWord_3784324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784324).length < 2 ^ (prefixWord ++ tailWord_3784324).sum := by decide
  have hdescent : baseEnd_3784324 < baseStart_3784324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784334 : List Nat := [4, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3]
def baseStart_3784334 : Nat := 118140960795 + 3784334 * 2 ^ 59
def prefixEnd_3784334 : Nat := 4983230072969 + 3 ^ 40 * 3784334 * 2
def baseEnd_3784334 : Nat := 1943182299151902009521171

theorem tailTrace_3784334 : CollatzResearch.WordTrace tailWord_3784334 prefixEnd_3784334 1943182299151902009521171 := by
  unfold tailWord_3784334
  simp only [CollatzResearch.WordTrace]
  refine ⟨17253250034001463204590007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92017333514674470424480037 17253250034001463204590007)
  ·
    refine ⟨25879875051002194806885011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17253250034001463204590007 25879875051002194806885011)
    ·
      refine ⟨38819812576503292210327517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25879875051002194806885011 38819812576503292210327517)
      ·
        refine ⟨14557429716188734578872819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38819812576503292210327517 14557429716188734578872819)
        ·
          refine ⟨21836144574283101868309229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14557429716188734578872819 21836144574283101868309229)
          ·
            refine ⟨8188554215356163200615961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21836144574283101868309229 8188554215356163200615961)
            ·
              refine ⟨6141415661517122400461971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8188554215356163200615961 6141415661517122400461971)
              ·
                refine ⟨9212123492275683600692957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6141415661517122400461971 9212123492275683600692957)
                ·
                  refine ⟨3454546309603381350259859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9212123492275683600692957 3454546309603381350259859)
                  ·
                    refine ⟨5181819464405072025389789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3454546309603381350259859 5181819464405072025389789)
                    ·
                      refine ⟨1943182299151902009521171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5181819464405072025389789 1943182299151902009521171)
                      ·
                        rfl

theorem cell23_3784334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_3784334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784334 prefixEnd_3784334 := by exact prefixLift 3784334
  have htrace : WordTrace (prefixWord ++ tailWord_3784334) baseStart_3784334 baseEnd_3784334 := by
    simpa [prefixWord, tailWord_3784334, baseEnd_3784334] using wordTrace_append hprefix tailTrace_3784334
  have hstable : (prefixWord ++ tailWord_3784334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784334).length < 2 ^ (prefixWord ++ tailWord_3784334).sum := by decide
  have hdescent : baseEnd_3784334 < baseStart_3784334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784370 : List Nat := [3, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4]
def baseStart_3784370 : Nat := 118140960795 + 3784370 * 2 ^ 59
def prefixEnd_3784370 : Nat := 4983230072969 + 3 ^ 40 * 3784370 * 2
def baseEnd_3784370 : Nat := 1943200784455463868671005

theorem tailTrace_3784370 : CollatzResearch.WordTrace tailWord_3784370 prefixEnd_3784370 1943200784455463868671005 := by
  unfold tailWord_3784370
  simp only [CollatzResearch.WordTrace]
  refine ⟨34506828324970320946257641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92018208866587522523353709 34506828324970320946257641)
  ·
    refine ⟨25880121243727740709693231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34506828324970320946257641 25880121243727740709693231)
    ·
      refine ⟨38820181865591611064539847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25880121243727740709693231 38820181865591611064539847)
      ·
        refine ⟨58230272798387416596809771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38820181865591611064539847 58230272798387416596809771)
        ·
          refine ⟨87345409197581124895214657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58230272798387416596809771 87345409197581124895214657)
          ·
            refine ⟨65509056898185843671410993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87345409197581124895214657 65509056898185843671410993)
            ·
              refine ⟨49131792673639382753558245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65509056898185843671410993 49131792673639382753558245)
              ·
                refine ⟨9212211126307384266292171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49131792673639382753558245 9212211126307384266292171)
                ·
                  refine ⟨13818316689461076399438257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9212211126307384266292171 13818316689461076399438257)
                  ·
                    refine ⟨10363737517095807299578693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13818316689461076399438257 10363737517095807299578693)
                    ·
                      refine ⟨1943200784455463868671005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10363737517095807299578693 1943200784455463868671005)
                      ·
                        rfl

theorem cell23_3784370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_3784370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784370 prefixEnd_3784370 := by exact prefixLift 3784370
  have htrace : WordTrace (prefixWord ++ tailWord_3784370) baseStart_3784370 baseEnd_3784370 := by
    simpa [prefixWord, tailWord_3784370, baseEnd_3784370] using wordTrace_append hprefix tailTrace_3784370
  have hstable : (prefixWord ++ tailWord_3784370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784370).length < 2 ^ (prefixWord ++ tailWord_3784370).sum := by decide
  have hdescent : baseEnd_3784370 < baseStart_3784370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784377 : List Nat := [1, 2, 1, 4, 1, 1, 4, 3, 1, 2, 3]
def baseStart_3784377 : Nat := 118140960795 + 3784377 * 2 ^ 59
def prefixEnd_3784377 : Nat := 4983230072969 + 3 ^ 40 * 3784377 * 2
def baseEnd_3784377 : Nat := 1943204378820045341283473

theorem tailTrace_3784377 : CollatzResearch.WordTrace tailWord_3784377 prefixEnd_3784377 1943204378820045341283473 := by
  unfold tailWord_3784377
  simp only [CollatzResearch.WordTrace]
  refine ⟨138027568610855923980535385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92018379073903949320356923 138027568610855923980535385)
  ·
    refine ⟨103520676458141942985401539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138027568610855923980535385 103520676458141942985401539)
    ·
      refine ⟨155281014687212914478102309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103520676458141942985401539 155281014687212914478102309)
      ·
        refine ⟨29115190253852421464644183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155281014687212914478102309 29115190253852421464644183)
        ·
          refine ⟨43672785380778632196966275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29115190253852421464644183 43672785380778632196966275)
          ·
            refine ⟨65509178071167948295449413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43672785380778632196966275 65509178071167948295449413)
            ·
              refine ⟨12282970888343990305396765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65509178071167948295449413 12282970888343990305396765)
              ·
                refine ⟨4606114083128996364523787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12282970888343990305396765 4606114083128996364523787)
                ·
                  refine ⟨6909171124693494546785681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4606114083128996364523787 6909171124693494546785681)
                  ·
                    refine ⟨5181878343520120910089261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6909171124693494546785681 5181878343520120910089261)
                    ·
                      refine ⟨1943204378820045341283473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5181878343520120910089261 1943204378820045341283473)
                      ·
                        rfl

theorem cell23_3784377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_3784377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784377 prefixEnd_3784377 := by exact prefixLift 3784377
  have htrace : WordTrace (prefixWord ++ tailWord_3784377) baseStart_3784377 baseEnd_3784377 := by
    simpa [prefixWord, tailWord_3784377, baseEnd_3784377] using wordTrace_append hprefix tailTrace_3784377
  have hstable : (prefixWord ++ tailWord_3784377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784377).length < 2 ^ (prefixWord ++ tailWord_3784377).sum := by decide
  have hdescent : baseEnd_3784377 < baseStart_3784377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784380 : List Nat := [2, 2, 2, 3, 1, 4, 9]
def baseStart_3784380 : Nat := 118140960795 + 3784380 * 2 ^ 59
def prefixEnd_3784380 : Nat := 4983230072969 + 3 ^ 40 * 3784380 * 2
def baseEnd_3784380 : Nat := 23990196534098874438839

theorem tailTrace_3784380 : CollatzResearch.WordTrace tailWord_3784380 prefixEnd_3784380 23990196534098874438839 := by
  unfold tailWord_3784380
  simp only [CollatzResearch.WordTrace]
  refine ⟨69013839014922527746447297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92018452019896703661929729 69013839014922527746447297)
  ·
    refine ⟨51760379261191895809835473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69013839014922527746447297 51760379261191895809835473)
    ·
      refine ⟨38820284445893921857376605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51760379261191895809835473 38820284445893921857376605)
      ·
        refine ⟨14557606667210220696516227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38820284445893921857376605 14557606667210220696516227)
        ·
          refine ⟨21836410000815331044774341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14557606667210220696516227 21836410000815331044774341)
          ·
            refine ⟨4094326875152874570895189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21836410000815331044774341 4094326875152874570895189)
            ·
              refine ⟨23990196534098874438839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4094326875152874570895189 23990196534098874438839)
              ·
                rfl

theorem cell23_3784380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 9].length) (baseStart_3784380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784380 prefixEnd_3784380 := by exact prefixLift 3784380
  have htrace : WordTrace (prefixWord ++ tailWord_3784380) baseStart_3784380 baseEnd_3784380 := by
    simpa [prefixWord, tailWord_3784380, baseEnd_3784380] using wordTrace_append hprefix tailTrace_3784380
  have hstable : (prefixWord ++ tailWord_3784380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784380).length < 2 ^ (prefixWord ++ tailWord_3784380).sum := by decide
  have hdescent : baseEnd_3784380 < baseStart_3784380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784397 : List Nat := [1, 6, 2, 1, 1, 1, 1, 10]
def baseStart_3784397 : Nat := 118140960795 + 3784397 * 2 ^ 59
def prefixEnd_3784397 : Nat := 4983230072969 + 3 ^ 40 * 3784397 * 2
def baseEnd_3784397 : Nat := 71970912904930935667903

theorem tailTrace_3784397 : CollatzResearch.WordTrace tailWord_3784397 prefixEnd_3784397 71970912904930935667903 := by
  unfold tailWord_3784397
  simp only [CollatzResearch.WordTrace]
  refine ⟨138028298070783467396263445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92018865380522311597508963 138028298070783467396263445)
  ·
    refine ⟨6470076472067975034199849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 138028298070783467396263445 6470076472067975034199849)
    ·
      refine ⟨4852557354050981275649887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6470076472067975034199849 4852557354050981275649887)
      ·
        refine ⟨7278836031076471913474831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4852557354050981275649887 7278836031076471913474831)
        ·
          refine ⟨10918254046614707870212247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7278836031076471913474831 10918254046614707870212247)
          ·
            refine ⟨16377381069922061805318371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10918254046614707870212247 16377381069922061805318371)
            ·
              refine ⟨24566071604883092707977557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16377381069922061805318371 24566071604883092707977557)
              ·
                refine ⟨71970912904930935667903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 24566071604883092707977557 71970912904930935667903)
                ·
                  rfl

theorem cell23_3784397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 10].length) (baseStart_3784397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784397 prefixEnd_3784397 := by exact prefixLift 3784397
  have htrace : WordTrace (prefixWord ++ tailWord_3784397) baseStart_3784397 baseEnd_3784397 := by
    simpa [prefixWord, tailWord_3784397, baseEnd_3784397] using wordTrace_append hprefix tailTrace_3784397
  have hstable : (prefixWord ++ tailWord_3784397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784397).length < 2 ^ (prefixWord ++ tailWord_3784397).sum := by decide
  have hdescent : baseEnd_3784397 < baseStart_3784397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784460 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 1, 4, 4]
def baseStart_3784460 : Nat := 118140960795 + 3784460 * 2 ^ 59
def prefixEnd_3784460 : Nat := 4983230072969 + 3 ^ 40 * 3784460 * 2
def baseEnd_3784460 : Nat := 1943246997714368516545591

theorem tailTrace_3784460 : CollatzResearch.WordTrace tailWord_3784460 prefixEnd_3784460 1943246997714368516545591 := by
  unfold tailWord_3784460
  simp only [CollatzResearch.WordTrace]
  refine ⟨69015297934777614577903417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92020397246370152770537889 69015297934777614577903417)
  ·
    refine ⟨51761473451083210933427563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69015297934777614577903417 51761473451083210933427563)
    ·
      refine ⟨77642210176624816400141345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51761473451083210933427563 77642210176624816400141345)
      ·
        refine ⟨58231657632468612300106009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77642210176624816400141345 58231657632468612300106009)
        ·
          refine ⟨43673743224351459225079507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58231657632468612300106009 43673743224351459225079507)
          ·
            refine ⟨65510614836527188837619261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43673743224351459225079507 65510614836527188837619261)
            ·
              refine ⟨24566480563697695814107223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65510614836527188837619261 24566480563697695814107223)
              ·
                refine ⟨36849720845546543721160835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24566480563697695814107223 36849720845546543721160835)
                ·
                  refine ⟨55274581268319815581741253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36849720845546543721160835 55274581268319815581741253)
                  ·
                    refine ⟨10363983987809965421576485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55274581268319815581741253 10363983987809965421576485)
                    ·
                      refine ⟨1943246997714368516545591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10363983987809965421576485 1943246997714368516545591)
                      ·
                        rfl

theorem cell23_3784460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_3784460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784460 prefixEnd_3784460 := by exact prefixLift 3784460
  have htrace : WordTrace (prefixWord ++ tailWord_3784460) baseStart_3784460 baseEnd_3784460 := by
    simpa [prefixWord, tailWord_3784460, baseEnd_3784460] using wordTrace_append hprefix tailTrace_3784460
  have hstable : (prefixWord ++ tailWord_3784460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784460).length < 2 ^ (prefixWord ++ tailWord_3784460).sum := by decide
  have hdescent : baseEnd_3784460 < baseStart_3784460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784497 : List Nat := [1, 2, 2, 3, 2, 2, 1, 2, 2, 3, 3]
def baseStart_3784497 : Nat := 118140960795 + 3784497 * 2 ^ 59
def prefixEnd_3784497 : Nat := 4983230072969 + 3 ^ 40 * 3784497 * 2
def baseEnd_3784497 : Nat := 1943265996498584871782921

theorem tailTrace_3784497 : CollatzResearch.WordTrace tailWord_3784497 prefixEnd_3784497 1943265996498584871782921 := by
  unfold tailWord_3784497
  simp only [CollatzResearch.WordTrace]
  refine ⟨138031945370421184474903745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92021296913614122983269163 138031945370421184474903745)
  ·
    refine ⟨103523959027815888356177809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138031945370421184474903745 103523959027815888356177809)
    ·
      refine ⟨77642969270861916267133357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103523959027815888356177809 77642969270861916267133357)
      ·
        refine ⟨29116113476573218600175009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77642969270861916267133357 29116113476573218600175009)
        ·
          refine ⟨21837085107429913950131257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29116113476573218600175009 21837085107429913950131257)
          ·
            refine ⟨16377813830572435462598443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21837085107429913950131257 16377813830572435462598443)
            ·
              refine ⟨24566720745858653193897665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16377813830572435462598443 24566720745858653193897665)
              ·
                refine ⟨18425040559393989895423249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24566720745858653193897665 18425040559393989895423249)
                ·
                  refine ⟨13818780419545492421567437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18425040559393989895423249 13818780419545492421567437)
                  ·
                    refine ⟨5182042657329559658087789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13818780419545492421567437 5182042657329559658087789)
                    ·
                      refine ⟨1943265996498584871782921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5182042657329559658087789 1943265996498584871782921)
                      ·
                        rfl

theorem cell23_3784497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_3784497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784497 prefixEnd_3784497 := by exact prefixLift 3784497
  have htrace : WordTrace (prefixWord ++ tailWord_3784497) baseStart_3784497 baseEnd_3784497 := by
    simpa [prefixWord, tailWord_3784497, baseEnd_3784497] using wordTrace_append hprefix tailTrace_3784497
  have hstable : (prefixWord ++ tailWord_3784497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784497).length < 2 ^ (prefixWord ++ tailWord_3784497).sum := by decide
  have hdescent : baseEnd_3784497 < baseStart_3784497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784498 : List Nat := [3, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2]
def baseStart_3784498 : Nat := 118140960795 + 3784498 * 2 ^ 59
def prefixEnd_3784498 : Nat := 4983230072969 + 3 ^ 40 * 3784498 * 2
def baseEnd_3784498 : Nat := 1943266509979239367870417

theorem tailTrace_3784498 : CollatzResearch.WordTrace tailWord_3784498 prefixEnd_3784498 1943266509979239367870417 := by
  unfold tailWord_3784498
  simp only [CollatzResearch.WordTrace]
  refine ⟨34507995460854390411422537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92021321228945041097126765 34507995460854390411422537)
  ·
    refine ⟨25880996595640792808566903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34507995460854390411422537 25880996595640792808566903)
    ·
      refine ⟨38821494893461189212850355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25880996595640792808566903 38821494893461189212850355)
      ·
        refine ⟨58232242340191783819275533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38821494893461189212850355 58232242340191783819275533)
        ·
          refine ⟨21837090877571918932228325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58232242340191783819275533 21837090877571918932228325)
          ·
            refine ⟨4094454539544734799792811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21837090877571918932228325 4094454539544734799792811)
            ·
              refine ⟨6141681809317102199689217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4094454539544734799792811 6141681809317102199689217)
              ·
                refine ⟨4606261356987826649766913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6141681809317102199689217 4606261356987826649766913)
                ·
                  refine ⟨3454696017740869987325185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4606261356987826649766913 3454696017740869987325185)
                  ·
                    refine ⟨2591022013305652490493889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3454696017740869987325185 2591022013305652490493889)
                    ·
                      refine ⟨1943266509979239367870417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2591022013305652490493889 1943266509979239367870417)
                      ·
                        rfl

theorem cell23_3784498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2].length) (baseStart_3784498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784498 prefixEnd_3784498 := by exact prefixLift 3784498
  have htrace : WordTrace (prefixWord ++ tailWord_3784498) baseStart_3784498 baseEnd_3784498 := by
    simpa [prefixWord, tailWord_3784498, baseEnd_3784498] using wordTrace_append hprefix tailTrace_3784498
  have hstable : (prefixWord ++ tailWord_3784498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784498).length < 2 ^ (prefixWord ++ tailWord_3784498).sum := by decide
  have hdescent : baseEnd_3784498 < baseStart_3784498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784537 : List Nat := [1, 2, 1, 2, 2, 3, 2, 3, 2, 1, 4]
def baseStart_3784537 : Nat := 118140960795 + 3784537 * 2 ^ 59
def prefixEnd_3784537 : Nat := 4983230072969 + 3 ^ 40 * 3784537 * 2
def baseEnd_3784537 : Nat := 1943286535724764715282737

theorem tailTrace_3784537 : CollatzResearch.WordTrace tailWord_3784537 prefixEnd_3784537 1943286535724764715282737 := by
  unfold tailWord_3784537
  simp only [CollatzResearch.WordTrace]
  refine ⟨138033404290276271306359865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92022269526850847537573243 138033404290276271306359865)
  ·
    refine ⟨103525053217707203479769899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138033404290276271306359865 103525053217707203479769899)
    ·
      refine ⟨155287579826560805219654849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103525053217707203479769899 155287579826560805219654849)
      ·
        refine ⟨116465684869920603914741137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155287579826560805219654849 116465684869920603914741137)
        ·
          refine ⟨87349263652440452936055853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116465684869920603914741137 87349263652440452936055853)
          ·
            refine ⟨32755973869665169851020945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87349263652440452936055853 32755973869665169851020945)
            ·
              refine ⟨24566980402248877388265709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32755973869665169851020945 24566980402248877388265709)
              ·
                refine ⟨9212617650843329020599641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24566980402248877388265709 9212617650843329020599641)
                ·
                  refine ⟨6909463238132496765449731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9212617650843329020599641 6909463238132496765449731)
                  ·
                    refine ⟨10364194857198745148174597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6909463238132496765449731 10364194857198745148174597)
                    ·
                      refine ⟨1943286535724764715282737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10364194857198745148174597 1943286535724764715282737)
                      ·
                        rfl

theorem cell23_3784537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_3784537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784537 prefixEnd_3784537 := by exact prefixLift 3784537
  have htrace : WordTrace (prefixWord ++ tailWord_3784537) baseStart_3784537 baseEnd_3784537 := by
    simpa [prefixWord, tailWord_3784537, baseEnd_3784537] using wordTrace_append hprefix tailTrace_3784537
  have hstable : (prefixWord ++ tailWord_3784537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784537).length < 2 ^ (prefixWord ++ tailWord_3784537).sum := by decide
  have hdescent : baseEnd_3784537 < baseStart_3784537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784615 : List Nat := [1, 1, 6, 1, 2, 3, 2, 2, 1, 4]
def baseStart_3784615 : Nat := 118140960795 + 3784615 * 2 ^ 59
def prefixEnd_3784615 : Nat := 4983230072969 + 3 ^ 40 * 3784615 * 2
def baseEnd_3784615 : Nat := 647775529071938470035793

theorem tailTrace_3784615 : CollatzResearch.WordTrace tailWord_3784615 prefixEnd_3784615 647775529071938470035793 := by
  unfold tailWord_3784615
  simp only [CollatzResearch.WordTrace]
  refine ⟨138036249183993690627699299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92024166122662460418466199 138036249183993690627699299)
  ·
    refine ⟨207054373775990535941548949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138036249183993690627699299 207054373775990535941548949)
    ·
      refine ⟨9705673770749556372260107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 207054373775990535941548949 9705673770749556372260107)
      ·
        refine ⟨14558510656124334558390161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9705673770749556372260107 14558510656124334558390161)
        ·
          refine ⟨10918882992093250918792621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14558510656124334558390161 10918882992093250918792621)
          ·
            refine ⟨4094581122034969094547233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10918882992093250918792621 4094581122034969094547233)
            ·
              refine ⟨3070935841526226820910425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4094581122034969094547233 3070935841526226820910425)
              ·
                refine ⟨2303201881144670115682819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3070935841526226820910425 2303201881144670115682819)
                ·
                  refine ⟨3454802821717005173524229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2303201881144670115682819 3454802821717005173524229)
                  ·
                    refine ⟨647775529071938470035793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3454802821717005173524229 647775529071938470035793)
                    ·
                      rfl

theorem cell23_3784615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_3784615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784615 prefixEnd_3784615 := by exact prefixLift 3784615
  have htrace : WordTrace (prefixWord ++ tailWord_3784615) baseStart_3784615 baseEnd_3784615 := by
    simpa [prefixWord, tailWord_3784615, baseEnd_3784615] using wordTrace_append hprefix tailTrace_3784615
  have hstable : (prefixWord ++ tailWord_3784615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784615).length < 2 ^ (prefixWord ++ tailWord_3784615).sum := by decide
  have hdescent : baseEnd_3784615 < baseStart_3784615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784627 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 4]
def baseStart_3784627 : Nat := 118140960795 + 3784627 * 2 ^ 59
def prefixEnd_3784627 : Nat := 4983230072969 + 3 ^ 40 * 3784627 * 2
def baseEnd_3784627 : Nat := 1943332748983669363157323

theorem tailTrace_3784627 : CollatzResearch.WordTrace tailWord_3784627 prefixEnd_3784627 1943332748983669363157323 := by
  unfold tailWord_3784627
  simp only [CollatzResearch.WordTrace]
  refine ⟨138036686859950216677136135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92024457906633477784757423 138036686859950216677136135)
  ·
    refine ⟨207055030289925325015704203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138036686859950216677136135 207055030289925325015704203)
    ·
      refine ⟨310582545434887987523556305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207055030289925325015704203 310582545434887987523556305)
      ·
        refine ⟨232936909076165990642667229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310582545434887987523556305 232936909076165990642667229)
        ·
          refine ⟨87351340903562246491000211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232936909076165990642667229 87351340903562246491000211)
          ·
            refine ⟨131027011355343369736500317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87351340903562246491000211 131027011355343369736500317)
            ·
              refine ⟨49135129258253763651187619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131027011355343369736500317 49135129258253763651187619)
              ·
                refine ⟨73702693887380645476781429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49135129258253763651187619 73702693887380645476781429)
                ·
                  refine ⟨6909627551941935513448259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73702693887380645476781429 6909627551941935513448259)
                  ·
                    refine ⟨10364441327912903270172389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6909627551941935513448259 10364441327912903270172389)
                    ·
                      refine ⟨1943332748983669363157323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10364441327912903270172389 1943332748983669363157323)
                      ·
                        rfl

theorem cell23_3784627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 4].length) (baseStart_3784627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784627 prefixEnd_3784627 := by exact prefixLift 3784627
  have htrace : WordTrace (prefixWord ++ tailWord_3784627) baseStart_3784627 baseEnd_3784627 := by
    simpa [prefixWord, tailWord_3784627, baseEnd_3784627] using wordTrace_append hprefix tailTrace_3784627
  have hstable : (prefixWord ++ tailWord_3784627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784627).length < 2 ^ (prefixWord ++ tailWord_3784627).sum := by decide
  have hdescent : baseEnd_3784627 < baseStart_3784627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784648 : List Nat := [2, 1, 3, 1, 4, 3, 1, 1, 2, 3, 2]
def baseStart_3784648 : Nat := 118140960795 + 3784648 * 2 ^ 59
def prefixEnd_3784648 : Nat := 4983230072969 + 3 ^ 40 * 3784648 * 2
def baseEnd_3784648 : Nat := 1943343532077413780994727

theorem tailTrace_3784648 : CollatzResearch.WordTrace tailWord_3784648 prefixEnd_3784648 1943343532077413780994727 := by
  unfold tailWord_3784648
  simp only [CollatzResearch.WordTrace]
  refine ⟨69018726396437068631825299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92024968528582758175767065 69018726396437068631825299)
  ·
    refine ⟨103528089594655602947737949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69018726396437068631825299 103528089594655602947737949)
    ·
      refine ⟨38823033597995851105401731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103528089594655602947737949 38823033597995851105401731)
      ·
        refine ⟨58234550396993776658102597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38823033597995851105401731 58234550396993776658102597)
        ·
          refine ⟨10918978199436333123394237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58234550396993776658102597 10918978199436333123394237)
          ·
            refine ⟨4094616824788624921272839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10918978199436333123394237 4094616824788624921272839)
            ·
              refine ⟨6141925237182937381909259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4094616824788624921272839 6141925237182937381909259)
              ·
                refine ⟨9212887855774406072863889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6141925237182937381909259 9212887855774406072863889)
                ·
                  refine ⟨6909665891830804554647917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9212887855774406072863889 6909665891830804554647917)
                  ·
                    refine ⟨2591124709436551707992969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6909665891830804554647917 2591124709436551707992969)
                    ·
                      refine ⟨1943343532077413780994727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2591124709436551707992969 1943343532077413780994727)
                      ·
                        rfl

theorem cell23_3784648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 2, 3, 2].length) (baseStart_3784648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784648 prefixEnd_3784648 := by exact prefixLift 3784648
  have htrace : WordTrace (prefixWord ++ tailWord_3784648) baseStart_3784648 baseEnd_3784648 := by
    simpa [prefixWord, tailWord_3784648, baseEnd_3784648] using wordTrace_append hprefix tailTrace_3784648
  have hstable : (prefixWord ++ tailWord_3784648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784648).length < 2 ^ (prefixWord ++ tailWord_3784648).sum := by decide
  have hdescent : baseEnd_3784648 < baseStart_3784648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784654 : List Nat := [4, 1, 1, 1, 2, 2, 2, 2, 4, 4]
def baseStart_3784654 : Nat := 118140960795 + 3784654 * 2 ^ 59
def prefixEnd_3784654 : Nat := 4983230072969 + 3 ^ 40 * 3784654 * 2
def baseEnd_3784654 : Nat := 647782204320446919173233

theorem tailTrace_3784654 : CollatzResearch.WordTrace tailWord_3784654 prefixEnd_3784654 647782204320446919173233 := by
  unfold tailWord_3784654
  simp only [CollatzResearch.WordTrace]
  refine ⟨17254708953856550036046127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92025114420568266858912677 17254708953856550036046127)
  ·
    refine ⟨25882063430784825054069191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17254708953856550036046127 25882063430784825054069191)
    ·
      refine ⟨38823095146177237581103787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25882063430784825054069191 38823095146177237581103787)
      ·
        refine ⟨58234642719265856371655681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38823095146177237581103787 58234642719265856371655681)
        ·
          refine ⟨43675982039449392278741761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58234642719265856371655681 43675982039449392278741761)
          ·
            refine ⟨32756986529587044209056321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43675982039449392278741761 32756986529587044209056321)
            ·
              refine ⟨24567739897190283156792241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32756986529587044209056321 24567739897190283156792241)
              ·
                refine ⟨18425804922892712367594181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24567739897190283156792241 18425804922892712367594181)
                ·
                  refine ⟨3454838423042383568923909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18425804922892712367594181 3454838423042383568923909)
                  ·
                    refine ⟨647782204320446919173233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3454838423042383568923909 647782204320446919173233)
                    ·
                      rfl

theorem cell23_3784654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_3784654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784654 prefixEnd_3784654 := by exact prefixLift 3784654
  have htrace : WordTrace (prefixWord ++ tailWord_3784654) baseStart_3784654 baseEnd_3784654 := by
    simpa [prefixWord, tailWord_3784654, baseEnd_3784654] using wordTrace_append hprefix tailTrace_3784654
  have hstable : (prefixWord ++ tailWord_3784654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784654).length < 2 ^ (prefixWord ++ tailWord_3784654).sum := by decide
  have hdescent : baseEnd_3784654 < baseStart_3784654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784657 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 3, 2, 4]
def baseStart_3784657 : Nat := 118140960795 + 3784657 * 2 ^ 59
def prefixEnd_3784657 : Nat := 4983230072969 + 3 ^ 40 * 3784657 * 2
def baseEnd_3784657 : Nat := 1943348153403304245782185

theorem tailTrace_3784657 : CollatzResearch.WordTrace tailWord_3784657 prefixEnd_3784657 1943348153403304245782185 := by
  unfold tailWord_3784657
  simp only [CollatzResearch.WordTrace]
  refine ⟨138037781049841531800728225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92025187366561021200485483 138037781049841531800728225)
  ·
    refine ⟨103528335787381148850546169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138037781049841531800728225 103528335787381148850546169)
    ·
      refine ⟨77646251840535861637909627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103528335787381148850546169 77646251840535861637909627)
      ·
        refine ⟨116469377760803792456864441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77646251840535861637909627 116469377760803792456864441)
        ·
          refine ⟨87352033320602844342648331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116469377760803792456864441 87352033320602844342648331)
          ·
            refine ⟨131028049980904266513972497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87352033320602844342648331 131028049980904266513972497)
            ·
              refine ⟨98271037485678199885479373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131028049980904266513972497 98271037485678199885479373)
              ·
                refine ⟨36851639057129324957054765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98271037485678199885479373 36851639057129324957054765)
                ·
                  refine ⟨13819364646423496858895537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36851639057129324957054765 13819364646423496858895537)
                  ·
                    refine ⟨10364523484817622644171653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13819364646423496858895537 10364523484817622644171653)
                    ·
                      refine ⟨1943348153403304245782185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10364523484817622644171653 1943348153403304245782185)
                      ·
                        rfl

theorem cell23_3784657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_3784657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784657 prefixEnd_3784657 := by exact prefixLift 3784657
  have htrace : WordTrace (prefixWord ++ tailWord_3784657) baseStart_3784657 baseEnd_3784657 := by
    simpa [prefixWord, tailWord_3784657, baseEnd_3784657] using wordTrace_append hprefix tailTrace_3784657
  have hstable : (prefixWord ++ tailWord_3784657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784657).length < 2 ^ (prefixWord ++ tailWord_3784657).sum := by decide
  have hdescent : baseEnd_3784657 < baseStart_3784657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784661 : List Nat := [1, 3, 2, 3, 2, 2, 1, 3, 1, 1, 4]
def baseStart_3784661 : Nat := 118140960795 + 3784661 * 2 ^ 59
def prefixEnd_3784661 : Nat := 4983230072969 + 3 ^ 40 * 3784661 * 2
def baseEnd_3784661 : Nat := 1943350207325922230132167

theorem tailTrace_3784661 : CollatzResearch.WordTrace tailWord_3784661 prefixEnd_3784661 1943350207325922230132167 := by
  unfold tailWord_3784661
  simp only [CollatzResearch.WordTrace]
  refine ⟨138037926941827040483873837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92025284627884693655915891 138037926941827040483873837)
  ·
    refine ⟨51764222603185140181452689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138037926941827040483873837 51764222603185140181452689)
    ·
      refine ⟨38823166952388855136089517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51764222603185140181452689 38823166952388855136089517)
      ·
        refine ⟨14558687607145820676033569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38823166952388855136089517 14558687607145820676033569)
        ·
          refine ⟨10919015705359365507025177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14558687607145820676033569 10919015705359365507025177)
          ·
            refine ⟨8189261779019524130268883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10919015705359365507025177 8189261779019524130268883)
            ·
              refine ⟨12283892668529286195403325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8189261779019524130268883 12283892668529286195403325)
              ·
                refine ⟨4606459750698482323276247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12283892668529286195403325 4606459750698482323276247)
                ·
                  refine ⟨6909689626047723484914371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4606459750698482323276247 6909689626047723484914371)
                  ·
                    refine ⟨10364534439071585227371557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6909689626047723484914371 10364534439071585227371557)
                    ·
                      refine ⟨1943350207325922230132167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10364534439071585227371557 1943350207325922230132167)
                      ·
                        rfl

theorem cell23_3784661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_3784661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784661 prefixEnd_3784661 := by exact prefixLift 3784661
  have htrace : WordTrace (prefixWord ++ tailWord_3784661) baseStart_3784661 baseEnd_3784661 := by
    simpa [prefixWord, tailWord_3784661, baseEnd_3784661] using wordTrace_append hprefix tailTrace_3784661
  have hstable : (prefixWord ++ tailWord_3784661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784661).length < 2 ^ (prefixWord ++ tailWord_3784661).sum := by decide
  have hdescent : baseEnd_3784661 < baseStart_3784661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784671 : List Nat := [1, 1, 2, 3, 4, 1, 3, 2, 2, 4]
def baseStart_3784671 : Nat := 118140960795 + 3784671 * 2 ^ 59
def prefixEnd_3784671 : Nat := 4983230072969 + 3 ^ 40 * 3784671 * 2
def baseEnd_3784671 : Nat := 647785114044155730335707

theorem tailTrace_3784671 : CollatzResearch.WordTrace tailWord_3784671 prefixEnd_3784671 647785114044155730335707 := by
  unfold tailWord_3784671
  simp only [CollatzResearch.WordTrace]
  refine ⟨138038291671790812191737867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92025527781193874794491911 138038291671790812191737867)
  ·
    refine ⟨207057437507686218287606801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138038291671790812191737867 207057437507686218287606801)
    ·
      refine ⟨155293078130764663715705101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207057437507686218287606801 155293078130764663715705101)
      ·
        refine ⟨58234904299036748893389413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155293078130764663715705101 58234904299036748893389413)
        ·
          refine ⟨10919044556069390417510515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58234904299036748893389413 10919044556069390417510515)
          ·
            refine ⟨16378566834104085626265773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10919044556069390417510515 16378566834104085626265773)
            ·
              refine ⟨6141962562789032109849665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16378566834104085626265773 6141962562789032109849665)
              ·
                refine ⟨4606471922091774082387249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6141962562789032109849665 4606471922091774082387249)
                ·
                  refine ⟨3454853941568830561790437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4606471922091774082387249 3454853941568830561790437)
                  ·
                    refine ⟨647785114044155730335707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3454853941568830561790437 647785114044155730335707)
                    ·
                      rfl

theorem cell23_3784671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 2, 4].length) (baseStart_3784671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784671 prefixEnd_3784671 := by exact prefixLift 3784671
  have htrace : WordTrace (prefixWord ++ tailWord_3784671) baseStart_3784671 baseEnd_3784671 := by
    simpa [prefixWord, tailWord_3784671, baseEnd_3784671] using wordTrace_append hprefix tailTrace_3784671
  have hstable : (prefixWord ++ tailWord_3784671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784671).length < 2 ^ (prefixWord ++ tailWord_3784671).sum := by decide
  have hdescent : baseEnd_3784671 < baseStart_3784671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784711 : List Nat := [1, 1, 4, 3, 1, 2, 1, 2, 4, 1, 3]
def baseStart_3784711 : Nat := 118140960795 + 3784711 * 2 ^ 59
def prefixEnd_3784711 : Nat := 4983230072969 + 3 ^ 40 * 3784711 * 2
def baseEnd_3784711 : Nat := 1943375881358647034506937

theorem tailTrace_3784711 : CollatzResearch.WordTrace tailWord_3784711 prefixEnd_3784711 1943375881358647034506937 := by
  unfold tailWord_3784711
  simp only [CollatzResearch.WordTrace]
  refine ⟨138039750591645899023193987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92026500394430599348795991 138039750591645899023193987)
  ·
    refine ⟨207059625887468848534790981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138039750591645899023193987 207059625887468848534790981)
    ·
      refine ⟨38823679853900409100273309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207059625887468848534790981 38823679853900409100273309)
      ·
        refine ⟨14558879945212653412602491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38823679853900409100273309 14558879945212653412602491)
        ·
          refine ⟨21838319917818980118903737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14558879945212653412602491 21838319917818980118903737)
          ·
            refine ⟨16378739938364235089177803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21838319917818980118903737 16378739938364235089177803)
            ·
              refine ⟨24568109907546352633766705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16378739938364235089177803 24568109907546352633766705)
              ·
                refine ⟨18426082430659764475325029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24568109907546352633766705 18426082430659764475325029)
                ·
                  refine ⟨3454890455748705839123443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18426082430659764475325029 3454890455748705839123443)
                  ·
                    refine ⟨5182335683623058758685165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3454890455748705839123443 5182335683623058758685165)
                    ·
                      refine ⟨1943375881358647034506937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5182335683623058758685165 1943375881358647034506937)
                      ·
                        rfl

theorem cell23_3784711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_3784711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784711 prefixEnd_3784711 := by exact prefixLift 3784711
  have htrace : WordTrace (prefixWord ++ tailWord_3784711) baseStart_3784711 baseEnd_3784711 := by
    simpa [prefixWord, tailWord_3784711, baseEnd_3784711] using wordTrace_append hprefix tailTrace_3784711
  have hstable : (prefixWord ++ tailWord_3784711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784711).length < 2 ^ (prefixWord ++ tailWord_3784711).sum := by decide
  have hdescent : baseEnd_3784711 < baseStart_3784711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784751 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 6, 2, 2]
def baseStart_3784751 : Nat := 118140960795 + 3784751 * 2 ^ 59
def prefixEnd_3784751 : Nat := 4983230072969 + 3 ^ 40 * 3784751 * 2
def baseEnd_3784751 : Nat := 1943396420584826878006753

theorem tailTrace_3784751 : CollatzResearch.WordTrace tailWord_3784751 prefixEnd_3784751 1943396420584826878006753 := by
  unfold tailWord_3784751
  simp only [CollatzResearch.WordTrace]
  refine ⟨138041209511500985854650107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92027473007667323903100071 138041209511500985854650107)
  ·
    refine ⟨207061814267251478781975161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138041209511500985854650107 207061814267251478781975161)
    ·
      refine ⟨155296360700438609086481371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207061814267251478781975161 155296360700438609086481371)
      ·
        refine ⟨232944541050657913629722057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155296360700438609086481371 232944541050657913629722057)
        ·
          refine ⟨174708405787993435222291543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232944541050657913629722057 174708405787993435222291543)
          ·
            refine ⟨262062608681990152833437315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174708405787993435222291543 262062608681990152833437315)
            ·
              refine ⟨393093913022985229250155973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262062608681990152833437315 393093913022985229250155973)
              ·
                refine ⟨73705108691809730484404245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 393093913022985229250155973 73705108691809730484404245)
                ·
                  refine ⟨3454926969928581116456449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73705108691809730484404245 3454926969928581116456449)
                  ·
                    refine ⟨2591195227446435837342337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3454926969928581116456449 2591195227446435837342337)
                    ·
                      refine ⟨1943396420584826878006753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2591195227446435837342337 1943396420584826878006753)
                      ·
                        rfl

theorem cell23_3784751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 6, 2, 2].length) (baseStart_3784751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784751 prefixEnd_3784751 := by exact prefixLift 3784751
  have htrace : WordTrace (prefixWord ++ tailWord_3784751) baseStart_3784751 baseEnd_3784751 := by
    simpa [prefixWord, tailWord_3784751, baseEnd_3784751] using wordTrace_append hprefix tailTrace_3784751
  have hstable : (prefixWord ++ tailWord_3784751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784751).length < 2 ^ (prefixWord ++ tailWord_3784751).sum := by decide
  have hdescent : baseEnd_3784751 < baseStart_3784751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784754 : List Nat := [3, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5]
def baseStart_3784754 : Nat := 118140960795 + 3784754 * 2 ^ 59
def prefixEnd_3784754 : Nat := 4983230072969 + 3 ^ 40 * 3784754 * 2
def baseEnd_3784754 : Nat := 1943397961026790366269239

theorem tailTrace_3784754 : CollatzResearch.WordTrace tailWord_3784754 prefixEnd_3784754 1943397961026790366269239 := by
  unfold tailWord_3784754
  simp only [CollatzResearch.WordTrace]
  refine ⟨34510329732622529341752329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92027545953660078244672877 34510329732622529341752329)
  ·
    refine ⟨25882747299466897006314247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34510329732622529341752329 25882747299466897006314247)
    ·
      refine ⟨38824120949200345509471371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25882747299466897006314247 38824120949200345509471371)
      ·
        refine ⟨58236181423800518264207057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38824120949200345509471371 58236181423800518264207057)
        ·
          refine ⟨43677136067850388698155293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58236181423800518264207057 43677136067850388698155293)
          ·
            refine ⟨16378926025443895761808235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43677136067850388698155293 16378926025443895761808235)
            ·
              refine ⟨24568389038165843642712353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16378926025443895761808235 24568389038165843642712353)
              ·
                refine ⟨18426291778624382732034265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24568389038165843642712353 18426291778624382732034265)
                ·
                  refine ⟨13819718833968287049025699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18426291778624382732034265 13819718833968287049025699)
                  ·
                    refine ⟨20729578250952430573538549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13819718833968287049025699 20729578250952430573538549)
                    ·
                      refine ⟨1943397961026790366269239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20729578250952430573538549 1943397961026790366269239)
                      ·
                        rfl

theorem cell23_3784754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_3784754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784754 prefixEnd_3784754 := by exact prefixLift 3784754
  have htrace : WordTrace (prefixWord ++ tailWord_3784754) baseStart_3784754 baseEnd_3784754 := by
    simpa [prefixWord, tailWord_3784754, baseEnd_3784754] using wordTrace_append hprefix tailTrace_3784754
  have hstable : (prefixWord ++ tailWord_3784754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784754).length < 2 ^ (prefixWord ++ tailWord_3784754).sum := by decide
  have hdescent : baseEnd_3784754 < baseStart_3784754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784781 : List Nat := [1, 6, 1, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_3784781 : Nat := 118140960795 + 3784781 * 2 ^ 59
def prefixEnd_3784781 : Nat := 4983230072969 + 3 ^ 40 * 3784781 * 2
def baseEnd_3784781 : Nat := 1943411825004461760631615

theorem tailTrace_3784781 : CollatzResearch.WordTrace tailWord_3784781 prefixEnd_3784781 1943411825004461760631615 := by
  unfold tailWord_3784781
  simp only [CollatzResearch.WordTrace]
  refine ⟨138042303701392300978242197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92028202467594867318828131 138042303701392300978242197)
  ·
    refine ⟨6470732986002764108355103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 138042303701392300978242197 6470732986002764108355103)
    ·
      refine ⟨9706099479004146162532655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6470732986002764108355103 9706099479004146162532655)
      ·
        refine ⟨14559149218506219243798983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9706099479004146162532655 14559149218506219243798983)
        ·
          refine ⟨21838723827759328865698475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14559149218506219243798983 21838723827759328865698475)
          ·
            refine ⟨32758085741638993298547713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21838723827759328865698475 32758085741638993298547713)
            ·
              refine ⟨24568564306229244973910785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32758085741638993298547713 24568564306229244973910785)
              ·
                refine ⟨18426423229671933730433089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24568564306229244973910785 18426423229671933730433089)
                ·
                  refine ⟨13819817422253950297824817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18426423229671933730433089 13819817422253950297824817)
                  ·
                    refine ⟨10364863066690462723368613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13819817422253950297824817 10364863066690462723368613)
                    ·
                      refine ⟨1943411825004461760631615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10364863066690462723368613 1943411825004461760631615)
                      ·
                        rfl

theorem cell23_3784781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_3784781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784781 prefixEnd_3784781 := by exact prefixLift 3784781
  have htrace : WordTrace (prefixWord ++ tailWord_3784781) baseStart_3784781 baseEnd_3784781 := by
    simpa [prefixWord, tailWord_3784781, baseEnd_3784781] using wordTrace_append hprefix tailTrace_3784781
  have hstable : (prefixWord ++ tailWord_3784781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784781).length < 2 ^ (prefixWord ++ tailWord_3784781).sum := by decide
  have hdescent : baseEnd_3784781 < baseStart_3784781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784804 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 4, 5]
def baseStart_3784804 : Nat := 118140960795 + 3784804 * 2 ^ 59
def prefixEnd_3784804 : Nat := 4983230072969 + 3 ^ 40 * 3784804 * 2
def baseEnd_3784804 : Nat := 647807878353171723548003

theorem tailTrace_3784804 : CollatzResearch.WordTrace tailWord_3784804 prefixEnd_3784804 647807878353171723548003 := by
  unfold tailWord_3784804
  simp only [CollatzResearch.WordTrace]
  refine ⟨69021571290154487953164733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92028761720205983937552977 69021571290154487953164733)
  ·
    refine ⟨25883089233807932982436775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69021571290154487953164733 25883089233807932982436775)
    ·
      refine ⟨38824633850711899473655163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25883089233807932982436775 38824633850711899473655163)
      ·
        refine ⟨58236950776067849210482745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38824633850711899473655163 58236950776067849210482745)
        ·
          refine ⟨43677713082050886907862059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58236950776067849210482745 43677713082050886907862059)
          ·
            refine ⟨65516569623076330361793089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43677713082050886907862059 65516569623076330361793089)
            ·
              refine ⟨49137427217307247771344817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65516569623076330361793089 49137427217307247771344817)
              ·
                refine ⟨36853070412980435828508613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49137427217307247771344817 36853070412980435828508613)
                ·
                  refine ⟨6909950702433831717845365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36853070412980435828508613 6909950702433831717845365)
                  ·
                    refine ⟨647807878353171723548003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6909950702433831717845365 647807878353171723548003)
                    ·
                      rfl

theorem cell23_3784804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_3784804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3784804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3784804 prefixEnd_3784804 := by exact prefixLift 3784804
  have htrace : WordTrace (prefixWord ++ tailWord_3784804) baseStart_3784804 baseEnd_3784804 := by
    simpa [prefixWord, tailWord_3784804, baseEnd_3784804] using wordTrace_append hprefix tailTrace_3784804
  have hstable : (prefixWord ++ tailWord_3784804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784804).length < 2 ^ (prefixWord ++ tailWord_3784804).sum := by decide
  have hdescent : baseEnd_3784804 < baseStart_3784804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
