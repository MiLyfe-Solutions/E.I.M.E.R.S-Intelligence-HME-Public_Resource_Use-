import V185TrunkScan23Chunk1227

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7276611 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 3, 5, 2]
def baseStart_7276611 : Nat := 118140960795 + 7276611 * 2 ^ 59
def prefixEnd_7276611 : Nat := 4983230072969 + 3 ^ 40 * 7276611 * 2
def baseEnd_7276611 : Nat := 3736398978793534959697981

theorem tailTrace_7276611 : CollatzResearch.WordTrace tailWord_7276611 prefixEnd_7276611 3736398978793534959697981 := by
  unfold tailWord_7276611
  simp only [CollatzResearch.WordTrace]
  refine ⟨265399806641088568063829687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176933204427392378709219791 265399806641088568063829687)
  ·
    refine ⟨398099709961632852095744531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265399806641088568063829687 398099709961632852095744531)
    ·
      refine ⟨597149564942449278143616797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398099709961632852095744531 597149564942449278143616797)
      ·
        refine ⟨223931086853418479303856299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 597149564942449278143616797 223931086853418479303856299)
        ·
          refine ⟨335896630280127718955784449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223931086853418479303856299 335896630280127718955784449)
          ·
            refine ⟨251922472710095789216838337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335896630280127718955784449 251922472710095789216838337)
            ·
              refine ⟨188941854532571841912628753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251922472710095789216838337 188941854532571841912628753)
              ·
                refine ⟨141706390899428881434471565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188941854532571841912628753 141706390899428881434471565)
                ·
                  refine ⟨53139896587285830537926837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141706390899428881434471565 53139896587285830537926837)
                  ·
                    refine ⟨4981865305058046612930641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53139896587285830537926837 4981865305058046612930641)
                    ·
                      refine ⟨3736398978793534959697981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4981865305058046612930641 3736398978793534959697981)
                      ·
                        rfl

theorem cell23_7276611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 5, 2].length) (baseStart_7276611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276611 prefixEnd_7276611 := by exact prefixLift 7276611
  have htrace : WordTrace (prefixWord ++ tailWord_7276611) baseStart_7276611 baseEnd_7276611 := by
    simpa [prefixWord, tailWord_7276611, baseEnd_7276611] using wordTrace_append hprefix tailTrace_7276611
  have hstable : (prefixWord ++ tailWord_7276611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276611).length < 2 ^ (prefixWord ++ tailWord_7276611).sum := by decide
  have hdescent : baseEnd_7276611 < baseStart_7276611 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276624 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 4]
def baseStart_7276624 : Nat := 118140960795 + 7276624 * 2 ^ 59
def prefixEnd_7276624 : Nat := 4983230072969 + 3 ^ 40 * 7276624 * 2
def baseEnd_7276624 : Nat := 3736405654042043408835421

theorem tailTrace_7276624 : CollatzResearch.WordTrace tailWord_7276624 prefixEnd_7276624 3736405654042043408835421 := by
  unfold tailWord_7276624
  simp only [CollatzResearch.WordTrace]
  refine ⟨132700140395020735642026463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176933520526694314189368617 132700140395020735642026463)
  ·
    refine ⟨199050210592531103463039695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132700140395020735642026463 199050210592531103463039695)
    ·
      refine ⟨298575315888796655194559543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199050210592531103463039695 298575315888796655194559543)
      ·
        refine ⟨447862973833194982791839315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298575315888796655194559543 447862973833194982791839315)
        ·
          refine ⟨671794460749792474187758973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447862973833194982791839315 671794460749792474187758973)
          ·
            refine ⟨251922922781172177820409615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 671794460749792474187758973 251922922781172177820409615)
            ·
              refine ⟨377884384171758266730614423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251922922781172177820409615 377884384171758266730614423)
              ·
                refine ⟨566826576257637400095921635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377884384171758266730614423 566826576257637400095921635)
                ·
                  refine ⟨850239864386456100143882453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 566826576257637400095921635 850239864386456100143882453)
                  ·
                    refine ⟨19927496821557564847122245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 850239864386456100143882453 19927496821557564847122245)
                    ·
                      refine ⟨3736405654042043408835421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19927496821557564847122245 3736405654042043408835421)
                      ·
                        rfl

theorem cell23_7276624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 4].length) (baseStart_7276624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276624 prefixEnd_7276624 := by exact prefixLift 7276624
  have htrace : WordTrace (prefixWord ++ tailWord_7276624) baseStart_7276624 baseEnd_7276624 := by
    simpa [prefixWord, tailWord_7276624, baseEnd_7276624] using wordTrace_append hprefix tailTrace_7276624
  have hstable : (prefixWord ++ tailWord_7276624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276624).length < 2 ^ (prefixWord ++ tailWord_7276624).sum := by decide
  have hdescent : baseEnd_7276624 < baseStart_7276624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276628 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 6, 3, 2]
def baseStart_7276628 : Nat := 118140960795 + 7276628 * 2 ^ 59
def prefixEnd_7276628 : Nat := 4983230072969 + 3 ^ 40 * 7276628 * 2
def baseEnd_7276628 : Nat := 3736407707964661393185403

theorem tailTrace_7276628 : CollatzResearch.WordTrace tailWord_7276628 prefixEnd_7276628 3736407707964661393185403 := by
  unfold tailWord_7276628
  simp only [CollatzResearch.WordTrace]
  refine ⟨132700213341013489983599269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176933617788017986644799025 132700213341013489983599269)
  ·
    refine ⟨24881290001440029371924863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132700213341013489983599269 24881290001440029371924863)
    ·
      refine ⟨37321935002160044057887295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24881290001440029371924863 37321935002160044057887295)
      ·
        refine ⟨55982902503240066086830943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37321935002160044057887295 55982902503240066086830943)
        ·
          refine ⟨83974353754860099130246415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55982902503240066086830943 83974353754860099130246415)
          ·
            refine ⟨125961530632290148695369623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83974353754860099130246415 125961530632290148695369623)
            ·
              refine ⟨188942295948435223043054435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125961530632290148695369623 188942295948435223043054435)
              ·
                refine ⟨283413443922652834564581653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188942295948435223043054435 283413443922652834564581653)
                ·
                  refine ⟨13285005183874351620214765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 283413443922652834564581653 13285005183874351620214765)
                  ·
                    refine ⟨4981876943952881857580537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13285005183874351620214765 4981876943952881857580537)
                    ·
                      refine ⟨3736407707964661393185403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4981876943952881857580537 3736407707964661393185403)
                      ·
                        rfl

theorem cell23_7276628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_7276628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276628 prefixEnd_7276628 := by exact prefixLift 7276628
  have htrace : WordTrace (prefixWord ++ tailWord_7276628) baseStart_7276628 baseEnd_7276628 := by
    simpa [prefixWord, tailWord_7276628, baseEnd_7276628] using wordTrace_append hprefix tailTrace_7276628
  have hstable : (prefixWord ++ tailWord_7276628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276628).length < 2 ^ (prefixWord ++ tailWord_7276628).sum := by decide
  have hdescent : baseEnd_7276628 < baseStart_7276628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276645 : List Nat := [1, 3, 1, 3, 2, 3, 2, 1, 2, 3, 2]
def baseStart_7276645 : Nat := 118140960795 + 7276645 * 2 ^ 59
def prefixEnd_7276645 : Nat := 4983230072969 + 3 ^ 40 * 7276645 * 2
def baseEnd_7276645 : Nat := 3736416437135787826672825

theorem tailTrace_7276645 : CollatzResearch.WordTrace tailWord_7276645 prefixEnd_7276645 3736416437135787826672825 := by
  unfold tailWord_7276645
  simp only [CollatzResearch.WordTrace]
  refine ⟨265401046722965391870567389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176934031148643594580378259 265401046722965391870567389)
  ·
    refine ⟨99525392521112021951462771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265401046722965391870567389 99525392521112021951462771)
    ·
      refine ⟨149288088781668032927194157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99525392521112021951462771 149288088781668032927194157)
      ·
        refine ⟨55983033293125512347697809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149288088781668032927194157 55983033293125512347697809)
        ·
          refine ⟨41987274969844134260773357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55983033293125512347697809 41987274969844134260773357)
          ·
            refine ⟨15745228113691550347790009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41987274969844134260773357 15745228113691550347790009)
            ·
              refine ⟨11808921085268662760842507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15745228113691550347790009 11808921085268662760842507)
              ·
                refine ⟨17713381627902994141263761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11808921085268662760842507 17713381627902994141263761)
                ·
                  refine ⟨13285036220927245605947821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17713381627902994141263761 13285036220927245605947821)
                  ·
                    refine ⟨4981888582847717102230433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13285036220927245605947821 4981888582847717102230433)
                    ·
                      refine ⟨3736416437135787826672825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4981888582847717102230433 3736416437135787826672825)
                      ·
                        rfl

theorem cell23_7276645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_7276645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276645 prefixEnd_7276645 := by exact prefixLift 7276645
  have htrace : WordTrace (prefixWord ++ tailWord_7276645) baseStart_7276645 baseEnd_7276645 := by
    simpa [prefixWord, tailWord_7276645, baseEnd_7276645] using wordTrace_append hprefix tailTrace_7276645
  have hstable : (prefixWord ++ tailWord_7276645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276645).length < 2 ^ (prefixWord ++ tailWord_7276645).sum := by decide
  have hdescent : baseEnd_7276645 < baseStart_7276645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276668 : List Nat := [2, 2, 2, 1, 1, 4, 1, 4, 2, 4]
def baseStart_7276668 : Nat := 118140960795 + 7276668 * 2 ^ 59
def prefixEnd_7276668 : Nat := 4983230072969 + 3 ^ 40 * 7276668 * 2
def baseEnd_7276668 : Nat := 1245476082396947078895073

theorem tailTrace_7276668 : CollatzResearch.WordTrace tailWord_7276668 prefixEnd_7276668 1245476082396947078895073 := by
  unfold tailWord_7276668
  simp only [CollatzResearch.WordTrace]
  refine ⟨132700942800941033399327329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176934590401254711199103105 132700942800941033399327329)
  ·
    refine ⟨99525707100705775049495497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132700942800941033399327329 99525707100705775049495497)
    ·
      refine ⟨74644280325529331287121623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99525707100705775049495497 74644280325529331287121623)
      ·
        refine ⟨111966420488293996930682435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74644280325529331287121623 111966420488293996930682435)
        ·
          refine ⟨167949630732440995396023653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111966420488293996930682435 167949630732440995396023653)
          ·
            refine ⟨31490555762332686636754435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167949630732440995396023653 31490555762332686636754435)
            ·
              refine ⟨47235833643499029955131653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31490555762332686636754435 47235833643499029955131653)
              ·
                refine ⟨8856718808156068116587185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47235833643499029955131653 8856718808156068116587185)
                ·
                  refine ⟨6642539106117051087440389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8856718808156068116587185 6642539106117051087440389)
                  ·
                    refine ⟨1245476082396947078895073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6642539106117051087440389 1245476082396947078895073)
                    ·
                      rfl

theorem cell23_7276668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_7276668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276668 prefixEnd_7276668 := by exact prefixLift 7276668
  have htrace : WordTrace (prefixWord ++ tailWord_7276668) baseStart_7276668 baseEnd_7276668 := by
    simpa [prefixWord, tailWord_7276668, baseEnd_7276668] using wordTrace_append hprefix tailTrace_7276668
  have hstable : (prefixWord ++ tailWord_7276668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276668).length < 2 ^ (prefixWord ++ tailWord_7276668).sum := by decide
  have hdescent : baseEnd_7276668 < baseStart_7276668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276669 : List Nat := [1, 4, 1, 1, 3, 4, 2, 2, 1, 1, 3]
def baseStart_7276669 : Nat := 118140960795 + 7276669 * 2 ^ 59
def prefixEnd_7276669 : Nat := 4983230072969 + 3 ^ 40 * 7276669 * 2
def baseEnd_7276669 : Nat := 3736428760671495732772715

theorem tailTrace_7276669 : CollatzResearch.WordTrace tailWord_7276669 prefixEnd_7276669 3736428760671495732772715 := by
  unfold tailWord_7276669
  simp only [CollatzResearch.WordTrace]
  refine ⟨265401922074878443969441061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176934614716585629312960707 265401922074878443969441061)
  ·
    refine ⟨49762860389039708244270199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265401922074878443969441061 49762860389039708244270199)
    ·
      refine ⟨74644290583559562366405299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49762860389039708244270199 74644290583559562366405299)
      ·
        refine ⟨111966435875339343549607949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74644290583559562366405299 111966435875339343549607949)
        ·
          refine ⟨41987413453252253831102981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111966435875339343549607949 41987413453252253831102981)
          ·
            refine ⟨7872640022484797593331809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41987413453252253831102981 7872640022484797593331809)
            ·
              refine ⟨5904480016863598194998857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7872640022484797593331809 5904480016863598194998857)
              ·
                refine ⟨4428360012647698646249143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5904480016863598194998857 4428360012647698646249143)
                ·
                  refine ⟨6642540018971547969373715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4428360012647698646249143 6642540018971547969373715)
                  ·
                    refine ⟨9963810028457321954060573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6642540018971547969373715 9963810028457321954060573)
                    ·
                      refine ⟨3736428760671495732772715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9963810028457321954060573 3736428760671495732772715)
                      ·
                        rfl

theorem cell23_7276669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 2, 1, 1, 3].length) (baseStart_7276669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276669 prefixEnd_7276669 := by exact prefixLift 7276669
  have htrace : WordTrace (prefixWord ++ tailWord_7276669) baseStart_7276669 baseEnd_7276669 := by
    simpa [prefixWord, tailWord_7276669, baseEnd_7276669] using wordTrace_append hprefix tailTrace_7276669
  have hstable : (prefixWord ++ tailWord_7276669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276669).length < 2 ^ (prefixWord ++ tailWord_7276669).sum := by decide
  have hdescent : baseEnd_7276669 < baseStart_7276669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276741 : List Nat := [1, 3, 1, 1, 1, 1, 6, 1, 2, 6]
def baseStart_7276741 : Nat := 118140960795 + 7276741 * 2 ^ 59
def prefixEnd_7276741 : Nat := 4983230072969 + 3 ^ 40 * 7276741 * 2
def baseEnd_7276741 : Nat := 1245488577092873150357461

theorem tailTrace_7276741 : CollatzResearch.WordTrace tailWord_7276741 prefixEnd_7276741 1245488577092873150357461 := by
  unfold tailWord_7276741
  simp only [CollatzResearch.WordTrace]
  refine ⟨265404548130617600266062077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176936365420411733510708051 265404548130617600266062077)
  ·
    refine ⟨99526705548981600099773279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265404548130617600266062077 99526705548981600099773279)
    ·
      refine ⟨149290058323472400149659919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99526705548981600099773279 149290058323472400149659919)
      ·
        refine ⟨223935087485208600224489879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149290058323472400149659919 223935087485208600224489879)
        ·
          refine ⟨335902631227812900336734819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223935087485208600224489879 335902631227812900336734819)
          ·
            refine ⟨503853946841719350505102229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335902631227812900336734819 503853946841719350505102229)
            ·
              refine ⟨23618153758205594554926667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 503853946841719350505102229 23618153758205594554926667)
              ·
                refine ⟨35427230637308391832390001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23618153758205594554926667 35427230637308391832390001)
                ·
                  refine ⟨26570422977981293874292501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35427230637308391832390001 26570422977981293874292501)
                  ·
                    refine ⟨1245488577092873150357461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26570422977981293874292501 1245488577092873150357461)
                    ·
                      rfl

theorem cell23_7276741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 6].length) (baseStart_7276741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276741 prefixEnd_7276741 := by exact prefixLift 7276741
  have htrace : WordTrace (prefixWord ++ tailWord_7276741) baseStart_7276741 baseEnd_7276741 := by
    simpa [prefixWord, tailWord_7276741, baseEnd_7276741] using wordTrace_append hprefix tailTrace_7276741
  have hstable : (prefixWord ++ tailWord_7276741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276741).length < 2 ^ (prefixWord ++ tailWord_7276741).sum := by decide
  have hdescent : baseEnd_7276741 < baseStart_7276741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276751 : List Nat := [1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 5]
def baseStart_7276751 : Nat := 118140960795 + 7276751 * 2 ^ 59
def prefixEnd_7276751 : Nat := 4983230072969 + 3 ^ 40 * 7276751 * 2
def baseEnd_7276751 : Nat := 3736470866085164411947337

theorem tailTrace_7276751 : CollatzResearch.WordTrace tailWord_7276751 prefixEnd_7276751 3736470866085164411947337 := by
  unfold tailWord_7276751
  simp only [CollatzResearch.WordTrace]
  refine ⟨265404912860581371973926107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176936608573720914649284071 265404912860581371973926107)
  ·
    refine ⟨398107369290872057960889161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265404912860581371973926107 398107369290872057960889161)
    ·
      refine ⟨298580526968154043470666871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398107369290872057960889161 298580526968154043470666871)
      ·
        refine ⟨447870790452231065206000307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298580526968154043470666871 447870790452231065206000307)
        ·
          refine ⟨671806185678346597809000461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447870790452231065206000307 671806185678346597809000461)
          ·
            refine ⟨251927319629379974178375173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 671806185678346597809000461 251927319629379974178375173)
            ·
              refine ⟨47236372430508745158445345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 251927319629379974178375173 47236372430508745158445345)
              ·
                refine ⟨35427279322881558868834009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47236372430508745158445345 35427279322881558868834009)
                ·
                  refine ⟨26570459492161169151625507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35427279322881558868834009 26570459492161169151625507)
                  ·
                    refine ⟨39855689238241753727438261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26570459492161169151625507 39855689238241753727438261)
                    ·
                      refine ⟨3736470866085164411947337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39855689238241753727438261 3736470866085164411947337)
                      ·
                        rfl

theorem cell23_7276751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 5].length) (baseStart_7276751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276751 prefixEnd_7276751 := by exact prefixLift 7276751
  have htrace : WordTrace (prefixWord ++ tailWord_7276751) baseStart_7276751 baseEnd_7276751 := by
    simpa [prefixWord, tailWord_7276751, baseEnd_7276751] using wordTrace_append hprefix tailTrace_7276751
  have hstable : (prefixWord ++ tailWord_7276751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276751).length < 2 ^ (prefixWord ++ tailWord_7276751).sum := by decide
  have hdescent : baseEnd_7276751 < baseStart_7276751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276761 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 1, 4, 4]
def baseStart_7276761 : Nat := 118140960795 + 7276761 * 2 ^ 59
def prefixEnd_7276761 : Nat := 4983230072969 + 3 ^ 40 * 7276761 * 2
def baseEnd_7276761 : Nat := 3736476000891709372822291

theorem tailTrace_7276761 : CollatzResearch.WordTrace tailWord_7276761 prefixEnd_7276761 3736476000891709372822291 := by
  unfold tailWord_7276761
  simp only [CollatzResearch.WordTrace]
  refine ⟨265405277590545143681790137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176936851727030095787860091 265405277590545143681790137)
  ·
    refine ⟨199053958192908857761342603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265405277590545143681790137 199053958192908857761342603)
    ·
      refine ⟨298580937289363286642013905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199053958192908857761342603 298580937289363286642013905)
      ·
        refine ⟨223935702967022464981510429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298580937289363286642013905 223935702967022464981510429)
        ·
          refine ⟨83975888612633424368066411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223935702967022464981510429 83975888612633424368066411)
          ·
            refine ⟨125963832918950136552099617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83975888612633424368066411 125963832918950136552099617)
            ·
              refine ⟨94472874689212602414074713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125963832918950136552099617 94472874689212602414074713)
              ·
                refine ⟨70854656016909451810556035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94472874689212602414074713 70854656016909451810556035)
                ·
                  refine ⟨106281984025364177715834053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70854656016909451810556035 106281984025364177715834053)
                  ·
                    refine ⟨19927872004755783321718885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106281984025364177715834053 19927872004755783321718885)
                    ·
                      refine ⟨3736476000891709372822291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19927872004755783321718885 3736476000891709372822291)
                      ·
                        rfl

theorem cell23_7276761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_7276761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276761 prefixEnd_7276761 := by exact prefixLift 7276761
  have htrace : WordTrace (prefixWord ++ tailWord_7276761) baseStart_7276761 baseEnd_7276761 := by
    simpa [prefixWord, tailWord_7276761, baseEnd_7276761] using wordTrace_append hprefix tailTrace_7276761
  have hstable : (prefixWord ++ tailWord_7276761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276761).length < 2 ^ (prefixWord ++ tailWord_7276761).sum := by decide
  have hdescent : baseEnd_7276761 < baseStart_7276761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276782 : List Nat := [4, 1, 2, 1, 1, 1, 1, 6, 2, 2, 2]
def baseStart_7276782 : Nat := 118140960795 + 7276782 * 2 ^ 59
def prefixEnd_7276782 : Nat := 4983230072969 + 3 ^ 40 * 7276782 * 2
def baseEnd_7276782 : Nat := 3736486783985453790659695

theorem tailTrace_7276782 : CollatzResearch.WordTrace tailWord_7276782 prefixEnd_7276782 3736486783985453790659695 := by
  unfold tailWord_7276782
  simp only [CollatzResearch.WordTrace]
  refine ⟨33175755440433633033538075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176937362348979376178869733 33175755440433633033538075)
  ·
    refine ⟨49763633160650449550307113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33175755440433633033538075 49763633160650449550307113)
    ·
      refine ⟨37322724870487837162730335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49763633160650449550307113 37322724870487837162730335)
      ·
        refine ⟨55984087305731755744095503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37322724870487837162730335 55984087305731755744095503)
        ·
          refine ⟨83976130958597633616143255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55984087305731755744095503 83976130958597633616143255)
          ·
            refine ⟨125964196437896450424214883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83976130958597633616143255 125964196437896450424214883)
            ·
              refine ⟨188946294656844675636322325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125964196437896450424214883 188946294656844675636322325)
              ·
                refine ⟨8856857562039594170452609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 188946294656844675636322325 8856857562039594170452609)
                ·
                  refine ⟨6642643171529695627839457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8856857562039594170452609 6642643171529695627839457)
                  ·
                    refine ⟨4981982378647271720879593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6642643171529695627839457 4981982378647271720879593)
                    ·
                      refine ⟨3736486783985453790659695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4981982378647271720879593 3736486783985453790659695)
                      ·
                        rfl

theorem cell23_7276782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_7276782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276782 prefixEnd_7276782 := by exact prefixLift 7276782
  have htrace : WordTrace (prefixWord ++ tailWord_7276782) baseStart_7276782 baseEnd_7276782 := by
    simpa [prefixWord, tailWord_7276782, baseEnd_7276782] using wordTrace_append hprefix tailTrace_7276782
  have hstable : (prefixWord ++ tailWord_7276782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276782).length < 2 ^ (prefixWord ++ tailWord_7276782).sum := by decide
  have hdescent : baseEnd_7276782 < baseStart_7276782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276811 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 7]
def baseStart_7276811 : Nat := 118140960795 + 7276811 * 2 ^ 59
def prefixEnd_7276811 : Nat := 4983230072969 + 3 ^ 40 * 7276811 * 2
def baseEnd_7276811 : Nat := 3736501674924434177197061

theorem tailTrace_7276811 : CollatzResearch.WordTrace tailWord_7276811 prefixEnd_7276811 3736501674924434177197061 := by
  unfold tailWord_7276811
  simp only [CollatzResearch.WordTrace]
  refine ⟨265407101240364002221110287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176938067493576001480740191 265407101240364002221110287)
  ·
    refine ⟨398110651860546003331665431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265407101240364002221110287 398110651860546003331665431)
    ·
      refine ⟨597165977790819004997498147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398110651860546003331665431 597165977790819004997498147)
      ·
        refine ⟨895748966686228507496247221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597165977790819004997498147 895748966686228507496247221)
        ·
          refine ⟨83976465626833922577773177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 895748966686228507496247221 83976465626833922577773177)
          ·
            refine ⟨62982349220125441933329883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83976465626833922577773177 62982349220125441933329883)
            ·
              refine ⟨94473523830188162899994825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62982349220125441933329883 94473523830188162899994825)
              ·
                refine ⟨70855142872641122174996119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94473523830188162899994825 70855142872641122174996119)
                ·
                  refine ⟨106282714308961683262494179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70855142872641122174996119 106282714308961683262494179)
                  ·
                    refine ⟨159424071463442524893741269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106282714308961683262494179 159424071463442524893741269)
                    ·
                      refine ⟨3736501674924434177197061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 159424071463442524893741269 3736501674924434177197061)
                      ·
                        rfl

theorem cell23_7276811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 7].length) (baseStart_7276811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276811 prefixEnd_7276811 := by exact prefixLift 7276811
  have htrace : WordTrace (prefixWord ++ tailWord_7276811) baseStart_7276811 baseEnd_7276811 := by
    simpa [prefixWord, tailWord_7276811, baseEnd_7276811] using wordTrace_append hprefix tailTrace_7276811
  have hstable : (prefixWord ++ tailWord_7276811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276811).length < 2 ^ (prefixWord ++ tailWord_7276811).sum := by decide
  have hdescent : baseEnd_7276811 < baseStart_7276811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276882 : List Nat := [3, 2, 2, 1, 1, 1, 3, 5, 1, 4]
def baseStart_7276882 : Nat := 118140960795 + 7276882 * 2 ^ 59
def prefixEnd_7276882 : Nat := 4983230072969 + 3 ^ 40 * 7276882 * 2
def baseEnd_7276882 : Nat := 1245512710683634466469745

theorem tailTrace_7276882 : CollatzResearch.WordTrace tailWord_7276882 prefixEnd_7276882 1245512710683634466469745 := by
  unfold tailWord_7276882
  simp only [CollatzResearch.WordTrace]
  refine ⟨66352422705776695336736225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176939793882071187564629933 66352422705776695336736225)
  ·
    refine ⟨49764317029332521502552169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66352422705776695336736225 49764317029332521502552169)
    ·
      refine ⟨37323237771999391126914127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49764317029332521502552169 37323237771999391126914127)
      ·
        refine ⟨55984856657999086690371191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37323237771999391126914127 55984856657999086690371191)
        ·
          refine ⟨83977284986998630035556787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55984856657999086690371191 83977284986998630035556787)
          ·
            refine ⟨125965927480497945053335181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83977284986998630035556787 125965927480497945053335181)
            ·
              refine ⟨47237222805186729395000693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125965927480497945053335181 47237222805186729395000693)
              ·
                refine ⟨4428489637986255880781315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47237222805186729395000693 4428489637986255880781315)
                ·
                  refine ⟨6642734456979383821171973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4428489637986255880781315 6642734456979383821171973)
                  ·
                    refine ⟨1245512710683634466469745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6642734456979383821171973 1245512710683634466469745)
                    ·
                      rfl

theorem cell23_7276882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_7276882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276882 prefixEnd_7276882 := by exact prefixLift 7276882
  have htrace : WordTrace (prefixWord ++ tailWord_7276882) baseStart_7276882 baseEnd_7276882 := by
    simpa [prefixWord, tailWord_7276882, baseEnd_7276882] using wordTrace_append hprefix tailTrace_7276882
  have hstable : (prefixWord ++ tailWord_7276882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276882).length < 2 ^ (prefixWord ++ tailWord_7276882).sum := by decide
  have hdescent : baseEnd_7276882 < baseStart_7276882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276915 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 4, 3, 2]
def baseStart_7276915 : Nat := 118140960795 + 7276915 * 2 ^ 59
def prefixEnd_7276915 : Nat := 4983230072969 + 3 ^ 40 * 7276915 * 2
def baseEnd_7276915 : Nat := 3736555076912501770296583

theorem tailTrace_7276915 : CollatzResearch.WordTrace tailWord_7276915 prefixEnd_7276915 3736555076912501770296583 := by
  unfold tailWord_7276915
  simp only [CollatzResearch.WordTrace]
  refine ⟨265410894431987227982896199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176940596287991485321930799 265410894431987227982896199)
  ·
    refine ⟨398116341647980841974344299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265410894431987227982896199 398116341647980841974344299)
    ·
      refine ⟨597174512471971262961516449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398116341647980841974344299 597174512471971262961516449)
      ·
        refine ⟨447880884353978447221137337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 597174512471971262961516449 447880884353978447221137337)
        ·
          refine ⟨335910663265483835415853003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447880884353978447221137337 335910663265483835415853003)
          ·
            refine ⟨503865994898225753123779505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335910663265483835415853003 503865994898225753123779505)
            ·
              refine ⟨377899496173669314842834629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503865994898225753123779505 377899496173669314842834629)
              ·
                refine ⟨70856155532562996533031493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 377899496173669314842834629 70856155532562996533031493)
                ·
                  refine ⟨13285529162355561849943405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70856155532562996533031493 13285529162355561849943405)
                  ·
                    refine ⟨4982073435883335693728777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13285529162355561849943405 4982073435883335693728777)
                    ·
                      refine ⟨3736555076912501770296583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4982073435883335693728777 3736555076912501770296583)
                      ·
                        rfl

theorem cell23_7276915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 3, 2].length) (baseStart_7276915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276915 prefixEnd_7276915 := by exact prefixLift 7276915
  have htrace : WordTrace (prefixWord ++ tailWord_7276915) baseStart_7276915 baseEnd_7276915 := by
    simpa [prefixWord, tailWord_7276915, baseEnd_7276915] using wordTrace_append hprefix tailTrace_7276915
  have hstable : (prefixWord ++ tailWord_7276915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276915).length < 2 ^ (prefixWord ++ tailWord_7276915).sum := by decide
  have hdescent : baseEnd_7276915 < baseStart_7276915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276925 : List Nat := [1, 4, 1, 1, 2, 3, 1, 4, 1, 5]
def baseStart_7276925 : Nat := 118140960795 + 7276925 * 2 ^ 59
def prefixEnd_7276925 : Nat := 4983230072969 + 3 ^ 40 * 7276925 * 2
def baseEnd_7276925 : Nat := 1245520070573015577057179

theorem tailTrace_7276925 : CollatzResearch.WordTrace tailWord_7276925 prefixEnd_7276925 1245520070573015577057179 := by
  unfold tailWord_7276925
  simp only [CollatzResearch.WordTrace]
  refine ⟨265411259161950999690760229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176940839441300666460506819 265411259161950999690760229)
  ·
    refine ⟨49764611092865812442017543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265411259161950999690760229 49764611092865812442017543)
    ·
      refine ⟨74646916639298718663026315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49764611092865812442017543 74646916639298718663026315)
      ·
        refine ⟨111970374958948077994539473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74646916639298718663026315 111970374958948077994539473)
        ·
          refine ⟨83977781219211058495904605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111970374958948077994539473 83977781219211058495904605)
          ·
            refine ⟨31491667957204146935964227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83977781219211058495904605 31491667957204146935964227)
            ·
              refine ⟨47237501935806220403946341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31491667957204146935964227 47237501935806220403946341)
              ·
                refine ⟨8857031612963666325739939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47237501935806220403946341 8857031612963666325739939)
                ·
                  refine ⟨13285547419445499488609909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8857031612963666325739939 13285547419445499488609909)
                  ·
                    refine ⟨1245520070573015577057179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13285547419445499488609909 1245520070573015577057179)
                    ·
                      rfl

theorem cell23_7276925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_7276925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276925 prefixEnd_7276925 := by exact prefixLift 7276925
  have htrace : WordTrace (prefixWord ++ tailWord_7276925) baseStart_7276925 baseEnd_7276925 := by
    simpa [prefixWord, tailWord_7276925, baseEnd_7276925] using wordTrace_append hprefix tailTrace_7276925
  have hstable : (prefixWord ++ tailWord_7276925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276925).length < 2 ^ (prefixWord ++ tailWord_7276925).sum := by decide
  have hdescent : baseEnd_7276925 < baseStart_7276925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276932 : List Nat := [2, 3, 2, 1, 1, 2, 2, 3, 2, 3, 2]
def baseStart_7276932 : Nat := 118140960795 + 7276932 * 2 ^ 59
def prefixEnd_7276932 : Nat := 4983230072969 + 3 ^ 40 * 7276932 * 2
def baseEnd_7276932 : Nat := 3736563806083628203784005

theorem tailTrace_7276932 : CollatzResearch.WordTrace tailWord_7276932 prefixEnd_7276932 3736563806083628203784005 := by
  unfold tailWord_7276932
  simp only [CollatzResearch.WordTrace]
  refine ⟨132705757236462819943132525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176941009648617093257510033 132705757236462819943132525)
  ·
    refine ⟨49764658963673557478674697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132705757236462819943132525 49764658963673557478674697)
    ·
      refine ⟨37323494222755168109006023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49764658963673557478674697 37323494222755168109006023)
      ·
        refine ⟨55985241334132752163509035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37323494222755168109006023 55985241334132752163509035)
        ·
          refine ⟨83977862001199128245263553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55985241334132752163509035 83977862001199128245263553)
          ·
            refine ⟨62983396500899346183947665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83977862001199128245263553 62983396500899346183947665)
            ·
              refine ⟨47237547375674509637960749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62983396500899346183947665 47237547375674509637960749)
              ·
                refine ⟨17714080265877941114235281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47237547375674509637960749 17714080265877941114235281)
                ·
                  refine ⟨13285560199408455835676461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17714080265877941114235281 13285560199408455835676461)
                  ·
                    refine ⟨4982085074778170938378673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13285560199408455835676461 4982085074778170938378673)
                    ·
                      refine ⟨3736563806083628203784005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4982085074778170938378673 3736563806083628203784005)
                      ·
                        rfl

theorem cell23_7276932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_7276932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276932 prefixEnd_7276932 := by exact prefixLift 7276932
  have htrace : WordTrace (prefixWord ++ tailWord_7276932) baseStart_7276932 baseEnd_7276932 := by
    simpa [prefixWord, tailWord_7276932, baseEnd_7276932] using wordTrace_append hprefix tailTrace_7276932
  have hstable : (prefixWord ++ tailWord_7276932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276932).length < 2 ^ (prefixWord ++ tailWord_7276932).sum := by decide
  have hdescent : baseEnd_7276932 < baseStart_7276932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276939 : List Nat := [1, 1, 1, 1, 4, 4, 3, 3, 1, 1, 3]
def baseStart_7276939 : Nat := 118140960795 + 7276939 * 2 ^ 59
def prefixEnd_7276939 : Nat := 4983230072969 + 3 ^ 40 * 7276939 * 2
def baseEnd_7276939 : Nat := 3736567400448209676396473

theorem tailTrace_7276939 : CollatzResearch.WordTrace tailWord_7276939 prefixEnd_7276939 3736567400448209676396473 := by
  unfold tailWord_7276939
  simp only [CollatzResearch.WordTrace]
  refine ⟨265411769783900280081769871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176941179855933520054513247 265411769783900280081769871)
  ·
    refine ⟨398117654675850420122654807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265411769783900280081769871 398117654675850420122654807)
    ·
      refine ⟨597176482013775630183982211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398117654675850420122654807 597176482013775630183982211)
      ·
        refine ⟨895764723020663445275973317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597176482013775630183982211 895764723020663445275973317)
        ·
          refine ⟨167955885566374395989244997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 895764723020663445275973317 167955885566374395989244997)
          ·
            refine ⟨31491728543695199247983437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167955885566374395989244997 31491728543695199247983437)
            ·
              refine ⟨11809398203885699717993789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31491728543695199247983437 11809398203885699717993789)
              ·
                refine ⟨4428524326457137394247671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11809398203885699717993789 4428524326457137394247671)
                ·
                  refine ⟨6642786489685706091371507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4428524326457137394247671 6642786489685706091371507)
                  ·
                    refine ⟨9964179734528559137057261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6642786489685706091371507 9964179734528559137057261)
                    ·
                      refine ⟨3736567400448209676396473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9964179734528559137057261 3736567400448209676396473)
                      ·
                        rfl

theorem cell23_7276939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 3, 1, 1, 3].length) (baseStart_7276939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276939 prefixEnd_7276939 := by exact prefixLift 7276939
  have htrace : WordTrace (prefixWord ++ tailWord_7276939) baseStart_7276939 baseEnd_7276939 := by
    simpa [prefixWord, tailWord_7276939, baseEnd_7276939] using wordTrace_append hprefix tailTrace_7276939
  have hstable : (prefixWord ++ tailWord_7276939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276939).length < 2 ^ (prefixWord ++ tailWord_7276939).sum := by decide
  have hdescent : baseEnd_7276939 < baseStart_7276939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276942 : List Nat := [4, 1, 1, 4, 1, 1, 2, 3, 1, 5]
def baseStart_7276942 : Nat := 118140960795 + 7276942 * 2 ^ 59
def prefixEnd_7276942 : Nat := 4983230072969 + 3 ^ 40 * 7276942 * 2
def baseEnd_7276942 : Nat := 1245522980296724388219653

theorem tailTrace_7276942 : CollatzResearch.WordTrace tailWord_7276942 prefixEnd_7276942 1245522980296724388219653 := by
  unfold tailWord_7276942
  simp only [CollatzResearch.WordTrace]
  refine ⟨33176484900361176449266135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176941252801926274396086053 33176484900361176449266135)
  ·
    refine ⟨49764727350541764673899203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33176484900361176449266135 49764727350541764673899203)
    ·
      refine ⟨74647091025812647010848805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49764727350541764673899203 74647091025812647010848805)
      ·
        refine ⟨13996329567339871314534151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74647091025812647010848805 13996329567339871314534151)
        ·
          refine ⟨20994494351009806971801227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13996329567339871314534151 20994494351009806971801227)
          ·
            refine ⟨31491741526514710457701841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20994494351009806971801227 31491741526514710457701841)
            ·
              refine ⟨23618806144886032843276381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31491741526514710457701841 23618806144886032843276381)
              ·
                refine ⟨8857052304332262316228643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23618806144886032843276381 8857052304332262316228643)
                ·
                  refine ⟨13285578456498393474342965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8857052304332262316228643 13285578456498393474342965)
                  ·
                    refine ⟨1245522980296724388219653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13285578456498393474342965 1245522980296724388219653)
                    ·
                      rfl

theorem cell23_7276942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_7276942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276942 prefixEnd_7276942 := by exact prefixLift 7276942
  have htrace : WordTrace (prefixWord ++ tailWord_7276942) baseStart_7276942 baseEnd_7276942 := by
    simpa [prefixWord, tailWord_7276942, baseEnd_7276942] using wordTrace_append hprefix tailTrace_7276942
  have hstable : (prefixWord ++ tailWord_7276942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276942).length < 2 ^ (prefixWord ++ tailWord_7276942).sum := by decide
  have hdescent : baseEnd_7276942 < baseStart_7276942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276950 : List Nat := [5, 3, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_7276950 : Nat := 118140960795 + 7276950 * 2 ^ 59
def prefixEnd_7276950 : Nat := 4983230072969 + 3 ^ 40 * 7276950 * 2
def baseEnd_7276950 : Nat := 1245524349578469711119641

theorem tailTrace_7276950 : CollatzResearch.WordTrace tailWord_7276950 prefixEnd_7276950 1245524349578469711119641 := by
  unfold tailWord_7276950
  simp only [CollatzResearch.WordTrace]
  refine ⟨16588260686678776810026269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176941447324573619306946869 16588260686678776810026269)
  ·
    refine ⟨6220597757504541303759851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16588260686678776810026269 6220597757504541303759851)
    ·
      refine ⟨9330896636256811955639777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6220597757504541303759851 9330896636256811955639777)
      ·
        refine ⟨6998172477192608966729833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9330896636256811955639777 6998172477192608966729833)
        ·
          refine ⟨5248629357894456725047375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6998172477192608966729833 5248629357894456725047375)
          ·
            refine ⟨7872944036841685087571063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5248629357894456725047375 7872944036841685087571063)
            ·
              refine ⟨11809416055262527631356595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7872944036841685087571063 11809416055262527631356595)
              ·
                refine ⟨17714124082893791447034893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11809416055262527631356595 17714124082893791447034893)
                ·
                  refine ⟨6642796531085171792638085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17714124082893791447034893 6642796531085171792638085)
                  ·
                    refine ⟨1245524349578469711119641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6642796531085171792638085 1245524349578469711119641)
                    ·
                      rfl

theorem cell23_7276950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_7276950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276950 prefixEnd_7276950 := by exact prefixLift 7276950
  have htrace : WordTrace (prefixWord ++ tailWord_7276950) baseStart_7276950 baseEnd_7276950 := by
    simpa [prefixWord, tailWord_7276950, baseEnd_7276950] using wordTrace_append hprefix tailTrace_7276950
  have hstable : (prefixWord ++ tailWord_7276950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276950).length < 2 ^ (prefixWord ++ tailWord_7276950).sum := by decide
  have hdescent : baseEnd_7276950 < baseStart_7276950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276965 : List Nat := [1, 3, 1, 2, 1, 1, 4, 2, 3, 2, 3]
def baseStart_7276965 : Nat := 118140960795 + 7276965 * 2 ^ 59
def prefixEnd_7276965 : Nat := 4983230072969 + 3 ^ 40 * 7276965 * 2
def baseEnd_7276965 : Nat := 3736580750945226574671353

theorem tailTrace_7276965 : CollatzResearch.WordTrace tailWord_7276965 prefixEnd_7276965 3736580750945226574671353 := by
  unfold tailWord_7276965
  simp only [CollatzResearch.WordTrace]
  refine ⟨265412718081806086522216349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176941812054537391014810899 265412718081806086522216349)
  ·
    refine ⟨99529769280677282445831131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265412718081806086522216349 99529769280677282445831131)
    ·
      refine ⟨149294653921015923668746697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99529769280677282445831131 149294653921015923668746697)
      ·
        refine ⟨111970990440761942751560023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149294653921015923668746697 111970990440761942751560023)
        ·
          refine ⟨167956485661142914127340035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111970990440761942751560023 167956485661142914127340035)
          ·
            refine ⟨251934728491714371191010053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167956485661142914127340035 251934728491714371191010053)
            ·
              refine ⟨47237761592196444598314385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 251934728491714371191010053 47237761592196444598314385)
              ·
                refine ⟨35428321194147333448735789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47237761592196444598314385 35428321194147333448735789)
                ·
                  refine ⟨13285620447805250043275921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35428321194147333448735789 13285620447805250043275921)
                  ·
                    refine ⟨9964215335853937532456941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13285620447805250043275921 9964215335853937532456941)
                    ·
                      refine ⟨3736580750945226574671353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9964215335853937532456941 3736580750945226574671353)
                      ·
                        rfl

theorem cell23_7276965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_7276965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276965 prefixEnd_7276965 := by exact prefixLift 7276965
  have htrace : WordTrace (prefixWord ++ tailWord_7276965) baseStart_7276965 baseEnd_7276965 := by
    simpa [prefixWord, tailWord_7276965, baseEnd_7276965] using wordTrace_append hprefix tailTrace_7276965
  have hstable : (prefixWord ++ tailWord_7276965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276965).length < 2 ^ (prefixWord ++ tailWord_7276965).sum := by decide
  have hdescent : baseEnd_7276965 < baseStart_7276965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276993 : List Nat := [1, 2, 7, 1, 1, 1, 3, 1, 1, 5]
def baseStart_7276993 : Nat := 118140960795 + 7276993 * 2 ^ 59
def prefixEnd_7276993 : Nat := 4983230072969 + 3 ^ 40 * 7276993 * 2
def baseEnd_7276993 : Nat := 1245531709467850821707075

theorem tailTrace_7276993 : CollatzResearch.WordTrace tailWord_7276993 prefixEnd_7276993 1245531709467850821707075 := by
  unfold tailWord_7276993
  simp only [CollatzResearch.WordTrace]
  refine ⟨265413739325704647304235633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176942492883803098202823755 265413739325704647304235633)
  ·
    refine ⟨199060304494278485478176725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265413739325704647304235633 199060304494278485478176725)
    ·
      refine ⟨4665475886584652003394767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 199060304494278485478176725 4665475886584652003394767)
      ·
        refine ⟨6998213829876978005092151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4665475886584652003394767 6998213829876978005092151)
        ·
          refine ⟨10497320744815467007638227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6998213829876978005092151 10497320744815467007638227)
          ·
            refine ⟨15745981117223200511457341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10497320744815467007638227 15745981117223200511457341)
            ·
              refine ⟨5904742918958700191796503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15745981117223200511457341 5904742918958700191796503)
              ·
                refine ⟨8857114378438050287694755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5904742918958700191796503 8857114378438050287694755)
                ·
                  refine ⟨13285671567657075431542133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8857114378438050287694755 13285671567657075431542133)
                  ·
                    refine ⟨1245531709467850821707075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13285671567657075431542133 1245531709467850821707075)
                    ·
                      rfl

theorem cell23_7276993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_7276993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276993 prefixEnd_7276993 := by exact prefixLift 7276993
  have htrace : WordTrace (prefixWord ++ tailWord_7276993) baseStart_7276993 baseEnd_7276993 := by
    simpa [prefixWord, tailWord_7276993, baseEnd_7276993] using wordTrace_append hprefix tailTrace_7276993
  have hstable : (prefixWord ++ tailWord_7276993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276993).length < 2 ^ (prefixWord ++ tailWord_7276993).sum := by decide
  have hdescent : baseEnd_7276993 < baseStart_7276993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276996 : List Nat := [2, 3, 3, 2, 2, 1, 3, 1, 1, 1, 4]
def baseStart_7276996 : Nat := 118140960795 + 7276996 * 2 ^ 59
def prefixEnd_7276996 : Nat := 4983230072969 + 3 ^ 40 * 7276996 * 2
def baseEnd_7276996 : Nat := 3736596668845515953383711

theorem tailTrace_7276996 : CollatzResearch.WordTrace tailWord_7276996 prefixEnd_7276996 3736596668845515953383711 := by
  unfold tailWord_7276996
  simp only [CollatzResearch.WordTrace]
  refine ⟨132706924372346889408297421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176942565829795852544396561 132706924372346889408297421)
  ·
    refine ⟨49765096639630083528111533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132706924372346889408297421 49765096639630083528111533)
    ·
      refine ⟨18661911239861281323041825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49765096639630083528111533 18661911239861281323041825)
      ·
        refine ⟨13996433429895960992281369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18661911239861281323041825 13996433429895960992281369)
        ·
          refine ⟨10497325072421970744211027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13996433429895960992281369 10497325072421970744211027)
          ·
            refine ⟨15745987608632956116316541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10497325072421970744211027 15745987608632956116316541)
            ·
              refine ⟨5904745353237358543618703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15745987608632956116316541 5904745353237358543618703)
              ·
                refine ⟨8857118029856037815428055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5904745353237358543618703 8857118029856037815428055)
                ·
                  refine ⟨13285677044784056723142083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8857118029856037815428055 13285677044784056723142083)
                  ·
                    refine ⟨19928515567176085084713125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13285677044784056723142083 19928515567176085084713125)
                    ·
                      refine ⟨3736596668845515953383711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19928515567176085084713125 3736596668845515953383711)
                      ·
                        rfl

theorem cell23_7276996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_7276996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276996 prefixEnd_7276996 := by exact prefixLift 7276996
  have htrace : WordTrace (prefixWord ++ tailWord_7276996) baseStart_7276996 baseEnd_7276996 := by
    simpa [prefixWord, tailWord_7276996, baseEnd_7276996] using wordTrace_append hprefix tailTrace_7276996
  have hstable : (prefixWord ++ tailWord_7276996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276996).length < 2 ^ (prefixWord ++ tailWord_7276996).sum := by decide
  have hdescent : baseEnd_7276996 < baseStart_7276996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276999 : List Nat := [1, 1, 4, 1, 1, 5, 3, 1, 1, 2, 3]
def baseStart_7276999 : Nat := 118140960795 + 7276999 * 2 ^ 59
def prefixEnd_7276999 : Nat := 4983230072969 + 3 ^ 40 * 7276999 * 2
def baseEnd_7276999 : Nat := 3736598209287479441646197

theorem tailTrace_7276999 : CollatzResearch.WordTrace tailWord_7276999 prefixEnd_7276999 3736598209287479441646197 := by
  unfold tailWord_7276999
  simp only [CollatzResearch.WordTrace]
  refine ⟨265413958163682910328954051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176942638775788606885969367 265413958163682910328954051)
  ·
    refine ⟨398120937245524365493431077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265413958163682910328954051 398120937245524365493431077)
    ·
      refine ⟨74647675733535818530018327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 398120937245524365493431077 74647675733535818530018327)
      ·
        refine ⟨111971513600303727795027491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74647675733535818530018327 111971513600303727795027491)
        ·
          refine ⟨167957270400455591692541237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111971513600303727795027491 167957270400455591692541237)
          ·
            refine ⟨15745994100042711721175741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 167957270400455591692541237 15745994100042711721175741)
            ·
              refine ⟨5904747787516016895440903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15745994100042711721175741 5904747787516016895440903)
              ·
                refine ⟨8857121681274025343161355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5904747787516016895440903 8857121681274025343161355)
                ·
                  refine ⟨13285682521911038014742033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8857121681274025343161355 13285682521911038014742033)
                  ·
                    refine ⟨9964261891433278511056525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13285682521911038014742033 9964261891433278511056525)
                    ·
                      refine ⟨3736598209287479441646197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9964261891433278511056525 3736598209287479441646197)
                      ·
                        rfl

theorem cell23_7276999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 1, 2, 3].length) (baseStart_7276999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276999 prefixEnd_7276999 := by exact prefixLift 7276999
  have htrace : WordTrace (prefixWord ++ tailWord_7276999) baseStart_7276999 baseEnd_7276999 := by
    simpa [prefixWord, tailWord_7276999, baseEnd_7276999] using wordTrace_append hprefix tailTrace_7276999
  have hstable : (prefixWord ++ tailWord_7276999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276999).length < 2 ^ (prefixWord ++ tailWord_7276999).sum := by decide
  have hdescent : baseEnd_7276999 < baseStart_7276999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277013 : List Nat := [1, 3, 2, 3, 1, 2, 4, 2, 1, 2, 2]
def baseStart_7277013 : Nat := 118140960795 + 7277013 * 2 ^ 59
def prefixEnd_7277013 : Nat := 4983230072969 + 3 ^ 40 * 7277013 * 2
def baseEnd_7277013 : Nat := 3736605398016642386871133

theorem tailTrace_7277013 : CollatzResearch.WordTrace tailWord_7277013 prefixEnd_7277013 3736605398016642386871133 := by
  unfold tailWord_7277013
  simp only [CollatzResearch.WordTrace]
  refine ⟨265414468785632190719963693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176942979190421460479975795 265414468785632190719963693)
  ·
    refine ⟨99530425794612071519986385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265414468785632190719963693 99530425794612071519986385)
    ·
      refine ⟨74647819345959053639989789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99530425794612071519986385 74647819345959053639989789)
      ·
        refine ⟨27992932254734645114996171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74647819345959053639989789 27992932254734645114996171)
        ·
          refine ⟨41989398382101967672494257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27992932254734645114996171 41989398382101967672494257)
          ·
            refine ⟨31492048786576475754370693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41989398382101967672494257 31492048786576475754370693)
            ·
              refine ⟨5904759147483089203944505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31492048786576475754370693 5904759147483089203944505)
              ·
                refine ⟨4428569360612316902958379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5904759147483089203944505 4428569360612316902958379)
                ·
                  refine ⟨6642854040918475354437569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4428569360612316902958379 6642854040918475354437569)
                  ·
                    refine ⟨4982140530688856515828177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6642854040918475354437569 4982140530688856515828177)
                    ·
                      refine ⟨3736605398016642386871133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4982140530688856515828177 3736605398016642386871133)
                      ·
                        rfl

theorem cell23_7277013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_7277013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277013 prefixEnd_7277013 := by exact prefixLift 7277013
  have htrace : WordTrace (prefixWord ++ tailWord_7277013) baseStart_7277013 baseEnd_7277013 := by
    simpa [prefixWord, tailWord_7277013, baseEnd_7277013] using wordTrace_append hprefix tailTrace_7277013
  have hstable : (prefixWord ++ tailWord_7277013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277013).length < 2 ^ (prefixWord ++ tailWord_7277013).sum := by decide
  have hdescent : baseEnd_7277013 < baseStart_7277013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277026 : List Nat := [3, 3, 3, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_7277026 : Nat := 118140960795 + 7277026 * 2 ^ 59
def prefixEnd_7277026 : Nat := 4983230072969 + 3 ^ 40 * 7277026 * 2
def baseEnd_7277026 : Nat := 3736612073265150836008573

theorem tailTrace_7277026 : CollatzResearch.WordTrace tailWord_7277026 prefixEnd_7277026 3736612073265150836008573 := by
  unfold tailWord_7277026
  simp only [CollatzResearch.WordTrace]
  refine ⟨66353735733646273485046733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176943295289723395960124621 66353735733646273485046733)
  ·
    refine ⟨24882650900117352556892525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66353735733646273485046733 24882650900117352556892525)
    ·
      refine ⟨9330994087544007208834697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24882650900117352556892525 9330994087544007208834697)
      ·
        refine ⟨6998245565658005406626023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9330994087544007208834697 6998245565658005406626023)
        ·
          refine ⟨10497368348487008109939035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6998245565658005406626023 10497368348487008109939035)
          ·
            refine ⟨15746052522730512164908553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10497368348487008109939035 15746052522730512164908553)
            ·
              refine ⟨11809539392047884123681415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15746052522730512164908553 11809539392047884123681415)
              ·
                refine ⟨17714309088071826185522123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11809539392047884123681415 17714309088071826185522123)
                ·
                  refine ⟨26571463632107739278283185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17714309088071826185522123 26571463632107739278283185)
                  ·
                    refine ⟨19928597724080804458712389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26571463632107739278283185 19928597724080804458712389)
                    ·
                      refine ⟨3736612073265150836008573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19928597724080804458712389 3736612073265150836008573)
                      ·
                        rfl

theorem cell23_7277026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_7277026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277026 prefixEnd_7277026 := by exact prefixLift 7277026
  have htrace : WordTrace (prefixWord ++ tailWord_7277026) baseStart_7277026 baseEnd_7277026 := by
    simpa [prefixWord, tailWord_7277026, baseEnd_7277026] using wordTrace_append hprefix tailTrace_7277026
  have hstable : (prefixWord ++ tailWord_7277026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277026).length < 2 ^ (prefixWord ++ tailWord_7277026).sum := by decide
  have hdescent : baseEnd_7277026 < baseStart_7277026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277029 : List Nat := [1, 3, 1, 5, 2, 1, 2, 1, 1, 3, 3]
def baseStart_7277029 : Nat := 118140960795 + 7277029 * 2 ^ 59
def prefixEnd_7277029 : Nat := 4983230072969 + 3 ^ 40 * 7277029 * 2
def baseEnd_7277029 : Nat := 3736613613707114324271059

theorem tailTrace_7277029 : CollatzResearch.WordTrace tailWord_7277029 prefixEnd_7277029 3736613613707114324271059 := by
  unfold tailWord_7277029
  simp only [CollatzResearch.WordTrace]
  refine ⟨265415052353574225452546141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176943368235716150301697427 265415052353574225452546141)
  ·
    refine ⟨99530644632590334544704803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265415052353574225452546141 99530644632590334544704803)
    ·
      refine ⟨149295966948885501817057205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99530644632590334544704803 149295966948885501817057205)
      ·
        refine ⟨13996496901458015795349113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149295966948885501817057205 13996496901458015795349113)
        ·
          refine ⟨10497372676093511846511835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13996496901458015795349113 10497372676093511846511835)
          ·
            refine ⟨15746059014140267769767753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10497372676093511846511835 15746059014140267769767753)
            ·
              refine ⟨11809544260605200827325815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15746059014140267769767753 11809544260605200827325815)
              ·
                refine ⟨17714316390907801240988723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11809544260605200827325815 17714316390907801240988723)
                ·
                  refine ⟨26571474586361701861483085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17714316390907801240988723 26571474586361701861483085)
                  ·
                    refine ⟨9964302969885638198056157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26571474586361701861483085 9964302969885638198056157)
                    ·
                      refine ⟨3736613613707114324271059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9964302969885638198056157 3736613613707114324271059)
                      ·
                        rfl

theorem cell23_7277029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_7277029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277029 prefixEnd_7277029 := by exact prefixLift 7277029
  have htrace : WordTrace (prefixWord ++ tailWord_7277029) baseStart_7277029 baseEnd_7277029 := by
    simpa [prefixWord, tailWord_7277029, baseEnd_7277029] using wordTrace_append hprefix tailTrace_7277029
  have hstable : (prefixWord ++ tailWord_7277029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277029).length < 2 ^ (prefixWord ++ tailWord_7277029).sum := by decide
  have hdescent : baseEnd_7277029 < baseStart_7277029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277063 : List Nat := [1, 1, 4, 3, 4, 1, 1, 2, 2, 1, 3]
def baseStart_7277063 : Nat := 118140960795 + 7277063 * 2 ^ 59
def prefixEnd_7277063 : Nat := 4983230072969 + 3 ^ 40 * 7277063 * 2
def baseEnd_7277063 : Nat := 3736631072049367191245903

theorem tailTrace_7277063 : CollatzResearch.WordTrace tailWord_7277063 prefixEnd_7277063 3736631072049367191245903 := by
  unfold tailWord_7277063
  simp only [CollatzResearch.WordTrace]
  refine ⟨265416292435451049259283843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176944194956967366172855895 265416292435451049259283843)
  ·
    refine ⟨398124438653176573888925765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265416292435451049259283843 398124438653176573888925765)
    ·
      refine ⟨74648332247470607604173581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 398124438653176573888925765 74648332247470607604173581)
      ·
        refine ⟨27993124592801477851565093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74648332247470607604173581 27993124592801477851565093)
        ·
          refine ⟨5248710861150277097168455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27993124592801477851565093 5248710861150277097168455)
          ·
            refine ⟨7873066291725415645752683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5248710861150277097168455 7873066291725415645752683)
            ·
              refine ⟨11809599437588123468629025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7873066291725415645752683 11809599437588123468629025)
              ·
                refine ⟨8857199578191092601471769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11809599437588123468629025 8857199578191092601471769)
                ·
                  refine ⟨6642899683643319451103827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8857199578191092601471769 6642899683643319451103827)
                  ·
                    refine ⟨9964349525464979176655741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6642899683643319451103827 9964349525464979176655741)
                    ·
                      refine ⟨3736631072049367191245903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9964349525464979176655741 3736631072049367191245903)
                      ·
                        rfl

theorem cell23_7277063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_7277063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277063 prefixEnd_7277063 := by exact prefixLift 7277063
  have htrace : WordTrace (prefixWord ++ tailWord_7277063) baseStart_7277063 baseEnd_7277063 := by
    simpa [prefixWord, tailWord_7277063, baseEnd_7277063] using wordTrace_append hprefix tailTrace_7277063
  have hstable : (prefixWord ++ tailWord_7277063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277063).length < 2 ^ (prefixWord ++ tailWord_7277063).sum := by decide
  have hdescent : baseEnd_7277063 < baseStart_7277063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277075 : List Nat := [1, 1, 1, 2, 1, 5, 4, 1, 7]
def baseStart_7277075 : Nat := 118140960795 + 7277075 * 2 ^ 59
def prefixEnd_7277075 : Nat := 4983230072969 + 3 ^ 40 * 7277075 * 2
def baseEnd_7277075 : Nat := 415181914868580127143983

theorem tailTrace_7277075 : CollatzResearch.WordTrace tailWord_7277075 prefixEnd_7277075 415181914868580127143983 := by
  unfold tailWord_7277075
  simp only [CollatzResearch.WordTrace]
  refine ⟨265416730111407575308720679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176944486740938383539147119 265416730111407575308720679)
  ·
    refine ⟨398125095167111362963081019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265416730111407575308720679 398125095167111362963081019)
    ·
      refine ⟨597187642750667044444621529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398125095167111362963081019 597187642750667044444621529)
      ·
        refine ⟨447890732063000283333466147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 597187642750667044444621529 447890732063000283333466147)
        ·
          refine ⟨671836098094500425000199221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447890732063000283333466147 671836098094500425000199221)
          ·
            refine ⟨62984634196359414843768677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 671836098094500425000199221 62984634196359414843768677)
            ·
              refine ⟨11809618911817390283206627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62984634196359414843768677 11809618911817390283206627)
              ·
                refine ⟨17714428367726085424809941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11809618911817390283206627 17714428367726085424809941)
                ·
                  refine ⟨415181914868580127143983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17714428367726085424809941 415181914868580127143983)
                  ·
                    rfl

theorem cell23_7277075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 7].length) (baseStart_7277075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277075 prefixEnd_7277075 := by exact prefixLift 7277075
  have htrace : WordTrace (prefixWord ++ tailWord_7277075) baseStart_7277075 baseEnd_7277075 := by
    simpa [prefixWord, tailWord_7277075, baseEnd_7277075] using wordTrace_append hprefix tailTrace_7277075
  have hstable : (prefixWord ++ tailWord_7277075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277075).length < 2 ^ (prefixWord ++ tailWord_7277075).sum := by decide
  have hdescent : baseEnd_7277075 < baseStart_7277075 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277105 : List Nat := [1, 2, 2, 3, 1, 1, 4, 1, 1, 7]
def baseStart_7277105 : Nat := 118140960795 + 7277105 * 2 ^ 59
def prefixEnd_7277105 : Nat := 4983230072969 + 3 ^ 40 * 7277105 * 2
def baseEnd_7277105 : Nat := 1245550879412285342306903

theorem tailTrace_7277105 : CollatzResearch.WordTrace tailWord_7277105 prefixEnd_7277105 1245550879412285342306903 := by
  unfold tailWord_7277105
  simp only [CollatzResearch.WordTrace]
  refine ⟨265417824301298890432312769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176945216200865926954875179 265417824301298890432312769)
  ·
    refine ⟨199063368225974167824234577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265417824301298890432312769 199063368225974167824234577)
    ·
      refine ⟨149297526169480625868175933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199063368225974167824234577 149297526169480625868175933)
      ·
        refine ⟨55986572313555234700565975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149297526169480625868175933 55986572313555234700565975)
        ·
          refine ⟨83979858470332852050848963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55986572313555234700565975 83979858470332852050848963)
          ·
            refine ⟨125969787705499278076273445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83979858470332852050848963 125969787705499278076273445)
            ·
              refine ⟨23619335194781114639301271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125969787705499278076273445 23619335194781114639301271)
              ·
                refine ⟨35429002792171671958951907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23619335194781114639301271 35429002792171671958951907)
                ·
                  refine ⟨53143504188257507938427861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35429002792171671958951907 53143504188257507938427861)
                  ·
                    refine ⟨1245550879412285342306903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53143504188257507938427861 1245550879412285342306903)
                    ·
                      rfl

theorem cell23_7277105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 7].length) (baseStart_7277105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277105 prefixEnd_7277105 := by exact prefixLift 7277105
  have htrace : WordTrace (prefixWord ++ tailWord_7277105) baseStart_7277105 baseEnd_7277105 := by
    simpa [prefixWord, tailWord_7277105, baseEnd_7277105] using wordTrace_append hprefix tailTrace_7277105
  have hstable : (prefixWord ++ tailWord_7277105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277105).length < 2 ^ (prefixWord ++ tailWord_7277105).sum := by decide
  have hdescent : baseEnd_7277105 < baseStart_7277105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277126 : List Nat := [6, 1, 1, 1, 2, 3, 1, 1, 7]
def baseStart_7277126 : Nat := 118140960795 + 7277126 * 2 ^ 59
def prefixEnd_7277126 : Nat := 4983230072969 + 3 ^ 40 * 7277126 * 2
def baseEnd_7277126 : Nat := 415184824592288938306457

theorem tailTrace_7277126 : CollatzResearch.WordTrace tailWord_7277126 prefixEnd_7277126 415184824592288938306457 := by
  unfold tailWord_7277126
  simp only [CollatzResearch.WordTrace]
  refine ⟨8294330944819462844338351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 176945726822815207345884821 8294330944819462844338351)
  ·
    refine ⟨12441496417229194266507527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8294330944819462844338351 12441496417229194266507527)
    ·
      refine ⟨18662244625843791399761291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12441496417229194266507527 18662244625843791399761291)
      ·
        refine ⟨27993366938765687099641937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18662244625843791399761291 27993366938765687099641937)
        ·
          refine ⟨20995025204074265324731453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27993366938765687099641937 20995025204074265324731453)
          ·
            refine ⟨7873134451527849496774295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20995025204074265324731453 7873134451527849496774295)
            ·
              refine ⟨11809701677291774245161443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7873134451527849496774295 11809701677291774245161443)
              ·
                refine ⟨17714552515937661367742165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11809701677291774245161443 17714552515937661367742165)
                ·
                  refine ⟨415184824592288938306457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17714552515937661367742165 415184824592288938306457)
                  ·
                    rfl

theorem cell23_7277126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_7277126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277126 prefixEnd_7277126 := by exact prefixLift 7277126
  have htrace : WordTrace (prefixWord ++ tailWord_7277126) baseStart_7277126 baseEnd_7277126 := by
    simpa [prefixWord, tailWord_7277126, baseEnd_7277126] using wordTrace_append hprefix tailTrace_7277126
  have hstable : (prefixWord ++ tailWord_7277126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277126).length < 2 ^ (prefixWord ++ tailWord_7277126).sum := by decide
  have hdescent : baseEnd_7277126 < baseStart_7277126 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277152 : List Nat := [2, 1, 1, 3, 2, 1, 2, 4, 3, 4]
def baseStart_7277152 : Nat := 118140960795 + 7277152 * 2 ^ 59
def prefixEnd_7277152 : Nat := 4983230072969 + 3 ^ 40 * 7277152 * 2
def baseEnd_7277152 : Nat := 1245558923942539114344331

theorem tailTrace_7277152 : CollatzResearch.WordTrace tailWord_7277152 prefixEnd_7277152 1245558923942539114344331 := by
  unfold tailWord_7277152
  simp only [CollatzResearch.WordTrace]
  refine ⟨132709769266064308729636855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176946359021419078306182473 132709769266064308729636855)
  ·
    refine ⟨199064653899096463094455283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132709769266064308729636855 199064653899096463094455283)
    ·
      refine ⟨298596980848644694641682925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199064653899096463094455283 298596980848644694641682925)
      ·
        refine ⟨111973867818241760490631097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298596980848644694641682925 111973867818241760490631097)
        ·
          refine ⟨83980400863681320367973323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111973867818241760490631097 83980400863681320367973323)
          ·
            refine ⟨125970601295521980551959985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83980400863681320367973323 125970601295521980551959985)
            ·
              refine ⟨94477950971641485413969989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125970601295521980551959985 94477950971641485413969989)
              ·
                refine ⟨17714615807182778515119373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94477950971641485413969989 17714615807182778515119373)
                ·
                  refine ⟨6642980927693541943169765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17714615807182778515119373 6642980927693541943169765)
                  ·
                    refine ⟨1245558923942539114344331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6642980927693541943169765 1245558923942539114344331)
                    ·
                      rfl

theorem cell23_7277152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 3, 4].length) (baseStart_7277152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277152 prefixEnd_7277152 := by exact prefixLift 7277152
  have htrace : WordTrace (prefixWord ++ tailWord_7277152) baseStart_7277152 baseEnd_7277152 := by
    simpa [prefixWord, tailWord_7277152, baseEnd_7277152] using wordTrace_append hprefix tailTrace_7277152
  have hstable : (prefixWord ++ tailWord_7277152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277152).length < 2 ^ (prefixWord ++ tailWord_7277152).sum := by decide
  have hdescent : baseEnd_7277152 < baseStart_7277152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277209 : List Nat := [1, 2, 1, 2, 1, 2, 5, 2, 3, 1, 3]
def baseStart_7277209 : Nat := 118140960795 + 7277209 * 2 ^ 59
def prefixEnd_7277209 : Nat := 4983230072969 + 3 ^ 40 * 7277209 * 2
def baseEnd_7277209 : Nat := 3736706040224923620020231

theorem tailTrace_7277209 : CollatzResearch.WordTrace tailWord_7277209 prefixEnd_7277209 3736706040224923620020231 := by
  unfold tailWord_7277209
  simp only [CollatzResearch.WordTrace]
  refine ⟨265421617492922116194098681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176947744995281410796065787 265421617492922116194098681)
  ·
    refine ⟨199066213119691587145574011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265421617492922116194098681 199066213119691587145574011)
    ·
      refine ⟨298599319679537380718361017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199066213119691587145574011 298599319679537380718361017)
      ·
        refine ⟨223949489759653035538770763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298599319679537380718361017 223949489759653035538770763)
        ·
          refine ⟨335924234639479553308156145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223949489759653035538770763 335924234639479553308156145)
          ·
            refine ⟨251943175979609664981117109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335924234639479553308156145 251943175979609664981117109)
            ·
              refine ⟨23619672748088406091979729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 251943175979609664981117109 23619672748088406091979729)
              ·
                refine ⟨17714754561066304568984797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23619672748088406091979729 17714754561066304568984797)
                ·
                  refine ⟨6643032960399864213369299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17714754561066304568984797 6643032960399864213369299)
                  ·
                    refine ⟨9964549440599796320053949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6643032960399864213369299 9964549440599796320053949)
                    ·
                      refine ⟨3736706040224923620020231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9964549440599796320053949 3736706040224923620020231)
                      ·
                        rfl

theorem cell23_7277209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 3, 1, 3].length) (baseStart_7277209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277209 prefixEnd_7277209 := by exact prefixLift 7277209
  have htrace : WordTrace (prefixWord ++ tailWord_7277209) baseStart_7277209 baseEnd_7277209 := by
    simpa [prefixWord, tailWord_7277209, baseEnd_7277209] using wordTrace_append hprefix tailTrace_7277209
  have hstable : (prefixWord ++ tailWord_7277209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277209).length < 2 ^ (prefixWord ++ tailWord_7277209).sum := by decide
  have hdescent : baseEnd_7277209 < baseStart_7277209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277219 : List Nat := [1, 1, 1, 4, 1, 1, 2, 5, 2, 3, 2]
def baseStart_7277219 : Nat := 118140960795 + 7277219 * 2 ^ 59
def prefixEnd_7277219 : Nat := 4983230072969 + 3 ^ 40 * 7277219 * 2
def baseEnd_7277219 : Nat := 3736711175031468580895185

theorem tailTrace_7277219 : CollatzResearch.WordTrace tailWord_7277219 prefixEnd_7277219 3736711175031468580895185 := by
  unfold tailWord_7277219
  simp only [CollatzResearch.WordTrace]
  refine ⟨265421982222885887901962711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176947988148590591934641807 265421982222885887901962711)
  ·
    refine ⟨398132973334328831852944067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265421982222885887901962711 398132973334328831852944067)
    ·
      refine ⟨597199460001493247779416101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398132973334328831852944067 597199460001493247779416101)
      ·
        refine ⟨111974898750279983958640519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 597199460001493247779416101 111974898750279983958640519)
        ·
          refine ⟨167962348125419975937960779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111974898750279983958640519 167962348125419975937960779)
          ·
            refine ⟨251943522188129963906941169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167962348125419975937960779 251943522188129963906941169)
            ·
              refine ⟨188957641641097472930205877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251943522188129963906941169 188957641641097472930205877)
              ·
                refine ⟨17714778903852888087206801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 188957641641097472930205877 17714778903852888087206801)
                ·
                  refine ⟨13286084177889666065405101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17714778903852888087206801 13286084177889666065405101)
                  ·
                    refine ⟨4982281566708624774526913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13286084177889666065405101 4982281566708624774526913)
                    ·
                      refine ⟨3736711175031468580895185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4982281566708624774526913 3736711175031468580895185)
                      ·
                        rfl

theorem cell23_7277219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 3, 2].length) (baseStart_7277219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277219 prefixEnd_7277219 := by exact prefixLift 7277219
  have htrace : WordTrace (prefixWord ++ tailWord_7277219) baseStart_7277219 baseEnd_7277219 := by
    simpa [prefixWord, tailWord_7277219, baseEnd_7277219] using wordTrace_append hprefix tailTrace_7277219
  have hstable : (prefixWord ++ tailWord_7277219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277219).length < 2 ^ (prefixWord ++ tailWord_7277219).sum := by decide
  have hdescent : baseEnd_7277219 < baseStart_7277219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277233 : List Nat := [1, 2, 2, 6, 2, 1, 1, 2, 6]
def baseStart_7277233 : Nat := 118140960795 + 7277233 * 2 ^ 59
def prefixEnd_7277233 : Nat := 4983230072969 + 3 ^ 40 * 7277233 * 2
def baseEnd_7277233 : Nat := 415190929306736836235569

theorem tailTrace_7277233 : CollatzResearch.WordTrace tailWord_7277233 prefixEnd_7277233 415190929306736836235569 := by
  unfold tailWord_7277233
  simp only [CollatzResearch.WordTrace]
  refine ⟨265422492844835168292972353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176948328563223445528648235 265422492844835168292972353)
  ·
    refine ⟨199066869633626376219729265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265422492844835168292972353 199066869633626376219729265)
    ·
      refine ⟨149300152225219782164796949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199066869633626376219729265 149300152225219782164796949)
      ·
        refine ⟨6998444635557177288974857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 149300152225219782164796949 6998444635557177288974857)
        ·
          refine ⟨5248833476667882966731143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6998444635557177288974857 5248833476667882966731143)
          ·
            refine ⟨7873250215001824450096715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5248833476667882966731143 7873250215001824450096715)
            ·
              refine ⟨11809875322502736675145073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7873250215001824450096715 11809875322502736675145073)
              ·
                refine ⟨8857406491877052506358805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11809875322502736675145073 8857406491877052506358805)
                ·
                  refine ⟨415190929306736836235569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8857406491877052506358805 415190929306736836235569)
                  ·
                    rfl

theorem cell23_7277233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 6].length) (baseStart_7277233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277233 prefixEnd_7277233 := by exact prefixLift 7277233
  have htrace : WordTrace (prefixWord ++ tailWord_7277233) baseStart_7277233 baseEnd_7277233 := by
    simpa [prefixWord, tailWord_7277233, baseEnd_7277233] using wordTrace_append hprefix tailTrace_7277233
  have hstable : (prefixWord ++ tailWord_7277233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277233).length < 2 ^ (prefixWord ++ tailWord_7277233).sum := by decide
  have hdescent : baseEnd_7277233 < baseStart_7277233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277272 : List Nat := [2, 1, 2, 2, 3, 3, 1, 9]
def baseStart_7277272 : Nat := 118140960795 + 7277272 * 2 ^ 59
def prefixEnd_7277272 : Nat := 4983230072969 + 3 ^ 40 * 7277272 * 2
def baseEnd_7277272 : Nat := 138397718129857661982683

theorem tailTrace_7277272 : CollatzResearch.WordTrace tailWord_7277272 prefixEnd_7277272 138397718129857661982683 := by
  unfold tailWord_7277272
  simp only [CollatzResearch.WordTrace]
  refine ⟨132711957645846938976821035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176949276861129251969094713 132711957645846938976821035)
  ·
    refine ⟨199067936468770408465231553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132711957645846938976821035 199067936468770408465231553)
    ·
      refine ⟨149300952351577806348923665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199067936468770408465231553 149300952351577806348923665)
      ·
        refine ⟨111975714263683354761692749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149300952351577806348923665 111975714263683354761692749)
        ·
          refine ⟨41990892848881258035634781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111975714263683354761692749 41990892848881258035634781)
          ·
            refine ⟨15746584818330471763363043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41990892848881258035634781 15746584818330471763363043)
            ·
              refine ⟨23619877227495707645044565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15746584818330471763363043 23619877227495707645044565)
              ·
                refine ⟨138397718129857661982683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23619877227495707645044565 138397718129857661982683)
                ·
                  rfl

theorem cell23_7277272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 9].length) (baseStart_7277272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277272 prefixEnd_7277272 := by exact prefixLift 7277272
  have htrace : WordTrace (prefixWord ++ tailWord_7277272) baseStart_7277272 baseEnd_7277272 := by
    simpa [prefixWord, tailWord_7277272, baseEnd_7277272] using wordTrace_append hprefix tailTrace_7277272
  have hstable : (prefixWord ++ tailWord_7277272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277272).length < 2 ^ (prefixWord ++ tailWord_7277272).sum := by decide
  have hdescent : baseEnd_7277272 < baseStart_7277272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277276 : List Nat := [2, 2, 5, 1, 1, 1, 1, 2, 4, 4]
def baseStart_7277276 : Nat := 118140960795 + 7277276 * 2 ^ 59
def prefixEnd_7277276 : Nat := 4983230072969 + 3 ^ 40 * 7277276 * 2
def baseEnd_7277276 : Nat := 1245580147809591619294141

theorem tailTrace_7277276 : CollatzResearch.WordTrace tailWord_7277276 prefixEnd_7277276 1245580147809591619294141 := by
  unfold tailWord_7277276
  simp only [CollatzResearch.WordTrace]
  refine ⟨132712030591839693318393841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176949374122452924424525121 132712030591839693318393841)
  ·
    refine ⟨99534022943879769988795381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132712030591839693318393841 99534022943879769988795381)
    ·
      refine ⟨9331314650988728436449567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99534022943879769988795381 9331314650988728436449567)
      ·
        refine ⟨13996971976483092654674351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9331314650988728436449567 13996971976483092654674351)
        ·
          refine ⟨20995457964724638982011527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13996971976483092654674351 20995457964724638982011527)
          ·
            refine ⟨31493186947086958473017291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20995457964724638982011527 31493186947086958473017291)
            ·
              refine ⟨47239780420630437709525937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31493186947086958473017291 47239780420630437709525937)
              ·
                refine ⟨35429835315472828282144453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47239780420630437709525937 35429835315472828282144453)
                ·
                  refine ⟨6643094121651155302902085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35429835315472828282144453 6643094121651155302902085)
                  ·
                    refine ⟨1245580147809591619294141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6643094121651155302902085 1245580147809591619294141)
                    ·
                      rfl

theorem cell23_7277276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_7277276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277276 prefixEnd_7277276 := by exact prefixLift 7277276
  have htrace : WordTrace (prefixWord ++ tailWord_7277276) baseStart_7277276 baseEnd_7277276 := by
    simpa [prefixWord, tailWord_7277276, baseEnd_7277276] using wordTrace_append hprefix tailTrace_7277276
  have hstable : (prefixWord ++ tailWord_7277276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277276).length < 2 ^ (prefixWord ++ tailWord_7277276).sum := by decide
  have hdescent : baseEnd_7277276 < baseStart_7277276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277310 : List Nat := [4, 2, 2, 1, 2, 3, 2, 1, 2, 4]
def baseStart_7277310 : Nat := 118140960795 + 7277310 * 2 ^ 59
def prefixEnd_7277310 : Nat := 4983230072969 + 3 ^ 40 * 7277310 * 2
def baseEnd_7277310 : Nat := 1245585967257009241619089

theorem tailTrace_7277310 : CollatzResearch.WordTrace tailWord_7277310 prefixEnd_7277310 1245585967257009241619089 := by
  unfold tailWord_7277310
  simp only [CollatzResearch.WordTrace]
  refine ⟨33178162658194526305440673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176950200843704140295683589 33178162658194526305440673)
  ·
    refine ⟨24883621993645894729080505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33178162658194526305440673 24883621993645894729080505)
    ·
      refine ⟨18662716495234421046810379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24883621993645894729080505 18662716495234421046810379)
      ·
        refine ⟨27994074742851631570215569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18662716495234421046810379 27994074742851631570215569)
        ·
          refine ⟨20995556057138723677661677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27994074742851631570215569 20995556057138723677661677)
          ·
            refine ⟨7873333521427021379123129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20995556057138723677661677 7873333521427021379123129)
            ·
              refine ⟨5905000141070266034342347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7873333521427021379123129 5905000141070266034342347)
              ·
                refine ⟨8857500211605399051513521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5905000141070266034342347 8857500211605399051513521)
                ·
                  refine ⟨6643125158704049288635141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8857500211605399051513521 6643125158704049288635141)
                  ·
                    refine ⟨1245585967257009241619089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6643125158704049288635141 1245585967257009241619089)
                    ·
                      rfl

theorem cell23_7277310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_7277310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277310 prefixEnd_7277310 := by exact prefixLift 7277310
  have htrace : WordTrace (prefixWord ++ tailWord_7277310) baseStart_7277310 baseEnd_7277310 := by
    simpa [prefixWord, tailWord_7277310, baseEnd_7277310] using wordTrace_append hprefix tailTrace_7277310
  have hstable : (prefixWord ++ tailWord_7277310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277310).length < 2 ^ (prefixWord ++ tailWord_7277310).sum := by decide
  have hdescent : baseEnd_7277310 < baseStart_7277310 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277469 : List Nat := [1, 4, 2, 1, 2, 1, 1, 3, 8]
def baseStart_7277469 : Nat := 118140960795 + 7277469 * 2 ^ 59
def prefixEnd_7277469 : Nat := 4983230072969 + 3 ^ 40 * 7277469 * 2
def baseEnd_7277469 : Nat := 415204393910565844752115

theorem tailTrace_7277469 : CollatzResearch.WordTrace tailWord_7277469 prefixEnd_7277469 415204393910565844752115 := by
  unfold tailWord_7277469
  simp only [CollatzResearch.WordTrace]
  refine ⟨265431100471980180598563461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176954066981320120399042307 265431100471980180598563461)
  ·
    refine ⟨49768331338496283862230649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265431100471980180598563461 49768331338496283862230649)
    ·
      refine ⟨37326248503872212896672987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49768331338496283862230649 37326248503872212896672987)
      ·
        refine ⟨55989372755808319345009481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37326248503872212896672987 55989372755808319345009481)
        ·
          refine ⟨41992029566856239508757111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55989372755808319345009481 41992029566856239508757111)
          ·
            refine ⟨62988044350284359263135667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41992029566856239508757111 62988044350284359263135667)
            ·
              refine ⟨94482066525426538894703501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62988044350284359263135667 94482066525426538894703501)
              ·
                refine ⟨35430774947034952085513813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94482066525426538894703501 35430774947034952085513813)
                ·
                  refine ⟨415204393910565844752115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35430774947034952085513813 415204393910565844752115)
                  ·
                    rfl

theorem cell23_7277469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 8].length) (baseStart_7277469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277469 prefixEnd_7277469 := by exact prefixLift 7277469
  have htrace : WordTrace (prefixWord ++ tailWord_7277469) baseStart_7277469 baseEnd_7277469 := by
    simpa [prefixWord, tailWord_7277469, baseEnd_7277469] using wordTrace_append hprefix tailTrace_7277469
  have hstable : (prefixWord ++ tailWord_7277469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277469).length < 2 ^ (prefixWord ++ tailWord_7277469).sum := by decide
  have hdescent : baseEnd_7277469 < baseStart_7277469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277473 : List Nat := [1, 2, 3, 4, 1, 1, 3, 1, 3, 4]
def baseStart_7277473 : Nat := 118140960795 + 7277473 * 2 ^ 59
def prefixEnd_7277473 : Nat := 4983230072969 + 3 ^ 40 * 7277473 * 2
def baseEnd_7277473 : Nat := 1245613866372570195706339

theorem tailTrace_7277473 : CollatzResearch.WordTrace tailWord_7277473 prefixEnd_7277473 1245613866372570195706339 := by
  unfold tailWord_7277473
  simp only [CollatzResearch.WordTrace]
  refine ⟨265431246363965689281709073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176954164242643792854472715 265431246363965689281709073)
  ·
    refine ⟨199073434772974266961281805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265431246363965689281709073 199073434772974266961281805)
    ·
      refine ⟨74652538039865350110480677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199073434772974266961281805 74652538039865350110480677)
      ·
        refine ⟨13997350882474753145715127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74652538039865350110480677 13997350882474753145715127)
        ·
          refine ⟨20996026323712129718572691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13997350882474753145715127 20996026323712129718572691)
          ·
            refine ⟨31494039485568194577859037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20996026323712129718572691 31494039485568194577859037)
            ·
              refine ⟨11810264807088072966697139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31494039485568194577859037 11810264807088072966697139)
              ·
                refine ⟨17715397210632109450045709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11810264807088072966697139 17715397210632109450045709)
                ·
                  refine ⟨6643273953987041043767141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17715397210632109450045709 6643273953987041043767141)
                  ·
                    refine ⟨1245613866372570195706339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6643273953987041043767141 1245613866372570195706339)
                    ·
                      rfl

theorem cell23_7277473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_7277473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277473 prefixEnd_7277473 := by exact prefixLift 7277473
  have htrace : WordTrace (prefixWord ++ tailWord_7277473) baseStart_7277473 baseEnd_7277473 := by
    simpa [prefixWord, tailWord_7277473, baseEnd_7277473] using wordTrace_append hprefix tailTrace_7277473
  have hstable : (prefixWord ++ tailWord_7277473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277473).length < 2 ^ (prefixWord ++ tailWord_7277473).sum := by decide
  have hdescent : baseEnd_7277473 < baseStart_7277473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277536 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 4, 6, 2]
def baseStart_7277536 : Nat := 118140960795 + 7277536 * 2 ^ 59
def prefixEnd_7277536 : Nat := 4983230072969 + 3 ^ 40 * 7277536 * 2
def baseEnd_7277536 : Nat := 3736873948398943840631227

theorem tailTrace_7277536 : CollatzResearch.WordTrace tailWord_7277536 prefixEnd_7277536 3736873948398943840631227 := by
  unfold tailWord_7277536
  simp only [CollatzResearch.WordTrace]
  refine ⟨132716772081368725520626231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176955696108491634027501641 132716772081368725520626231)
  ·
    refine ⟨199075158122053088280939347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132716772081368725520626231 199075158122053088280939347)
    ·
      refine ⟨298612737183079632421409021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199075158122053088280939347 298612737183079632421409021)
      ·
        refine ⟨111979776443654862158028383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298612737183079632421409021 111979776443654862158028383)
        ·
          refine ⟨167969664665482293237042575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111979776443654862158028383 167969664665482293237042575)
          ·
            refine ⟨251954496998223439855563863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167969664665482293237042575 251954496998223439855563863)
            ·
              refine ⟨377931745497335159783345795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251954496998223439855563863 377931745497335159783345795)
              ·
                refine ⟨566897618246002739675018693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377931745497335159783345795 566897618246002739675018693)
                ·
                  refine ⟨106293303421125513689066005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 566897618246002739675018693 106293303421125513689066005)
                  ·
                    refine ⟨4982498597865258454174969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106293303421125513689066005 4982498597865258454174969)
                    ·
                      refine ⟨3736873948398943840631227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4982498597865258454174969 3736873948398943840631227)
                      ·
                        rfl

theorem cell23_7277536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 4, 6, 2].length) (baseStart_7277536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277536 prefixEnd_7277536 := by exact prefixLift 7277536
  have htrace : WordTrace (prefixWord ++ tailWord_7277536) baseStart_7277536 baseEnd_7277536 := by
    simpa [prefixWord, tailWord_7277536, baseEnd_7277536] using wordTrace_append hprefix tailTrace_7277536
  have hstable : (prefixWord ++ tailWord_7277536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277536).length < 2 ^ (prefixWord ++ tailWord_7277536).sum := by decide
  have hdescent : baseEnd_7277536 < baseStart_7277536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277546 : List Nat := [3, 1, 3, 1, 2, 2, 1, 3, 1, 6]
def baseStart_7277546 : Nat := 118140960795 + 7277546 * 2 ^ 59
def prefixEnd_7277546 : Nat := 4983230072969 + 3 ^ 40 * 7277546 * 2
def baseEnd_7277546 : Nat := 1245626361068496267168727

theorem tailTrace_7277546 : CollatzResearch.WordTrace tailWord_7277546 prefixEnd_7277546 1245626361068496267168727 := by
  unfold tailWord_7277546
  simp only [CollatzResearch.WordTrace]
  refine ⟨66358477223175305687279123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176955939261800815166077661 66358477223175305687279123)
  ·
    refine ⟨99537715834762958530918685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66358477223175305687279123 99537715834762958530918685)
    ·
      refine ⟨37326643438036109449094507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99537715834762958530918685 37326643438036109449094507)
      ·
        refine ⟨55989965157054164173641761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37326643438036109449094507 55989965157054164173641761)
        ·
          refine ⟨41992473867790623130231321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55989965157054164173641761 41992473867790623130231321)
          ·
            refine ⟨31494355400842967347673491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41992473867790623130231321 31494355400842967347673491)
            ·
              refine ⟨47241533101264451021510237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31494355400842967347673491 47241533101264451021510237)
              ·
                refine ⟨17715574912974169133066339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47241533101264451021510237 17715574912974169133066339)
                ·
                  refine ⟨26573362369461253699599509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17715574912974169133066339 26573362369461253699599509)
                  ·
                    refine ⟨1245626361068496267168727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26573362369461253699599509 1245626361068496267168727)
                    ·
                      rfl

theorem cell23_7277546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_7277546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277546 prefixEnd_7277546 := by exact prefixLift 7277546
  have htrace : WordTrace (prefixWord ++ tailWord_7277546) baseStart_7277546 baseEnd_7277546 := by
    simpa [prefixWord, tailWord_7277546, baseEnd_7277546] using wordTrace_append hprefix tailTrace_7277546
  have hstable : (prefixWord ++ tailWord_7277546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277546).length < 2 ^ (prefixWord ++ tailWord_7277546).sum := by decide
  have hdescent : baseEnd_7277546 < baseStart_7277546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277557 : List Nat := [1, 3, 5, 2, 1, 1, 1, 1, 1, 5, 2]
def baseStart_7277557 : Nat := 118140960795 + 7277557 * 2 ^ 59
def prefixEnd_7277557 : Nat := 4983230072969 + 3 ^ 40 * 7277557 * 2
def baseEnd_7277557 : Nat := 3736884731492688258468631

theorem tailTrace_7277557 : CollatzResearch.WordTrace tailWord_7277557 prefixEnd_7277557 3736884731492688258468631 := by
  unfold tailWord_7277557
  simp only [CollatzResearch.WordTrace]
  refine ⟨265434310095661371627766925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176956206730440914418511283 265434310095661371627766925)
  ·
    refine ⟨99537866285873014360412597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265434310095661371627766925 99537866285873014360412597)
    ·
      refine ⟨9331674964300595096288681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99537866285873014360412597 9331674964300595096288681)
      ·
        refine ⟨6998756223225446322216511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9331674964300595096288681 6998756223225446322216511)
        ·
          refine ⟨10498134334838169483324767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6998756223225446322216511 10498134334838169483324767)
          ·
            refine ⟨15747201502257254224987151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10498134334838169483324767 15747201502257254224987151)
            ·
              refine ⟨23620802253385881337480727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15747201502257254224987151 23620802253385881337480727)
              ·
                refine ⟨35431203380078822006221091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23620802253385881337480727 35431203380078822006221091)
                ·
                  refine ⟨53146805070118233009331637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35431203380078822006221091 53146805070118233009331637)
                  ·
                    refine ⟨4982512975323584344624841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53146805070118233009331637 4982512975323584344624841)
                    ·
                      refine ⟨3736884731492688258468631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4982512975323584344624841 3736884731492688258468631)
                      ·
                        rfl

theorem cell23_7277557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_7277557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277557 prefixEnd_7277557 := by exact prefixLift 7277557
  have htrace : WordTrace (prefixWord ++ tailWord_7277557) baseStart_7277557 baseEnd_7277557 := by
    simpa [prefixWord, tailWord_7277557, baseEnd_7277557] using wordTrace_append hprefix tailTrace_7277557
  have hstable : (prefixWord ++ tailWord_7277557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277557).length < 2 ^ (prefixWord ++ tailWord_7277557).sum := by decide
  have hdescent : baseEnd_7277557 < baseStart_7277557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277573 : List Nat := [1, 3, 1, 1, 2, 3, 3, 3, 1, 2, 3]
def baseStart_7277573 : Nat := 118140960795 + 7277573 * 2 ^ 59
def prefixEnd_7277573 : Nat := 4983230072969 + 3 ^ 40 * 7277573 * 2
def baseEnd_7277573 : Nat := 3736892947183160195868557

theorem tailTrace_7277573 : CollatzResearch.WordTrace tailWord_7277573 prefixEnd_7277573 3736892947183160195868557 := by
  unfold tailWord_7277573
  simp only [CollatzResearch.WordTrace]
  refine ⟨265434893663603406360349373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176956595775735604240232915 265434893663603406360349373)
  ·
    refine ⟨99538085123851277385131015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265434893663603406360349373 99538085123851277385131015)
    ·
      refine ⟨149307127685776916077696523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99538085123851277385131015 149307127685776916077696523)
      ·
        refine ⟨223960691528665374116544785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149307127685776916077696523 223960691528665374116544785)
        ·
          refine ⟨167970518646499030587408589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223960691528665374116544785 167970518646499030587408589)
          ·
            refine ⟨62988944492437136470278221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167970518646499030587408589 62988944492437136470278221)
            ·
              refine ⟨23620854184663926176354333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62988944492437136470278221 23620854184663926176354333)
              ·
                refine ⟨8857820319248972316132875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23620854184663926176354333 8857820319248972316132875)
                ·
                  refine ⟨13286730478873458474199313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8857820319248972316132875 13286730478873458474199313)
                  ·
                    refine ⟨9965047859155093855649485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13286730478873458474199313 9965047859155093855649485)
                    ·
                      refine ⟨3736892947183160195868557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9965047859155093855649485 3736892947183160195868557)
                      ·
                        rfl

theorem cell23_7277573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 2, 3].length) (baseStart_7277573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277573 prefixEnd_7277573 := by exact prefixLift 7277573
  have htrace : WordTrace (prefixWord ++ tailWord_7277573) baseStart_7277573 baseEnd_7277573 := by
    simpa [prefixWord, tailWord_7277573, baseEnd_7277573] using wordTrace_append hprefix tailTrace_7277573
  have hstable : (prefixWord ++ tailWord_7277573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277573).length < 2 ^ (prefixWord ++ tailWord_7277573).sum := by decide
  have hdescent : baseEnd_7277573 < baseStart_7277573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277580 : List Nat := [2, 2, 1, 2, 3, 4, 1, 2, 2, 4]
def baseStart_7277580 : Nat := 118140960795 + 7277580 * 2 ^ 59
def prefixEnd_7277580 : Nat := 4983230072969 + 3 ^ 40 * 7277580 * 2
def baseEnd_7277580 : Nat := 1245632180515913889493675

theorem tailTrace_7277580 : CollatzResearch.WordTrace tailWord_7277580 prefixEnd_7277580 1245632180515913889493675 := by
  unfold tailWord_7277580
  simp only [CollatzResearch.WordTrace]
  refine ⟨132717574487289023277927097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176956765983052031037236129 132717574487289023277927097)
  ·
    refine ⟨99538180865466767458445323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132717574487289023277927097 99538180865466767458445323)
    ·
      refine ⟨149307271298200151187667985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99538180865466767458445323 149307271298200151187667985)
      ·
        refine ⟨111980453473650113390750989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149307271298200151187667985 111980453473650113390750989)
        ·
          refine ⟨41992670052618792521531621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111980453473650113390750989 41992670052618792521531621)
          ·
            refine ⟨7873625634866023597787179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41992670052618792521531621 7873625634866023597787179)
            ·
              refine ⟨11810438452299035396680769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7873625634866023597787179 11810438452299035396680769)
              ·
                refine ⟨8857828839224276547510577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11810438452299035396680769 8857828839224276547510577)
                ·
                  refine ⟨6643371629418207410632933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8857828839224276547510577 6643371629418207410632933)
                  ·
                    refine ⟨1245632180515913889493675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6643371629418207410632933 1245632180515913889493675)
                    ·
                      rfl

theorem cell23_7277580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 2, 4].length) (baseStart_7277580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277580 prefixEnd_7277580 := by exact prefixLift 7277580
  have htrace : WordTrace (prefixWord ++ tailWord_7277580) baseStart_7277580 baseEnd_7277580 := by
    simpa [prefixWord, tailWord_7277580, baseEnd_7277580] using wordTrace_append hprefix tailTrace_7277580
  have hstable : (prefixWord ++ tailWord_7277580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277580).length < 2 ^ (prefixWord ++ tailWord_7277580).sum := by decide
  have hdescent : baseEnd_7277580 < baseStart_7277580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277597 : List Nat := [1, 4, 2, 2, 3, 1, 3, 1, 2, 4]
def baseStart_7277597 : Nat := 118140960795 + 7277597 * 2 ^ 59
def prefixEnd_7277597 : Nat := 4983230072969 + 3 ^ 40 * 7277597 * 2
def baseEnd_7277597 : Nat := 1245635090239622700656149

theorem tailTrace_7277597 : CollatzResearch.WordTrace tailWord_7277597 prefixEnd_7277597 1245635090239622700656149 := by
  unfold tailWord_7277597
  simp only [CollatzResearch.WordTrace]
  refine ⟨265435769015516458459223045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176957179343677638972815363 265435769015516458459223045)
  ·
    refine ⟨49769206690409335961104321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265435769015516458459223045 49769206690409335961104321)
    ·
      refine ⟨37326905017807001970828241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49769206690409335961104321 37326905017807001970828241)
      ·
        refine ⟨27995178763355251478121181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37326905017807001970828241 27995178763355251478121181)
        ·
          refine ⟨10498192036258219304295443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27995178763355251478121181 10498192036258219304295443)
          ·
            refine ⟨15747288054387328956443165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10498192036258219304295443 15747288054387328956443165)
            ·
              refine ⟨5905233020395248358666187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15747288054387328956443165 5905233020395248358666187)
              ·
                refine ⟨8857849530592872537999281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5905233020395248358666187 8857849530592872537999281)
                ·
                  refine ⟨6643387147944654403499461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8857849530592872537999281 6643387147944654403499461)
                  ·
                    refine ⟨1245635090239622700656149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6643387147944654403499461 1245635090239622700656149)
                    ·
                      rfl

theorem cell23_7277597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_7277597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277597 prefixEnd_7277597 := by exact prefixLift 7277597
  have htrace : WordTrace (prefixWord ++ tailWord_7277597) baseStart_7277597 baseEnd_7277597 := by
    simpa [prefixWord, tailWord_7277597, baseEnd_7277597] using wordTrace_append hprefix tailTrace_7277597
  have hstable : (prefixWord ++ tailWord_7277597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277597).length < 2 ^ (prefixWord ++ tailWord_7277597).sum := by decide
  have hdescent : baseEnd_7277597 < baseStart_7277597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277603 : List Nat := [1, 1, 1, 4, 3, 2, 3, 1, 1, 3, 3]
def baseStart_7277603 : Nat := 118140960795 + 7277603 * 2 ^ 59
def prefixEnd_7277603 : Nat := 4983230072969 + 3 ^ 40 * 7277603 * 2
def baseEnd_7277603 : Nat := 3736908351602795078493419

theorem tailTrace_7277603 : CollatzResearch.WordTrace tailWord_7277603 prefixEnd_7277603 3736908351602795078493419 := by
  unfold tailWord_7277603
  simp only [CollatzResearch.WordTrace]
  refine ⟨265435987853494721483941463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176957325235663147655960975 265435987853494721483941463)
  ·
    refine ⟨398153981780242082225912195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265435987853494721483941463 398153981780242082225912195)
    ·
      refine ⟨597230972670363123338868293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398153981780242082225912195 597230972670363123338868293)
      ·
        refine ⟨111980807375693085626037805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 597230972670363123338868293 111980807375693085626037805)
        ·
          refine ⟨41992802765884907109764177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111980807375693085626037805 41992802765884907109764177)
          ·
            refine ⟨31494602074413680332323133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41992802765884907109764177 31494602074413680332323133)
            ·
              refine ⟨11810475777905130124621175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31494602074413680332323133 11810475777905130124621175)
              ·
                refine ⟨17715713666857695186931763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11810475777905130124621175 17715713666857695186931763)
                ·
                  refine ⟨26573570500286542780397645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17715713666857695186931763 26573570500286542780397645)
                  ·
                    refine ⟨9965088937607453542649117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26573570500286542780397645 9965088937607453542649117)
                    ·
                      refine ⟨3736908351602795078493419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9965088937607453542649117 3736908351602795078493419)
                      ·
                        rfl

theorem cell23_7277603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_7277603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277603 prefixEnd_7277603 := by exact prefixLift 7277603
  have htrace : WordTrace (prefixWord ++ tailWord_7277603) baseStart_7277603 baseEnd_7277603 := by
    simpa [prefixWord, tailWord_7277603, baseEnd_7277603] using wordTrace_append hprefix tailTrace_7277603
  have hstable : (prefixWord ++ tailWord_7277603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277603).length < 2 ^ (prefixWord ++ tailWord_7277603).sum := by decide
  have hdescent : baseEnd_7277603 < baseStart_7277603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277607 : List Nat := [1, 1, 7, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_7277607 : Nat := 118140960795 + 7277607 * 2 ^ 59
def prefixEnd_7277607 : Nat := 4983230072969 + 3 ^ 40 * 7277607 * 2
def baseEnd_7277607 : Nat := 3736910405525413062843401

theorem tailTrace_7277607 : CollatzResearch.WordTrace tailWord_7277607 prefixEnd_7277607 3736910405525413062843401 := by
  unfold tailWord_7277607
  simp only [CollatzResearch.WordTrace]
  refine ⟨265436133745480230167087075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176957422496986820111391383 265436133745480230167087075)
  ·
    refine ⟨398154200618220345250630613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265436133745480230167087075 398154200618220345250630613)
    ·
      refine ⟨9331739076989539341811655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 398154200618220345250630613 9331739076989539341811655)
      ·
        refine ⟨13997608615484309012717483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9331739076989539341811655 13997608615484309012717483)
        ·
          refine ⟨20996412923226463519076225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13997608615484309012717483 20996412923226463519076225)
          ·
            refine ⟨15747309692419847639307169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20996412923226463519076225 15747309692419847639307169)
            ·
              refine ⟨11810482269314885729480377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15747309692419847639307169 11810482269314885729480377)
              ·
                refine ⟨8857861701986164297110283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11810482269314885729480377 8857861701986164297110283)
                ·
                  refine ⟨13286792552979246445665425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8857861701986164297110283 13286792552979246445665425)
                  ·
                    refine ⟨9965094414734434834249069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13286792552979246445665425 9965094414734434834249069)
                    ·
                      refine ⟨3736910405525413062843401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9965094414734434834249069 3736910405525413062843401)
                      ·
                        rfl

theorem cell23_7277607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_7277607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277607 prefixEnd_7277607 := by exact prefixLift 7277607
  have htrace : WordTrace (prefixWord ++ tailWord_7277607) baseStart_7277607 baseEnd_7277607 := by
    simpa [prefixWord, tailWord_7277607, baseEnd_7277607] using wordTrace_append hprefix tailTrace_7277607
  have hstable : (prefixWord ++ tailWord_7277607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277607).length < 2 ^ (prefixWord ++ tailWord_7277607).sum := by decide
  have hdescent : baseEnd_7277607 < baseStart_7277607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277610 : List Nat := [3, 1, 4, 1, 3, 2, 2, 7]
def baseStart_7277610 : Nat := 118140960795 + 7277610 * 2 ^ 59
def prefixEnd_7277610 : Nat := 4983230072969 + 3 ^ 40 * 7277610 * 2
def baseEnd_7277610 : Nat := 138404146146939872263181

theorem tailTrace_7277610 : CollatzResearch.WordTrace tailWord_7277610 prefixEnd_7277610 138404146146939872263181 := by
  unfold tailWord_7277610
  simp only [CollatzResearch.WordTrace]
  refine ⟨66359060791117340419861571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176957495442979574452964189 66359060791117340419861571)
  ·
    refine ⟨99538591186676010629792357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66359060791117340419861571 99538591186676010629792357)
    ·
      refine ⟨18663485847501751993086067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99538591186676010629792357 18663485847501751993086067)
      ·
        refine ⟨27995228771252627989629101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18663485847501751993086067 27995228771252627989629101)
        ·
          refine ⟨10498210789219735496110913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27995228771252627989629101 10498210789219735496110913)
          ·
            refine ⟨7873658091914801622083185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10498210789219735496110913 7873658091914801622083185)
            ·
              refine ⟨5905243568936101216562389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7873658091914801622083185 5905243568936101216562389)
              ·
                refine ⟨138404146146939872263181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5905243568936101216562389 138404146146939872263181)
                ·
                  rfl

theorem cell23_7277610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 7].length) (baseStart_7277610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277610 prefixEnd_7277610 := by exact prefixLift 7277610
  have htrace : WordTrace (prefixWord ++ tailWord_7277610) baseStart_7277610 baseEnd_7277610 := by
    simpa [prefixWord, tailWord_7277610, baseEnd_7277610] using wordTrace_append hprefix tailTrace_7277610
  have hstable : (prefixWord ++ tailWord_7277610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277610).length < 2 ^ (prefixWord ++ tailWord_7277610).sum := by decide
  have hdescent : baseEnd_7277610 < baseStart_7277610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277638 : List Nat := [6, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2]
def baseStart_7277638 : Nat := 118140960795 + 7277638 * 2 ^ 59
def prefixEnd_7277638 : Nat := 4983230072969 + 3 ^ 40 * 7277638 * 2
def baseEnd_7277638 : Nat := 3736926323425702441555759

theorem tailTrace_7277638 : CollatzResearch.WordTrace tailWord_7277638 prefixEnd_7277638 3736926323425702441555759 := by
  unfold tailWord_7277638
  simp only [CollatzResearch.WordTrace]
  refine ⟨8294914512761497576920799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 176958176272245281640977045 8294914512761497576920799)
  ·
    refine ⟨12442371769142246365381199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8294914512761497576920799 12442371769142246365381199)
    ·
      refine ⟨18663557653713369548071799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12442371769142246365381199 18663557653713369548071799)
      ·
        refine ⟨27995336480570054322107699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18663557653713369548071799 27995336480570054322107699)
        ·
          refine ⟨41993004720855081483161549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27995336480570054322107699 41993004720855081483161549)
          ·
            refine ⟨15747376770320655556185581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41993004720855081483161549 15747376770320655556185581)
            ·
              refine ⟨5905266288870245833569593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15747376770320655556185581 5905266288870245833569593)
              ·
                refine ⟨4428949716652684375177195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5905266288870245833569593 4428949716652684375177195)
                ·
                  refine ⟨6643424574979026562765793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4428949716652684375177195 6643424574979026562765793)
                  ·
                    refine ⟨4982568431234269922074345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6643424574979026562765793 4982568431234269922074345)
                    ·
                      refine ⟨3736926323425702441555759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4982568431234269922074345 3736926323425702441555759)
                      ·
                        rfl

theorem cell23_7277638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_7277638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277638 prefixEnd_7277638 := by exact prefixLift 7277638
  have htrace : WordTrace (prefixWord ++ tailWord_7277638) baseStart_7277638 baseEnd_7277638 := by
    simpa [prefixWord, tailWord_7277638, baseEnd_7277638] using wordTrace_append hprefix tailTrace_7277638
  have hstable : (prefixWord ++ tailWord_7277638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277638).length < 2 ^ (prefixWord ++ tailWord_7277638).sum := by decide
  have hdescent : baseEnd_7277638 < baseStart_7277638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277646 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5]
def baseStart_7277646 : Nat := 118140960795 + 7277646 * 2 ^ 59
def prefixEnd_7277646 : Nat := 4983230072969 + 3 ^ 40 * 7277646 * 2
def baseEnd_7277646 : Nat := 3736930431270938410255721

theorem tailTrace_7277646 : CollatzResearch.WordTrace tailWord_7277646 prefixEnd_7277646 3736930431270938410255721 := by
  unfold tailWord_7277646
  simp only [CollatzResearch.WordTrace]
  refine ⟨33179694524042367478469599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176958370794892626551837861 33179694524042367478469599)
  ·
    refine ⟨49769541786063551217704399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33179694524042367478469599 49769541786063551217704399)
    ·
      refine ⟨74654312679095326826556599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49769541786063551217704399 74654312679095326826556599)
      ·
        refine ⟨111981469018642990239834899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74654312679095326826556599 111981469018642990239834899)
        ·
          refine ⟨167972203527964485359752349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111981469018642990239834899 167972203527964485359752349)
          ·
            refine ⟨62989576322986682009907131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167972203527964485359752349 62989576322986682009907131)
            ·
              refine ⟨94484364484480023014860697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62989576322986682009907131 94484364484480023014860697)
              ·
                refine ⟨70863273363360017261145523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94484364484480023014860697 70863273363360017261145523)
                ·
                  refine ⟨106294910045040025891718285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70863273363360017261145523 106294910045040025891718285)
                  ·
                    refine ⟨39860591266890009709394357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106294910045040025891718285 39860591266890009709394357)
                    ·
                      refine ⟨3736930431270938410255721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39860591266890009709394357 3736930431270938410255721)
                      ·
                        rfl

theorem cell23_7277646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_7277646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277646 prefixEnd_7277646 := by exact prefixLift 7277646
  have htrace : WordTrace (prefixWord ++ tailWord_7277646) baseStart_7277646 baseEnd_7277646 := by
    simpa [prefixWord, tailWord_7277646, baseEnd_7277646] using wordTrace_append hprefix tailTrace_7277646
  have hstable : (prefixWord ++ tailWord_7277646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277646).length < 2 ^ (prefixWord ++ tailWord_7277646).sum := by decide
  have hdescent : baseEnd_7277646 < baseStart_7277646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277656 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 1, 4, 4]
def baseStart_7277656 : Nat := 118140960795 + 7277656 * 2 ^ 59
def prefixEnd_7277656 : Nat := 4983230072969 + 3 ^ 40 * 7277656 * 2
def baseEnd_7277656 : Nat := 3736935566077483371130675

theorem tailTrace_7277656 : CollatzResearch.WordTrace tailWord_7277656 prefixEnd_7277656 3736935566077483371130675 := by
  unfold tailWord_7277656
  simp only [CollatzResearch.WordTrace]
  refine ⟨132718960461151355767810411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176958613948201807690413881 132718960461151355767810411)
  ·
    refine ⟨199078440691727033651715617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132718960461151355767810411 199078440691727033651715617)
    ·
      refine ⟨149308830518795275238786713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199078440691727033651715617 149308830518795275238786713)
      ·
        refine ⟨111981622889096456429090035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149308830518795275238786713 111981622889096456429090035)
        ·
          refine ⟨167972434333644684643635053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111981622889096456429090035 167972434333644684643635053)
          ·
            refine ⟨62989662875116756741363145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167972434333644684643635053 62989662875116756741363145)
            ·
              refine ⟨47242247156337567556022359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62989662875116756741363145 47242247156337567556022359)
              ·
                refine ⟨70863370734506351334033539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47242247156337567556022359 70863370734506351334033539)
                ·
                  refine ⟨106295056101759527001050309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70863370734506351334033539 106295056101759527001050309)
                  ·
                    refine ⟨19930323019079911312696933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106295056101759527001050309 19930323019079911312696933)
                    ·
                      refine ⟨3736935566077483371130675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19930323019079911312696933 3736935566077483371130675)
                      ·
                        rfl

theorem cell23_7277656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_7277656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277656 prefixEnd_7277656 := by exact prefixLift 7277656
  have htrace : WordTrace (prefixWord ++ tailWord_7277656) baseStart_7277656 baseEnd_7277656 := by
    simpa [prefixWord, tailWord_7277656, baseEnd_7277656] using wordTrace_append hprefix tailTrace_7277656
  have hstable : (prefixWord ++ tailWord_7277656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277656).length < 2 ^ (prefixWord ++ tailWord_7277656).sum := by decide
  have hdescent : baseEnd_7277656 < baseStart_7277656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277660 : List Nat := [2, 2, 4, 1, 1, 1, 2, 3, 1, 4, 2]
def baseStart_7277660 : Nat := 118140960795 + 7277660 * 2 ^ 59
def prefixEnd_7277660 : Nat := 4983230072969 + 3 ^ 40 * 7277660 * 2
def baseEnd_7277660 : Nat := 3736937620000101355480657

theorem tailTrace_7277660 : CollatzResearch.WordTrace tailWord_7277660 prefixEnd_7277660 3736937620000101355480657 := by
  unfold tailWord_7277660
  simp only [CollatzResearch.WordTrace]
  refine ⟨132719033407144110109383217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176958711209525480145844289 132719033407144110109383217)
  ·
    refine ⟨99539275055358082582037413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132719033407144110109383217 99539275055358082582037413)
    ·
      refine ⟨18663614072879640484132015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99539275055358082582037413 18663614072879640484132015)
      ·
        refine ⟨27995421109319460726198023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18663614072879640484132015 27995421109319460726198023)
        ·
          refine ⟨41993131663979191089297035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27995421109319460726198023 41993131663979191089297035)
          ·
            refine ⟨62989697495968786633945553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41993131663979191089297035 62989697495968786633945553)
            ·
              refine ⟨47242273121976589975459165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62989697495968786633945553 47242273121976589975459165)
              ·
                refine ⟨17715852420741221240797187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47242273121976589975459165 17715852420741221240797187)
                ·
                  refine ⟨26573778631111831861195781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17715852420741221240797187 26573778631111831861195781)
                  ·
                    refine ⟨4982583493333468473974209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26573778631111831861195781 4982583493333468473974209)
                    ·
                      refine ⟨3736937620000101355480657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4982583493333468473974209 3736937620000101355480657)
                      ·
                        rfl

theorem cell23_7277660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_7277660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277660 prefixEnd_7277660 := by exact prefixLift 7277660
  have htrace : WordTrace (prefixWord ++ tailWord_7277660) baseStart_7277660 baseEnd_7277660 := by
    simpa [prefixWord, tailWord_7277660, baseEnd_7277660] using wordTrace_append hprefix tailTrace_7277660
  have hstable : (prefixWord ++ tailWord_7277660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277660).length < 2 ^ (prefixWord ++ tailWord_7277660).sum := by decide
  have hdescent : baseEnd_7277660 < baseStart_7277660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277693 : List Nat := [1, 4, 1, 1, 3, 1, 2, 2, 2, 3, 3]
def baseStart_7277693 : Nat := 118140960795 + 7277693 * 2 ^ 59
def prefixEnd_7277693 : Nat := 4983230072969 + 3 ^ 40 * 7277693 * 2
def baseEnd_7277693 : Nat := 3736954564861699726368005

theorem tailTrace_7277693 : CollatzResearch.WordTrace tailWord_7277693 prefixEnd_7277693 3736954564861699726368005 := by
  unfold tailWord_7277693
  simp only [CollatzResearch.WordTrace]
  refine ⟨265439270423168666854717733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176959513615445777903145155 265439270423168666854717733)
  ·
    refine ⟨49769863204344125035259575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265439270423168666854717733 49769863204344125035259575)
    ·
      refine ⟨74654794806516187552889363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49769863204344125035259575 74654794806516187552889363)
      ·
        refine ⟨111982192209774281329334045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74654794806516187552889363 111982192209774281329334045)
        ·
          refine ⟨41993322078665355498500267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111982192209774281329334045 41993322078665355498500267)
          ·
            refine ⟨62989983117998033247750401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41993322078665355498500267 62989983117998033247750401)
            ·
              refine ⟨47242487338498524935812801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62989983117998033247750401 47242487338498524935812801)
              ·
                refine ⟨35431865503873893701859601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47242487338498524935812801 35431865503873893701859601)
                ·
                  refine ⟨26573899127905420276394701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35431865503873893701859601 26573899127905420276394701)
                  ·
                    refine ⟨9965212172964532603648013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26573899127905420276394701 9965212172964532603648013)
                    ·
                      refine ⟨3736954564861699726368005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9965212172964532603648013 3736954564861699726368005)
                      ·
                        rfl

theorem cell23_7277693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_7277693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277693 prefixEnd_7277693 := by exact prefixLift 7277693
  have htrace : WordTrace (prefixWord ++ tailWord_7277693) baseStart_7277693 baseEnd_7277693 := by
    simpa [prefixWord, tailWord_7277693, baseEnd_7277693] using wordTrace_append hprefix tailTrace_7277693
  have hstable : (prefixWord ++ tailWord_7277693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277693).length < 2 ^ (prefixWord ++ tailWord_7277693).sum := by decide
  have hdescent : baseEnd_7277693 < baseStart_7277693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277700 : List Nat := [2, 3, 2, 1, 2, 3, 1, 4, 5]
def baseStart_7277700 : Nat := 118140960795 + 7277700 * 2 ^ 59
def prefixEnd_7277700 : Nat := 4983230072969 + 3 ^ 40 * 7277700 * 2
def baseEnd_7277700 : Nat := 415217573247364577664497

theorem tailTrace_7277700 : CollatzResearch.WordTrace tailWord_7277700 prefixEnd_7277700 415217573247364577664497 := by
  unfold tailWord_7277700
  simp only [CollatzResearch.WordTrace]
  refine ⟨132719762867071653525111277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176959683822762204700148369 132719762867071653525111277)
  ·
    refine ⟨49769911075151870071916729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132719762867071653525111277 49769911075151870071916729)
    ·
      refine ⟨37327433306363902553937547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49769911075151870071916729 37327433306363902553937547)
      ·
        refine ⟨55991149959545853830906321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37327433306363902553937547 55991149959545853830906321)
        ·
          refine ⟨41993362469659390373179741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55991149959545853830906321 41993362469659390373179741)
          ·
            refine ⟨15747510926122271389942403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41993362469659390373179741 15747510926122271389942403)
            ·
              refine ⟨23621266389183407084913605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15747510926122271389942403 23621266389183407084913605)
              ·
                refine ⟨4428987447971888828421301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23621266389183407084913605 4428987447971888828421301)
                ·
                  refine ⟨415217573247364577664497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4428987447971888828421301 415217573247364577664497)
                  ·
                    rfl

theorem cell23_7277700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 4, 5].length) (baseStart_7277700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277700 prefixEnd_7277700 := by exact prefixLift 7277700
  have htrace : WordTrace (prefixWord ++ tailWord_7277700) baseStart_7277700 baseEnd_7277700 := by
    simpa [prefixWord, tailWord_7277700, baseEnd_7277700] using wordTrace_append hprefix tailTrace_7277700
  have hstable : (prefixWord ++ tailWord_7277700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277700).length < 2 ^ (prefixWord ++ tailWord_7277700).sum := by decide
  have hdescent : baseEnd_7277700 < baseStart_7277700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277710 : List Nat := [4, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3]
def baseStart_7277710 : Nat := 118140960795 + 7277710 * 2 ^ 59
def prefixEnd_7277710 : Nat := 4983230072969 + 3 ^ 40 * 7277710 * 2
def baseEnd_7277710 : Nat := 3736963294032826159855427

theorem tailTrace_7277710 : CollatzResearch.WordTrace tailWord_7277710 prefixEnd_7277710 3736963294032826159855427 := by
  unfold tailWord_7277710
  simp only [CollatzResearch.WordTrace]
  refine ⟨33179986308013384844760823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176959926976071385838724389 33179986308013384844760823)
  ·
    refine ⟨49769979462020077267141235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33179986308013384844760823 49769979462020077267141235)
    ·
      refine ⟨74654969193030115900711853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49769979462020077267141235 74654969193030115900711853)
      ·
        refine ⟨27995613447386293462766945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74654969193030115900711853 27995613447386293462766945)
        ·
          refine ⟨20996710085539720097075209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27995613447386293462766945 20996710085539720097075209)
          ·
            refine ⟨15747532564154790072806407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20996710085539720097075209 15747532564154790072806407)
            ·
              refine ⟨23621298846232185109209611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15747532564154790072806407 23621298846232185109209611)
              ·
                refine ⟨35431948269348277663814417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23621298846232185109209611 35431948269348277663814417)
                ·
                  refine ⟨26573961202011208247860813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35431948269348277663814417 26573961202011208247860813)
                  ·
                    refine ⟨9965235450754203092947805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26573961202011208247860813 9965235450754203092947805)
                    ·
                      refine ⟨3736963294032826159855427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9965235450754203092947805 3736963294032826159855427)
                      ·
                        rfl

theorem cell23_7277710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_7277710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277710 prefixEnd_7277710 := by exact prefixLift 7277710
  have htrace : WordTrace (prefixWord ++ tailWord_7277710) baseStart_7277710 baseEnd_7277710 := by
    simpa [prefixWord, tailWord_7277710, baseEnd_7277710] using wordTrace_append hprefix tailTrace_7277710
  have hstable : (prefixWord ++ tailWord_7277710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277710).length < 2 ^ (prefixWord ++ tailWord_7277710).sum := by decide
  have hdescent : baseEnd_7277710 < baseStart_7277710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277730 : List Nat := [3, 3, 1, 3, 2, 1, 1, 1, 1, 7]
def baseStart_7277730 : Nat := 118140960795 + 7277730 * 2 ^ 59
def prefixEnd_7277730 : Nat := 4983230072969 + 3 ^ 40 * 7277730 * 2
def baseEnd_7277730 : Nat := 1245657854548638693868445

theorem tailTrace_7277730 : CollatzResearch.WordTrace tailWord_7277730 prefixEnd_7277730 1245657854548638693868445 := by
  unfold tailWord_7277730
  simp only [CollatzResearch.WordTrace]
  refine ⟨66360154981008655543453661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176960413282689748115876429 66360154981008655543453661)
  ·
    refine ⟨24885058117878245828795123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66360154981008655543453661 24885058117878245828795123)
    ·
      refine ⟨37327587176817368743192685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24885058117878245828795123 37327587176817368743192685)
      ·
        refine ⟨13997845191306513278697257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37327587176817368743192685 13997845191306513278697257)
        ·
          refine ⟨10498383893479884959022943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13997845191306513278697257 10498383893479884959022943)
          ·
            refine ⟨15747575840219827438534415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10498383893479884959022943 15747575840219827438534415)
            ·
              refine ⟨23621363760329741157801623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15747575840219827438534415 23621363760329741157801623)
              ·
                refine ⟨35432045640494611736702435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23621363760329741157801623 35432045640494611736702435)
                ·
                  refine ⟨53148068460741917605053653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35432045640494611736702435 53148068460741917605053653)
                  ·
                    refine ⟨1245657854548638693868445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53148068460741917605053653 1245657854548638693868445)
                    ·
                      rfl

theorem cell23_7277730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_7277730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277730 prefixEnd_7277730 := by exact prefixLift 7277730
  have htrace : WordTrace (prefixWord ++ tailWord_7277730) baseStart_7277730 baseEnd_7277730 := by
    simpa [prefixWord, tailWord_7277730, baseEnd_7277730] using wordTrace_append hprefix tailTrace_7277730
  have hstable : (prefixWord ++ tailWord_7277730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277730).length < 2 ^ (prefixWord ++ tailWord_7277730).sum := by decide
  have hdescent : baseEnd_7277730 < baseStart_7277730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277733 : List Nat := [1, 3, 1, 2, 1, 5, 1, 1, 1, 3, 4]
def baseStart_7277733 : Nat := 118140960795 + 7277733 * 2 ^ 59
def prefixEnd_7277733 : Nat := 4983230072969 + 3 ^ 40 * 7277733 * 2
def baseEnd_7277733 : Nat := 3736975104087879569867821

theorem tailTrace_7277733 : CollatzResearch.WordTrace tailWord_7277733 prefixEnd_7277733 3736975104087879569867821 := by
  unfold tailWord_7277733
  simp only [CollatzResearch.WordTrace]
  refine ⟨265440729343023753686173853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176960486228682502457449235 265440729343023753686173853)
  ·
    refine ⟨99540273503633907632315195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265440729343023753686173853 99540273503633907632315195)
    ·
      refine ⟨149310410255450861448472793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99540273503633907632315195 149310410255450861448472793)
      ·
        refine ⟨111982807691588146086354595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149310410255450861448472793 111982807691588146086354595)
        ·
          refine ⟨167974211537382219129531893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111982807691588146086354595 167974211537382219129531893)
          ·
            refine ⟨15747582331629583043393615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 167974211537382219129531893 15747582331629583043393615)
            ·
              refine ⟨23621373497444374565090423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15747582331629583043393615 23621373497444374565090423)
              ·
                refine ⟨35432060246166561847635635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23621373497444374565090423 35432060246166561847635635)
                ·
                  refine ⟨53148090369249842771453453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35432060246166561847635635 53148090369249842771453453)
                  ·
                    refine ⟨19930533888468691039295045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53148090369249842771453453 19930533888468691039295045)
                    ·
                      refine ⟨3736975104087879569867821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19930533888468691039295045 3736975104087879569867821)
                      ·
                        rfl

theorem cell23_7277733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_7277733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277733 prefixEnd_7277733 := by exact prefixLift 7277733
  have htrace : WordTrace (prefixWord ++ tailWord_7277733) baseStart_7277733 baseEnd_7277733 := by
    simpa [prefixWord, tailWord_7277733, baseEnd_7277733] using wordTrace_append hprefix tailTrace_7277733
  have hstable : (prefixWord ++ tailWord_7277733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277733).length < 2 ^ (prefixWord ++ tailWord_7277733).sum := by decide
  have hdescent : baseEnd_7277733 < baseStart_7277733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277833 : List Nat := [1, 2, 1, 1, 3, 3, 2, 3, 1, 6]
def baseStart_7277833 : Nat := 118140960795 + 7277833 * 2 ^ 59
def prefixEnd_7277833 : Nat := 4983230072969 + 3 ^ 40 * 7277833 * 2
def baseEnd_7277833 : Nat := 1245675484051109726205787

theorem tailTrace_7277833 : CollatzResearch.WordTrace tailWord_7277833 prefixEnd_7277833 1245675484051109726205787 := by
  unfold tailWord_7277833
  simp only [CollatzResearch.WordTrace]
  refine ⟨265444376642661470764814153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176962917761774313843209435 265444376642661470764814153)
  ·
    refine ⟨199083282481996103073610615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265444376642661470764814153 199083282481996103073610615)
    ·
      refine ⟨298624923722994154610415923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199083282481996103073610615 298624923722994154610415923)
      ·
        refine ⟨447937385584491231915623885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298624923722994154610415923 447937385584491231915623885)
        ·
          refine ⟨167976519594184211968358957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 447937385584491231915623885 167976519594184211968358957)
          ·
            refine ⟨62991194847819079488134609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167976519594184211968358957 62991194847819079488134609)
            ·
              refine ⟨47243396135864309616100957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62991194847819079488134609 47243396135864309616100957)
              ·
                refine ⟨17716273550949116106037859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47243396135864309616100957 17716273550949116106037859)
                ·
                  refine ⟨26574410326423674159056789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17716273550949116106037859 26574410326423674159056789)
                  ·
                    refine ⟨1245675484051109726205787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26574410326423674159056789 1245675484051109726205787)
                    ·
                      rfl

theorem cell23_7277833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 6].length) (baseStart_7277833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277833 prefixEnd_7277833 := by exact prefixLift 7277833
  have htrace : WordTrace (prefixWord ++ tailWord_7277833) baseStart_7277833 baseEnd_7277833 := by
    simpa [prefixWord, tailWord_7277833, baseEnd_7277833] using wordTrace_append hprefix tailTrace_7277833
  have hstable : (prefixWord ++ tailWord_7277833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277833).length < 2 ^ (prefixWord ++ tailWord_7277833).sum := by decide
  have hdescent : baseEnd_7277833 < baseStart_7277833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277850 : List Nat := [3, 1, 1, 3, 3, 2, 1, 2, 1, 6]
def baseStart_7277850 : Nat := 118140960795 + 7277850 * 2 ^ 59
def prefixEnd_7277850 : Nat := 4983230072969 + 3 ^ 40 * 7277850 * 2
def baseEnd_7277850 : Nat := 1245678393774818537368261

theorem tailTrace_7277850 : CollatzResearch.WordTrace tailWord_7277850 prefixEnd_7277850 1245678393774818537368261 := by
  unfold tailWord_7277850
  simp only [CollatzResearch.WordTrace]
  refine ⟨66361249170899970667045751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176963331122399921778788669 66361249170899970667045751)
  ·
    refine ⟨99541873756349956000568627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66361249170899970667045751 99541873756349956000568627)
    ·
      refine ⟨149312810634524934000852941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99541873756349956000568627 149312810634524934000852941)
      ·
        refine ⟨55992303987946850250319853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149312810634524934000852941 55992303987946850250319853)
        ·
          refine ⟨20997113995480068843869945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55992303987946850250319853 20997113995480068843869945)
          ·
            refine ⟨15747835496610051632902459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20997113995480068843869945 15747835496610051632902459)
            ·
              refine ⟨23621753244915077449353689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15747835496610051632902459 23621753244915077449353689)
              ·
                refine ⟨17716314933686308087015267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23621753244915077449353689 17716314933686308087015267)
                ·
                  refine ⟨26574472400529462130522901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17716314933686308087015267 26574472400529462130522901)
                  ·
                    refine ⟨1245678393774818537368261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26574472400529462130522901 1245678393774818537368261)
                    ·
                      rfl

theorem cell23_7277850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 1, 6].length) (baseStart_7277850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277850 prefixEnd_7277850 := by exact prefixLift 7277850
  have htrace : WordTrace (prefixWord ++ tailWord_7277850) baseStart_7277850 baseEnd_7277850 := by
    simpa [prefixWord, tailWord_7277850, baseEnd_7277850] using wordTrace_append hprefix tailTrace_7277850
  have hstable : (prefixWord ++ tailWord_7277850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277850).length < 2 ^ (prefixWord ++ tailWord_7277850).sum := by decide
  have hdescent : baseEnd_7277850 < baseStart_7277850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277924 : List Nat := [2, 3, 1, 1, 3, 2, 3, 2, 2, 1, 3]
def baseStart_7277924 : Nat := 118140960795 + 7277924 * 2 ^ 59
def prefixEnd_7277924 : Nat := 4983230072969 + 3 ^ 40 * 7277924 * 2
def baseEnd_7277924 : Nat := 3737073178892888322579443

theorem tailTrace_7277924 : CollatzResearch.WordTrace tailWord_7277924 prefixEnd_7277924 3737073178892888322579443 := by
  unfold tailWord_7277924
  simp only [CollatzResearch.WordTrace]
  refine ⟨132723847842665896653188413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176965130456887862204251217 132723847842665896653188413)
  ·
    refine ⟨49771442940999711244945655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132723847842665896653188413 49771442940999711244945655)
    ·
      refine ⟨74657164411499566867418483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49771442940999711244945655 74657164411499566867418483)
      ·
        refine ⟨111985746617249350301127725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74657164411499566867418483 111985746617249350301127725)
        ·
          refine ⟨41994654981468506362922897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111985746617249350301127725 41994654981468506362922897)
          ·
            refine ⟨31495991236101379772192173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41994654981468506362922897 31495991236101379772192173)
            ·
              refine ⟨11810996713538017414572065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31495991236101379772192173 11810996713538017414572065)
              ·
                refine ⟨8858247535153513060929049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11810996713538017414572065 8858247535153513060929049)
                ·
                  refine ⟨6643685651365134795696787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8858247535153513060929049 6643685651365134795696787)
                  ·
                    refine ⟨9965528477047702193545181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6643685651365134795696787 9965528477047702193545181)
                    ·
                      refine ⟨3737073178892888322579443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9965528477047702193545181 3737073178892888322579443)
                      ·
                        rfl

theorem cell23_7277924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_7277924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277924 prefixEnd_7277924 := by exact prefixLift 7277924
  have htrace : WordTrace (prefixWord ++ tailWord_7277924) baseStart_7277924 baseEnd_7277924 := by
    simpa [prefixWord, tailWord_7277924, baseEnd_7277924] using wordTrace_append hprefix tailTrace_7277924
  have hstable : (prefixWord ++ tailWord_7277924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277924).length < 2 ^ (prefixWord ++ tailWord_7277924).sum := by decide
  have hdescent : baseEnd_7277924 < baseStart_7277924 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7277941 : List Nat := [1, 3, 4, 1, 4, 1, 1, 1, 1, 3, 3]
def baseStart_7277941 : Nat := 118140960795 + 7277941 * 2 ^ 59
def prefixEnd_7277941 : Nat := 4983230072969 + 3 ^ 40 * 7277941 * 2
def baseEnd_7277941 : Nat := 3737081908064014756066865

theorem tailTrace_7277941 : CollatzResearch.WordTrace tailWord_7277941 prefixEnd_7277941 3737081908064014756066865 := by
  unfold tailWord_7277941
  simp only [CollatzResearch.WordTrace]
  refine ⟨265448315726270205209745677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176965543817513470139830451 265448315726270205209745677)
  ·
    refine ⟨99543118397351326953654629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265448315726270205209745677 99543118397351326953654629)
    ·
      refine ⟨18664334699503373803810243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99543118397351326953654629 18664334699503373803810243)
      ·
        refine ⟨27996502049255060705715365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18664334699503373803810243 27996502049255060705715365)
        ·
          refine ⟨5249344134235323882321631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27996502049255060705715365 5249344134235323882321631)
          ·
            refine ⟨7874016201352985823482447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5249344134235323882321631 7874016201352985823482447)
            ·
              refine ⟨11811024302029478735223671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7874016201352985823482447 11811024302029478735223671)
              ·
                refine ⟨17716536453044218102835507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11811024302029478735223671 17716536453044218102835507)
                ·
                  refine ⟨26574804679566327154253261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17716536453044218102835507 26574804679566327154253261)
                  ·
                    refine ⟨9965551754837372682844973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26574804679566327154253261 9965551754837372682844973)
                    ·
                      refine ⟨3737081908064014756066865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9965551754837372682844973 3737081908064014756066865)
                      ·
                        rfl

theorem cell23_7277941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_7277941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7277941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7277941 prefixEnd_7277941 := by exact prefixLift 7277941
  have htrace : WordTrace (prefixWord ++ tailWord_7277941) baseStart_7277941 baseEnd_7277941 := by
    simpa [prefixWord, tailWord_7277941, baseEnd_7277941] using wordTrace_append hprefix tailTrace_7277941
  have hstable : (prefixWord ++ tailWord_7277941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7277941).length < 2 ^ (prefixWord ++ tailWord_7277941).sum := by decide
  have hdescent : baseEnd_7277941 < baseStart_7277941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7277941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278037 : List Nat := [1, 3, 2, 3, 1, 1, 1, 4, 2, 1, 4]
def baseStart_7278037 : Nat := 118140960795 + 7278037 * 2 ^ 59
def prefixEnd_7278037 : Nat := 4983230072969 + 3 ^ 40 * 7278037 * 2
def baseEnd_7278037 : Nat := 3737131202206846380466423

theorem tailTrace_7278037 : CollatzResearch.WordTrace tailWord_7278037 prefixEnd_7278037 3737131202206846380466423 := by
  unfold tailWord_7278037
  simp only [CollatzResearch.WordTrace]
  refine ⟨265451817133922413605240365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176967878089281609070160243 265451817133922413605240365)
  ·
    refine ⟨99544431425220905101965137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265451817133922413605240365 99544431425220905101965137)
    ·
      refine ⟨74658323568915678826473853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99544431425220905101965137 74658323568915678826473853)
      ·
        refine ⟨27996871338343379559927695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74658323568915678826473853 27996871338343379559927695)
        ·
          refine ⟨41995307007515069339891543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27996871338343379559927695 41995307007515069339891543)
          ·
            refine ⟨62992960511272604009837315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41995307007515069339891543 62992960511272604009837315)
            ·
              refine ⟨94489440766908906014755973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62992960511272604009837315 94489440766908906014755973)
              ·
                refine ⟨17716770143795419877766745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94489440766908906014755973 17716770143795419877766745)
                ·
                  refine ⟨13287577607846564908325059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17716770143795419877766745 13287577607846564908325059)
                  ·
                    refine ⟨19931366411769847362487589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13287577607846564908325059 19931366411769847362487589)
                    ·
                      refine ⟨3737131202206846380466423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19931366411769847362487589 3737131202206846380466423)
                      ·
                        rfl

theorem cell23_7278037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_7278037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278037 prefixEnd_7278037 := by exact prefixLift 7278037
  have htrace : WordTrace (prefixWord ++ tailWord_7278037) baseStart_7278037 baseEnd_7278037 := by
    simpa [prefixWord, tailWord_7278037, baseEnd_7278037] using wordTrace_append hprefix tailTrace_7278037
  have hstable : (prefixWord ++ tailWord_7278037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278037).length < 2 ^ (prefixWord ++ tailWord_7278037).sum := by decide
  have hdescent : baseEnd_7278037 < baseStart_7278037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278038 : List Nat := [5, 2, 1, 1, 1, 4, 2, 2, 5]
def baseStart_7278038 : Nat := 118140960795 + 7278038 * 2 ^ 59
def prefixEnd_7278038 : Nat := 4983230072969 + 3 ^ 40 * 7278038 * 2
def baseEnd_7278038 : Nat := 415236857298611208505991

theorem tailTrace_7278038 : CollatzResearch.WordTrace tailWord_7278038 prefixEnd_7278038 415236857298611208505991 := by
  unfold tailWord_7278038
  simp only [CollatzResearch.WordTrace]
  refine ⟨16590740850432424423501673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176967902404612527184017845 16590740850432424423501673)
  ·
    refine ⟨12443055637824318317626255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16590740850432424423501673 12443055637824318317626255)
    ·
      refine ⟨18664583456736477476439383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12443055637824318317626255 18664583456736477476439383)
      ·
        refine ⟨27996875185104716214659075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18664583456736477476439383 27996875185104716214659075)
        ·
          refine ⟨41995312777657074321988613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27996875185104716214659075 41995312777657074321988613)
          ·
            refine ⟨7874121145810701435372865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41995312777657074321988613 7874121145810701435372865)
            ·
              refine ⟨5905590859358026076529649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7874121145810701435372865 5905590859358026076529649)
              ·
                refine ⟨4429193144518519557397237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5905590859358026076529649 4429193144518519557397237)
                ·
                  refine ⟨415236857298611208505991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4429193144518519557397237 415236857298611208505991)
                  ·
                    rfl

theorem cell23_7278038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_7278038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278038 prefixEnd_7278038 := by exact prefixLift 7278038
  have htrace : WordTrace (prefixWord ++ tailWord_7278038) baseStart_7278038 baseEnd_7278038 := by
    simpa [prefixWord, tailWord_7278038, baseEnd_7278038] using wordTrace_append hprefix tailTrace_7278038
  have hstable : (prefixWord ++ tailWord_7278038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278038).length < 2 ^ (prefixWord ++ tailWord_7278038).sum := by decide
  have hdescent : baseEnd_7278038 < baseStart_7278038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278047 : List Nat := [1, 1, 2, 3, 3, 1, 2, 3, 3, 4]
def baseStart_7278047 : Nat := 118140960795 + 7278047 * 2 ^ 59
def prefixEnd_7278047 : Nat := 4983230072969 + 3 ^ 40 * 7278047 * 2
def baseEnd_7278047 : Nat := 1245712112337797113780459

theorem tailTrace_7278047 : CollatzResearch.WordTrace tailWord_7278047 prefixEnd_7278047 1245712112337797113780459 := by
  unfold tailWord_7278047
  simp only [CollatzResearch.WordTrace]
  refine ⟨265452181863886185313104395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176968121242590790208736263 265452181863886185313104395)
  ·
    refine ⟨398178272795829277969656593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265452181863886185313104395 398178272795829277969656593)
    ·
      refine ⟨298633704596871958477242445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398178272795829277969656593 298633704596871958477242445)
      ·
        refine ⟨111987639223826984428965917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298633704596871958477242445 111987639223826984428965917)
        ·
          refine ⟨41995364708935119160862219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111987639223826984428965917 41995364708935119160862219)
          ·
            refine ⟨62993047063402678741293329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41995364708935119160862219 62993047063402678741293329)
            ·
              refine ⟨47244785297552009055969997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62993047063402678741293329 47244785297552009055969997)
              ·
                refine ⟨17716794486582003395988749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47244785297552009055969997 17716794486582003395988749)
                ·
                  refine ⟨6643797932468251273495781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17716794486582003395988749 6643797932468251273495781)
                  ·
                    refine ⟨1245712112337797113780459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6643797932468251273495781 1245712112337797113780459)
                    ·
                      rfl

theorem cell23_7278047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 3, 4].length) (baseStart_7278047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278047 prefixEnd_7278047 := by exact prefixLift 7278047
  have htrace : WordTrace (prefixWord ++ tailWord_7278047) baseStart_7278047 baseEnd_7278047 := by
    simpa [prefixWord, tailWord_7278047, baseEnd_7278047] using wordTrace_append hprefix tailTrace_7278047
  have hstable : (prefixWord ++ tailWord_7278047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278047).length < 2 ^ (prefixWord ++ tailWord_7278047).sum := by decide
  have hdescent : baseEnd_7278047 < baseStart_7278047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278114 : List Nat := [3, 3, 1, 1, 1, 1, 3, 2, 1, 5, 2]
def baseStart_7278114 : Nat := 118140960795 + 7278114 * 2 ^ 59
def prefixEnd_7278114 : Nat := 4983230072969 + 3 ^ 40 * 7278114 * 2
def baseEnd_7278114 : Nat := 3737170740217242579203569

theorem tailTrace_7278114 : CollatzResearch.WordTrace tailWord_7278114 prefixEnd_7278114 3737170740217242579203569 := by
  unfold tailWord_7278114
  simp only [CollatzResearch.WordTrace]
  refine ⟨66363656388660863938948349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176969750369762303837195597 66363656388660863938948349)
  ·
    refine ⟨24886371145747823977105631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66363656388660863938948349 24886371145747823977105631)
    ·
      refine ⟨37329556718621735965658447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24886371145747823977105631 37329556718621735965658447)
      ·
        refine ⟨55994335077932603948487671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37329556718621735965658447 55994335077932603948487671)
        ·
          refine ⟨83991502616898905922731507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55994335077932603948487671 83991502616898905922731507)
          ·
            refine ⟨125987253925348358884097261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83991502616898905922731507 125987253925348358884097261)
            ·
              refine ⟨47245220222005634581536473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125987253925348358884097261 47245220222005634581536473)
              ·
                refine ⟨35433915166504225936152355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47245220222005634581536473 35433915166504225936152355)
                ·
                  refine ⟨53150872749756338904228533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35433915166504225936152355 53150872749756338904228533)
                  ·
                    refine ⟨4982894320289656772271425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53150872749756338904228533 4982894320289656772271425)
                    ·
                      refine ⟨3737170740217242579203569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4982894320289656772271425 3737170740217242579203569)
                      ·
                        rfl

theorem cell23_7278114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_7278114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278114 prefixEnd_7278114 := by exact prefixLift 7278114
  have htrace : WordTrace (prefixWord ++ tailWord_7278114) baseStart_7278114 baseEnd_7278114 := by
    simpa [prefixWord, tailWord_7278114, baseEnd_7278114] using wordTrace_append hprefix tailTrace_7278114
  have hstable : (prefixWord ++ tailWord_7278114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278114).length < 2 ^ (prefixWord ++ tailWord_7278114).sum := by decide
  have hdescent : baseEnd_7278114 < baseStart_7278114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278147 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 7, 2, 3]
def baseStart_7278147 : Nat := 118140960795 + 7278147 * 2 ^ 59
def prefixEnd_7278147 : Nat := 4983230072969 + 3 ^ 40 * 7278147 * 2
def baseEnd_7278147 : Nat := 3737187685078840950090917

theorem tailTrace_7278147 : CollatzResearch.WordTrace tailWord_7278147 prefixEnd_7278147 3737187685078840950090917 := by
  unfold tailWord_7278147
  simp only [CollatzResearch.WordTrace]
  refine ⟨265455829163523902391744695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176970552775682601594496463 265455829163523902391744695)
  ·
    refine ⟨398183743745285853587617043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265455829163523902391744695 398183743745285853587617043)
    ·
      refine ⟨597275615617928780381425565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398183743745285853587617043 597275615617928780381425565)
      ·
        refine ⟨223978355856723292643034587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 597275615617928780381425565 223978355856723292643034587)
        ·
          refine ⟨335967533785084938964551881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223978355856723292643034587 335967533785084938964551881)
          ·
            refine ⟨251975650338813704223413911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335967533785084938964551881 251975650338813704223413911)
            ·
              refine ⟨377963475508220556335120867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251975650338813704223413911 377963475508220556335120867)
              ·
                refine ⟨566945213262330834502681301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377963475508220556335120867 566945213262330834502681301)
                ·
                  refine ⟨13287778435835878933656593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 566945213262330834502681301 13287778435835878933656593)
                  ·
                    refine ⟨9965833826876909200242445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13287778435835878933656593 9965833826876909200242445)
                    ·
                      refine ⟨3737187685078840950090917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9965833826876909200242445 3737187685078840950090917)
                      ·
                        rfl

theorem cell23_7278147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 2, 3].length) (baseStart_7278147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278147 prefixEnd_7278147 := by exact prefixLift 7278147
  have htrace : WordTrace (prefixWord ++ tailWord_7278147) baseStart_7278147 baseEnd_7278147 := by
    simpa [prefixWord, tailWord_7278147, baseEnd_7278147] using wordTrace_append hprefix tailTrace_7278147
  have hstable : (prefixWord ++ tailWord_7278147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278147).length < 2 ^ (prefixWord ++ tailWord_7278147).sum := by decide
  have hdescent : baseEnd_7278147 < baseStart_7278147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278154 : List Nat := [3, 1, 2, 1, 1, 3, 2, 4, 2, 4]
def baseStart_7278154 : Nat := 118140960795 + 7278154 * 2 ^ 59
def prefixEnd_7278154 : Nat := 4983230072969 + 3 ^ 40 * 7278154 * 2
def baseEnd_7278154 : Nat := 1245730426481140807567795

theorem tailTrace_7278154 : CollatzResearch.WordTrace tailWord_7278154 prefixEnd_7278154 1245730426481140807567795 := by
  unfold tailWord_7278154
  simp only [CollatzResearch.WordTrace]
  refine ⟨66364021118624635646812379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176970722982999028391499677 66364021118624635646812379)
  ·
    refine ⟨99546031677936953470218569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66364021118624635646812379 99546031677936953470218569)
    ·
      refine ⟨74659523758452715102663927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99546031677936953470218569 74659523758452715102663927)
      ·
        refine ⟨111989285637679072653995891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74659523758452715102663927 111989285637679072653995891)
        ·
          refine ⟨167983928456518608980993837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111989285637679072653995891 167983928456518608980993837)
          ·
            refine ⟨62993973171194478367872689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167983928456518608980993837 62993973171194478367872689)
            ·
              refine ⟨47245479878395858775904517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62993973171194478367872689 47245479878395858775904517)
              ·
                refine ⟨8858527477199223520482097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47245479878395858775904517 8858527477199223520482097)
                ·
                  refine ⟨6643895607899417640361573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8858527477199223520482097 6643895607899417640361573)
                  ·
                    refine ⟨1245730426481140807567795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6643895607899417640361573 1245730426481140807567795)
                    ·
                      rfl

theorem cell23_7278154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_7278154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278154 prefixEnd_7278154 := by exact prefixLift 7278154
  have htrace : WordTrace (prefixWord ++ tailWord_7278154) baseStart_7278154 baseEnd_7278154 := by
    simpa [prefixWord, tailWord_7278154, baseEnd_7278154] using wordTrace_append hprefix tailTrace_7278154
  have hstable : (prefixWord ++ tailWord_7278154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278154).length < 2 ^ (prefixWord ++ tailWord_7278154).sum := by decide
  have hdescent : baseEnd_7278154 < baseStart_7278154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278164 : List Nat := [2, 4, 1, 1, 1, 2, 2, 2, 3, 2, 3]
def baseStart_7278164 : Nat := 118140960795 + 7278164 * 2 ^ 59
def prefixEnd_7278164 : Nat := 4983230072969 + 3 ^ 40 * 7278164 * 2
def baseEnd_7278164 : Nat := 3737196414249967383578339

theorem tailTrace_7278164 : CollatzResearch.WordTrace tailWord_7278164 prefixEnd_7278164 3737196414249967383578339 := by
  unfold tailWord_7278164
  simp only [CollatzResearch.WordTrace]
  refine ⟨132728224602231157147556773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176970966136308209530075697 132728224602231157147556773)
  ·
    refine ⟨24886542112918341965166895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132728224602231157147556773 24886542112918341965166895)
    ·
      refine ⟨37329813169377512947750343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24886542112918341965166895 37329813169377512947750343)
      ·
        refine ⟨55994719754066269421625515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37329813169377512947750343 55994719754066269421625515)
        ·
          refine ⟨83992079631099404132438273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55994719754066269421625515 83992079631099404132438273)
          ·
            refine ⟨62994059723324553099328705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83992079631099404132438273 62994059723324553099328705)
            ·
              refine ⟨47245544792493414824496529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62994059723324553099328705 47245544792493414824496529)
              ·
                refine ⟨35434158594370061118372397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47245544792493414824496529 35434158594370061118372397)
                ·
                  refine ⟨13287809472888772919389649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35434158594370061118372397 13287809472888772919389649)
                  ·
                    refine ⟨9965857104666579689542237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13287809472888772919389649 9965857104666579689542237)
                    ·
                      refine ⟨3737196414249967383578339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9965857104666579689542237 3737196414249967383578339)
                      ·
                        rfl

theorem cell23_7278164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_7278164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278164 prefixEnd_7278164 := by exact prefixLift 7278164
  have htrace : WordTrace (prefixWord ++ tailWord_7278164) baseStart_7278164 baseEnd_7278164 := by
    simpa [prefixWord, tailWord_7278164, baseEnd_7278164] using wordTrace_append hprefix tailTrace_7278164
  have hstable : (prefixWord ++ tailWord_7278164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278164).length < 2 ^ (prefixWord ++ tailWord_7278164).sum := by decide
  have hdescent : baseEnd_7278164 < baseStart_7278164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278167 : List Nat := [1, 1, 3, 2, 2, 4, 2, 8]
def baseStart_7278167 : Nat := 118140960795 + 7278167 * 2 ^ 59
def prefixEnd_7278167 : Nat := 4983230072969 + 3 ^ 40 * 7278167 * 2
def baseEnd_7278167 : Nat := 138414739062664106364475

theorem tailTrace_7278167 : CollatzResearch.WordTrace tailWord_7278167 prefixEnd_7278167 138414739062664106364475 := by
  unfold tailWord_7278167
  simp only [CollatzResearch.WordTrace]
  refine ⟨265456558623451445807472755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176971039082300963871648503 265456558623451445807472755)
  ·
    refine ⟨398184837935177168711209133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265456558623451445807472755 398184837935177168711209133)
    ·
      refine ⟨149319314225691438266703425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 398184837935177168711209133 149319314225691438266703425)
      ·
        refine ⟨111989485669268578700027569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149319314225691438266703425 111989485669268578700027569)
        ·
          refine ⟨83992114251951434025020677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111989485669268578700027569 83992114251951434025020677)
          ·
            refine ⟨15748521422240893879691377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83992114251951434025020677 15748521422240893879691377)
            ·
              refine ⟨11811391066680670409768533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15748521422240893879691377 11811391066680670409768533)
              ·
                refine ⟨138414739062664106364475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11811391066680670409768533 138414739062664106364475)
                ·
                  rfl

theorem cell23_7278167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 8].length) (baseStart_7278167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278167 prefixEnd_7278167 := by exact prefixLift 7278167
  have htrace : WordTrace (prefixWord ++ tailWord_7278167) baseStart_7278167 baseEnd_7278167 := by
    simpa [prefixWord, tailWord_7278167, baseEnd_7278167] using wordTrace_append hprefix tailTrace_7278167
  have hstable : (prefixWord ++ tailWord_7278167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278167).length < 2 ^ (prefixWord ++ tailWord_7278167).sum := by decide
  have hdescent : baseEnd_7278167 < baseStart_7278167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278181 : List Nat := [1, 3, 1, 3, 3, 1, 3, 2, 1, 2, 3]
def baseStart_7278181 : Nat := 118140960795 + 7278181 * 2 ^ 59
def prefixEnd_7278181 : Nat := 4983230072969 + 3 ^ 40 * 7278181 * 2
def baseEnd_7278181 : Nat := 3737205143421093817065761

theorem tailTrace_7278181 : CollatzResearch.WordTrace tailWord_7278181 prefixEnd_7278181 3737205143421093817065761 := by
  unfold tailWord_7278181
  simp only [CollatzResearch.WordTrace]
  refine ⟨265457069245400726198482397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176971379496933817465654931 265457069245400726198482397)
  ·
    refine ⟨99546400967025272324430899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265457069245400726198482397 99546400967025272324430899)
    ·
      refine ⟨149319601450537908486646349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99546400967025272324430899 149319601450537908486646349)
      ·
        refine ⟨55994850543951715682492381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149319601450537908486646349 55994850543951715682492381)
        ·
          refine ⟨20998068953981893380934643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55994850543951715682492381 20998068953981893380934643)
          ·
            refine ⟨31497103430972840071401965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20998068953981893380934643 31497103430972840071401965)
            ·
              refine ⟨11811413786614815026775737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31497103430972840071401965 11811413786614815026775737)
              ·
                refine ⟨8858560339961111270081803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11811413786614815026775737 8858560339961111270081803)
                ·
                  refine ⟨13287840509941666905122705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8858560339961111270081803 13287840509941666905122705)
                  ·
                    refine ⟨9965880382456250178842029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13287840509941666905122705 9965880382456250178842029)
                    ·
                      refine ⟨3737205143421093817065761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9965880382456250178842029 3737205143421093817065761)
                      ·
                        rfl

theorem cell23_7278181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_7278181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278181 prefixEnd_7278181 := by exact prefixLift 7278181
  have htrace : WordTrace (prefixWord ++ tailWord_7278181) baseStart_7278181 baseEnd_7278181 := by
    simpa [prefixWord, tailWord_7278181, baseEnd_7278181] using wordTrace_append hprefix tailTrace_7278181
  have hstable : (prefixWord ++ tailWord_7278181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278181).length < 2 ^ (prefixWord ++ tailWord_7278181).sum := by decide
  have hdescent : baseEnd_7278181 < baseStart_7278181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278194 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 3, 3, 3]
def baseStart_7278194 : Nat := 118140960795 + 7278194 * 2 ^ 59
def prefixEnd_7278194 : Nat := 4983230072969 + 3 ^ 40 * 7278194 * 2
def baseEnd_7278194 : Nat := 3737211818669602266203201

theorem tailTrace_7278194 : CollatzResearch.WordTrace tailWord_7278194 prefixEnd_7278194 3737211818669602266203201 := by
  unfold tailWord_7278194
  simp only [CollatzResearch.WordTrace]
  refine ⟨66364385848588407354676409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176971695596235752945803757 66364385848588407354676409)
  ·
    refine ⟨49773289386441305516007307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66364385848588407354676409 49773289386441305516007307)
    ·
      refine ⟨74659934079661958274010961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49773289386441305516007307 74659934079661958274010961)
      ·
        refine ⟨55994950559746468705508221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74659934079661958274010961 55994950559746468705508221)
        ·
          refine ⟨20998106459904925764565583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55994950559746468705508221 20998106459904925764565583)
          ·
            refine ⟨31497159689857388646848375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20998106459904925764565583 31497159689857388646848375)
            ·
              refine ⟨47245739534786082970272563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31497159689857388646848375 47245739534786082970272563)
              ·
                refine ⟨70868609302179124455408845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47245739534786082970272563 70868609302179124455408845)
                ·
                  refine ⟨26575728488317171670778317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70868609302179124455408845 26575728488317171670778317)
                  ·
                    refine ⟨9965898183118939376541869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26575728488317171670778317 9965898183118939376541869)
                    ·
                      refine ⟨3737211818669602266203201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9965898183118939376541869 3737211818669602266203201)
                      ·
                        rfl

theorem cell23_7278194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_7278194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278194 prefixEnd_7278194 := by exact prefixLift 7278194
  have htrace : WordTrace (prefixWord ++ tailWord_7278194) baseStart_7278194 baseEnd_7278194 := by
    simpa [prefixWord, tailWord_7278194, baseEnd_7278194] using wordTrace_append hprefix tailTrace_7278194
  have hstable : (prefixWord ++ tailWord_7278194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278194).length < 2 ^ (prefixWord ++ tailWord_7278194).sum := by decide
  have hdescent : baseEnd_7278194 < baseStart_7278194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278217 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 2, 3, 4]
def baseStart_7278217 : Nat := 118140960795 + 7278217 * 2 ^ 59
def prefixEnd_7278217 : Nat := 4983230072969 + 3 ^ 40 * 7278217 * 2
def baseEnd_7278217 : Nat := 3737223628724655676215595

theorem tailTrace_7278217 : CollatzResearch.WordTrace tailWord_7278217 prefixEnd_7278217 3737223628724655676215595 := by
  unfold tailWord_7278217
  simp only [CollatzResearch.WordTrace]
  refine ⟨265458382273270304346792905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176972254848846869564528603 265458382273270304346792905)
  ·
    refine ⟨199093786704952728260094679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265458382273270304346792905 199093786704952728260094679)
    ·
      refine ⟨298640680057429092390142019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199093786704952728260094679 298640680057429092390142019)
      ·
        refine ⟨447961020086143638585213029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298640680057429092390142019 447961020086143638585213029)
        ·
          refine ⟨83992691266151932234727443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 447961020086143638585213029 83992691266151932234727443)
          ·
            refine ⟨125989036899227898352091165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83992691266151932234727443 125989036899227898352091165)
            ·
              refine ⟨47245888837210461882034187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125989036899227898352091165 47245888837210461882034187)
              ·
                refine ⟨70868833255815692823051281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47245888837210461882034187 70868833255815692823051281)
                ·
                  refine ⟨53151624941861769617288461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70868833255815692823051281 53151624941861769617288461)
                  ·
                    refine ⟨19931859353198163606483173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53151624941861769617288461 19931859353198163606483173)
                    ·
                      refine ⟨3737223628724655676215595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19931859353198163606483173 3737223628724655676215595)
                      ·
                        rfl

theorem cell23_7278217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 3, 4].length) (baseStart_7278217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278217 prefixEnd_7278217 := by exact prefixLift 7278217
  have htrace : WordTrace (prefixWord ++ tailWord_7278217) baseStart_7278217 baseEnd_7278217 := by
    simpa [prefixWord, tailWord_7278217, baseEnd_7278217] using wordTrace_append hprefix tailTrace_7278217
  have hstable : (prefixWord ++ tailWord_7278217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278217).length < 2 ^ (prefixWord ++ tailWord_7278217).sum := by decide
  have hdescent : baseEnd_7278217 < baseStart_7278217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278228 : List Nat := [2, 4, 2, 2, 2, 1, 2, 1, 1, 3, 3]
def baseStart_7278228 : Nat := 118140960795 + 7278228 * 2 ^ 59
def prefixEnd_7278228 : Nat := 4983230072969 + 3 ^ 40 * 7278228 * 2
def baseEnd_7278228 : Nat := 3737229277011855133178045

theorem tailTrace_7278228 : CollatzResearch.WordTrace tailWord_7278228 prefixEnd_7278228 3737229277011855133178045 := by
  unfold tailWord_7278228
  simp only [CollatzResearch.WordTrace]
  refine ⟨132729391738115226612721669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176972522317486968816962225 132729391738115226612721669)
  ·
    refine ⟨24886760950896604989885313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132729391738115226612721669 24886760950896604989885313)
    ·
      refine ⟨18665070713172453742413985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24886760950896604989885313 18665070713172453742413985)
      ·
        refine ⟨13998803034879340306810489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18665070713172453742413985 13998803034879340306810489)
        ·
          refine ⟨10499102276159505230107867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13998803034879340306810489 10499102276159505230107867)
          ·
            refine ⟨15748653414239257845161801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10499102276159505230107867 15748653414239257845161801)
            ·
              refine ⟨11811490060679443383871351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15748653414239257845161801 11811490060679443383871351)
              ·
                refine ⟨17717235091019165075807027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11811490060679443383871351 17717235091019165075807027)
                ·
                  refine ⟨26575852636528747613710541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17717235091019165075807027 26575852636528747613710541)
                  ·
                    refine ⟨9965944738698280355141453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26575852636528747613710541 9965944738698280355141453)
                    ·
                      refine ⟨3737229277011855133178045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9965944738698280355141453 3737229277011855133178045)
                      ·
                        rfl

theorem cell23_7278228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_7278228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278228 prefixEnd_7278228 := by exact prefixLift 7278228
  have htrace : WordTrace (prefixWord ++ tailWord_7278228) baseStart_7278228 baseEnd_7278228 := by
    simpa [prefixWord, tailWord_7278228, baseEnd_7278228] using wordTrace_append hprefix tailTrace_7278228
  have hstable : (prefixWord ++ tailWord_7278228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278228).length < 2 ^ (prefixWord ++ tailWord_7278228).sum := by decide
  have hdescent : baseEnd_7278228 < baseStart_7278228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278238 : List Nat := [4, 3, 1, 1, 1, 2, 2, 1, 3, 3, 2]
def baseStart_7278238 : Nat := 118140960795 + 7278238 * 2 ^ 59
def prefixEnd_7278238 : Nat := 4983230072969 + 3 ^ 40 * 7278238 * 2
def baseEnd_7278238 : Nat := 3737234411818400094052999

theorem tailTrace_7278238 : CollatzResearch.WordTrace tailWord_7278238 prefixEnd_7278238 3737234411818400094052999 := by
  unfold tailWord_7278238
  simp only [CollatzResearch.WordTrace]
  refine ⟨33182393525774278116663421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176972765470796149955538245 33182393525774278116663421)
  ·
    refine ⟨12443397572165354293748783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33182393525774278116663421 12443397572165354293748783)
    ·
      refine ⟨18665096358248031440623175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12443397572165354293748783 18665096358248031440623175)
      ·
        refine ⟨27997644537372047160934763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18665096358248031440623175 27997644537372047160934763)
        ·
          refine ⟨41996466806058070741402145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27997644537372047160934763 41996466806058070741402145)
          ·
            refine ⟨31497350104543553056051609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41996466806058070741402145 31497350104543553056051609)
            ·
              refine ⟨23623012578407664792038707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31497350104543553056051609 23623012578407664792038707)
              ·
                refine ⟨35434518867611497188058061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23623012578407664792038707 35434518867611497188058061)
                ·
                  refine ⟨13287944575354311445521773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35434518867611497188058061 13287944575354311445521773)
                  ·
                    refine ⟨4982979215757866792070665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13287944575354311445521773 4982979215757866792070665)
                    ·
                      refine ⟨3737234411818400094052999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4982979215757866792070665 3737234411818400094052999)
                      ·
                        rfl

theorem cell23_7278238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_7278238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278238 prefixEnd_7278238 := by exact prefixLift 7278238
  have htrace : WordTrace (prefixWord ++ tailWord_7278238) baseStart_7278238 baseEnd_7278238 := by
    simpa [prefixWord, tailWord_7278238, baseEnd_7278238] using wordTrace_append hprefix tailTrace_7278238
  have hstable : (prefixWord ++ tailWord_7278238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278238).length < 2 ^ (prefixWord ++ tailWord_7278238).sum := by decide
  have hdescent : baseEnd_7278238 < baseStart_7278238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278262 : List Nat := [5, 1, 3, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_7278262 : Nat := 118140960795 + 7278262 * 2 ^ 59
def prefixEnd_7278262 : Nat := 4983230072969 + 3 ^ 40 * 7278262 * 2
def baseEnd_7278262 : Nat := 3737246735354108000152889

theorem tailTrace_7278262 : CollatzResearch.WordTrace tailWord_7278262 prefixEnd_7278262 3737246735354108000152889 := by
  unfold tailWord_7278262
  simp only [CollatzResearch.WordTrace]
  refine ⟨16591251472381704814511315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176973349038738184688120693 16591251472381704814511315)
  ·
    refine ⟨24886877208572557221766973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16591251472381704814511315 24886877208572557221766973)
    ·
      refine ⟨9332578953214708958162615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24886877208572557221766973 9332578953214708958162615)
      ·
        refine ⟨13998868429822063437243923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9332578953214708958162615 13998868429822063437243923)
        ·
          refine ⟨20998302644733095155865885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13998868429822063437243923 20998302644733095155865885)
          ·
            refine ⟨7874363491774910683449707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20998302644733095155865885 7874363491774910683449707)
            ·
              refine ⟨11811545237662366025174561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7874363491774910683449707 11811545237662366025174561)
              ·
                refine ⟨8858658928246774518880921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11811545237662366025174561 8858658928246774518880921)
                ·
                  refine ⟨6643994196185080889160691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8858658928246774518880921 6643994196185080889160691)
                  ·
                    refine ⟨9965991294277621333741037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6643994196185080889160691 9965991294277621333741037)
                    ·
                      refine ⟨3737246735354108000152889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9965991294277621333741037 3737246735354108000152889)
                      ·
                        rfl

theorem cell23_7278262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_7278262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278262 prefixEnd_7278262 := by exact prefixLift 7278262
  have htrace : WordTrace (prefixWord ++ tailWord_7278262) baseStart_7278262 baseEnd_7278262 := by
    simpa [prefixWord, tailWord_7278262, baseEnd_7278262] using wordTrace_append hprefix tailTrace_7278262
  have hstable : (prefixWord ++ tailWord_7278262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278262).length < 2 ^ (prefixWord ++ tailWord_7278262).sum := by decide
  have hdescent : baseEnd_7278262 < baseStart_7278262 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278268 : List Nat := [2, 2, 2, 3, 1, 3, 1, 1, 4, 2, 2]
def baseStart_7278268 : Nat := 118140960795 + 7278268 * 2 ^ 59
def prefixEnd_7278268 : Nat := 4983230072969 + 3 ^ 40 * 7278268 * 2
def baseEnd_7278268 : Nat := 3737249816238034976677861

theorem tailTrace_7278268 : CollatzResearch.WordTrace tailWord_7278268 prefixEnd_7278268 3737249816238034976677861 := by
  unfold tailWord_7278268
  simp only [CollatzResearch.WordTrace]
  refine ⟨132730121198042770028449729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176973494930723693371266305 132730121198042770028449729)
  ·
    refine ⟨99547590898532077521337297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132730121198042770028449729 99547590898532077521337297)
    ·
      refine ⟨74660693173899058141002973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99547590898532077521337297 74660693173899058141002973)
      ·
        refine ⟨27997759940212146802876115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74660693173899058141002973 27997759940212146802876115)
        ·
          refine ⟨41996639910318220204314173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27997759940212146802876115 41996639910318220204314173)
          ·
            refine ⟨15748739966369332576617815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41996639910318220204314173 15748739966369332576617815)
            ·
              refine ⟨23623109949553998864926723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15748739966369332576617815 23623109949553998864926723)
              ·
                refine ⟨35434664924330998297390085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23623109949553998864926723 35434664924330998297390085)
                ·
                  refine ⟨6643999673312062180760641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35434664924330998297390085 6643999673312062180760641)
                  ·
                    refine ⟨4982999754984046635570481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6643999673312062180760641 4982999754984046635570481)
                    ·
                      refine ⟨3737249816238034976677861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4982999754984046635570481 3737249816238034976677861)
                      ·
                        rfl

theorem cell23_7278268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_7278268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278268 prefixEnd_7278268 := by exact prefixLift 7278268
  have htrace : WordTrace (prefixWord ++ tailWord_7278268) baseStart_7278268 baseEnd_7278268 := by
    simpa [prefixWord, tailWord_7278268, baseEnd_7278268] using wordTrace_append hprefix tailTrace_7278268
  have hstable : (prefixWord ++ tailWord_7278268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278268).length < 2 ^ (prefixWord ++ tailWord_7278268).sum := by decide
  have hdescent : baseEnd_7278268 < baseStart_7278268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278278 : List Nat := [6, 1, 2, 1, 1, 1, 2, 1, 2, 6]
def baseStart_7278278 : Nat := 118140960795 + 7278278 * 2 ^ 59
def prefixEnd_7278278 : Nat := 4983230072969 + 3 ^ 40 * 7278278 * 2
def baseEnd_7278278 : Nat := 1245751650348193312517605

theorem tailTrace_7278278 : CollatzResearch.WordTrace tailWord_7278278 prefixEnd_7278278 1245751650348193312517605 := by
  unfold tailWord_7278278
  simp only [CollatzResearch.WordTrace]
  refine ⟨8295643972689040992648859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 176973738084032874509842325 8295643972689040992648859)
  ·
    refine ⟨12443465959033561488973289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8295643972689040992648859 12443465959033561488973289)
    ·
      refine ⟨9332599469275171116729967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12443465959033561488973289 9332599469275171116729967)
      ·
        refine ⟨13998899203912756675094951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9332599469275171116729967 13998899203912756675094951)
        ·
          refine ⟨20998348805869135012642427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13998899203912756675094951 20998348805869135012642427)
          ·
            refine ⟨31497523208803702518963641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20998348805869135012642427 31497523208803702518963641)
            ·
              refine ⟨23623142406602776889222731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31497523208803702518963641 23623142406602776889222731)
              ·
                refine ⟨35434713609904165333834097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23623142406602776889222731 35434713609904165333834097)
                ·
                  refine ⟨26576035207428124000375573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35434713609904165333834097 26576035207428124000375573)
                  ·
                    refine ⟨1245751650348193312517605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26576035207428124000375573 1245751650348193312517605)
                    ·
                      rfl

theorem cell23_7278278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_7278278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278278 prefixEnd_7278278 := by exact prefixLift 7278278
  have htrace : WordTrace (prefixWord ++ tailWord_7278278) baseStart_7278278 baseEnd_7278278 := by
    simpa [prefixWord, tailWord_7278278, baseEnd_7278278] using wordTrace_append hprefix tailTrace_7278278
  have hstable : (prefixWord ++ tailWord_7278278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278278).length < 2 ^ (prefixWord ++ tailWord_7278278).sum := by decide
  have hdescent : baseEnd_7278278 < baseStart_7278278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278285 : List Nat := [1, 6, 2, 1, 1, 1, 3, 1, 1, 4, 2]
def baseStart_7278285 : Nat := 118140960795 + 7278285 * 2 ^ 59
def prefixEnd_7278285 : Nat := 4983230072969 + 3 ^ 40 * 7278285 * 2
def baseEnd_7278285 : Nat := 3737258545409161410165283

theorem tailTrace_7278285 : CollatzResearch.WordTrace tailWord_7278285 prefixEnd_7278285 3737258545409161410165283 := by
  unfold tailWord_7278285
  simp only [CollatzResearch.WordTrace]
  refine ⟨265460862437023951960268309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176973908291349301306845539 265460862437023951960268309)
  ·
    refine ⟨12443477926735497748137577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 265460862437023951960268309 12443477926735497748137577)
    ·
      refine ⟨9332608445051623311103183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12443477926735497748137577 9332608445051623311103183)
      ·
        refine ⟨13998912667577434966654775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9332608445051623311103183 13998912667577434966654775)
        ·
          refine ⟨20998369001366152449982163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13998912667577434966654775 20998369001366152449982163)
          ·
            refine ⟨31497553502049228674973245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20998369001366152449982163 31497553502049228674973245)
            ·
              refine ⟨11811582563268460753114967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31497553502049228674973245 11811582563268460753114967)
              ·
                refine ⟨17717373844902691129672451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11811582563268460753114967 17717373844902691129672451)
                ·
                  refine ⟨26576060767354036694508677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17717373844902691129672451 26576060767354036694508677)
                  ·
                    refine ⟨4983011393878881880220377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26576060767354036694508677 4983011393878881880220377)
                    ·
                      refine ⟨3737258545409161410165283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4983011393878881880220377 3737258545409161410165283)
                      ·
                        rfl

theorem cell23_7278285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_7278285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278285 prefixEnd_7278285 := by exact prefixLift 7278285
  have htrace : WordTrace (prefixWord ++ tailWord_7278285) baseStart_7278285 baseEnd_7278285 := by
    simpa [prefixWord, tailWord_7278285, baseEnd_7278285] using wordTrace_append hprefix tailTrace_7278285
  have hstable : (prefixWord ++ tailWord_7278285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278285).length < 2 ^ (prefixWord ++ tailWord_7278285).sum := by decide
  have hdescent : baseEnd_7278285 < baseStart_7278285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278368 : List Nat := [2, 1, 1, 5, 1, 1, 2, 5, 1, 4]
def baseStart_7278368 : Nat := 118140960795 + 7278368 * 2 ^ 59
def prefixEnd_7278368 : Nat := 4983230072969 + 3 ^ 40 * 7278368 * 2
def baseEnd_7278368 : Nat := 1245767054767828195142467

theorem tailTrace_7278368 : CollatzResearch.WordTrace tailWord_7278368 prefixEnd_7278368 1245767054767828195142467 := by
  unfold tailWord_7278368
  simp only [CollatzResearch.WordTrace]
  refine ⟨132731944847861628567769879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176975926463815504757026505 132731944847861628567769879)
  ·
    refine ⟨199097917271792442851654819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132731944847861628567769879 199097917271792442851654819)
    ·
      refine ⟨298646875907688664277482229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199097917271792442851654819 298646875907688664277482229)
      ·
        refine ⟨27998144616345812276013959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 298646875907688664277482229 27998144616345812276013959)
        ·
          refine ⟨41997216924518718414020939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27998144616345812276013959 41997216924518718414020939)
          ·
            refine ⟨62995825386778077621031409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41997216924518718414020939 62995825386778077621031409)
            ·
              refine ⟨47246869040083558215773557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62995825386778077621031409 47246869040083558215773557)
              ·
                refine ⟨4429393972507833582728771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47246869040083558215773557 4429393972507833582728771)
                ·
                  refine ⟨6644090958761750374093157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4429393972507833582728771 6644090958761750374093157)
                  ·
                    refine ⟨1245767054767828195142467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6644090958761750374093157 1245767054767828195142467)
                    ·
                      rfl

theorem cell23_7278368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 5, 1, 4].length) (baseStart_7278368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278368 prefixEnd_7278368 := by exact prefixLift 7278368
  have htrace : WordTrace (prefixWord ++ tailWord_7278368) baseStart_7278368 baseEnd_7278368 := by
    simpa [prefixWord, tailWord_7278368, baseEnd_7278368] using wordTrace_append hprefix tailTrace_7278368
  have hstable : (prefixWord ++ tailWord_7278368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278368).length < 2 ^ (prefixWord ++ tailWord_7278368).sum := by decide
  have hdescent : baseEnd_7278368 < baseStart_7278368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278385 : List Nat := [1, 2, 2, 3, 2, 2, 4, 2, 1, 4]
def baseStart_7278385 : Nat := 118140960795 + 7278385 * 2 ^ 59
def prefixEnd_7278385 : Nat := 4983230072969 + 3 ^ 40 * 7278385 * 2
def baseEnd_7278385 : Nat := 1245769964491537006304941

theorem tailTrace_7278385 : CollatzResearch.WordTrace tailWord_7278385 prefixEnd_7278385 1245769964491537006304941 := by
  unfold tailWord_7278385
  simp only [CollatzResearch.WordTrace]
  refine ⟨265464509736661669038908609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176976339824441112692605739 265464509736661669038908609)
  ·
    refine ⟨199098382302496251779181457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265464509736661669038908609 199098382302496251779181457)
    ·
      refine ⟨149323786726872188834386093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199098382302496251779181457 149323786726872188834386093)
      ·
        refine ⟨55996420022577070812894785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149323786726872188834386093 55996420022577070812894785)
        ·
          refine ⟨41997315016932803109671089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55996420022577070812894785 41997315016932803109671089)
          ·
            refine ⟨31497986262699602332253317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41997315016932803109671089 31497986262699602332253317)
            ·
              refine ⟨5905872424256175437297497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31497986262699602332253317 5905872424256175437297497)
              ·
                refine ⟨4429404318192131577973123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5905872424256175437297497 4429404318192131577973123)
                ·
                  refine ⟨6644106477288197366959685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4429404318192131577973123 6644106477288197366959685)
                  ·
                    refine ⟨1245769964491537006304941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6644106477288197366959685 1245769964491537006304941)
                    ·
                      rfl

theorem cell23_7278385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 2, 1, 4].length) (baseStart_7278385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278385 prefixEnd_7278385 := by exact prefixLift 7278385
  have htrace : WordTrace (prefixWord ++ tailWord_7278385) baseStart_7278385 baseEnd_7278385 := by
    simpa [prefixWord, tailWord_7278385, baseEnd_7278385] using wordTrace_append hprefix tailTrace_7278385
  have hstable : (prefixWord ++ tailWord_7278385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278385).length < 2 ^ (prefixWord ++ tailWord_7278385).sum := by decide
  have hdescent : baseEnd_7278385 < baseStart_7278385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278408 : List Nat := [2, 1, 3, 1, 1, 5, 1, 2, 3, 1, 3]
def baseStart_7278408 : Nat := 118140960795 + 7278408 * 2 ^ 59
def prefixEnd_7278408 : Nat := 4983230072969 + 3 ^ 40 * 7278408 * 2
def baseEnd_7278408 : Nat := 3737321703529664428927217

theorem tailTrace_7278408 : CollatzResearch.WordTrace tailWord_7278408 prefixEnd_7278408 3737321703529664428927217 := by
  unfold tailWord_7278408
  simp only [CollatzResearch.WordTrace]
  refine ⟨132732674307789171983497939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176976899077052229311330585 132732674307789171983497939)
  ·
    refine ⟨199099011461683757975246909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132732674307789171983497939 199099011461683757975246909)
    ·
      refine ⟨74662129298131409240717591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199099011461683757975246909 74662129298131409240717591)
      ·
        refine ⟨111993193947197113861076387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74662129298131409240717591 111993193947197113861076387)
        ·
          refine ⟨167989790920795670791614581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111993193947197113861076387 167989790920795670791614581)
          ·
            refine ⟨15749042898824594136713867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 167989790920795670791614581 15749042898824594136713867)
            ·
              refine ⟨23623564348236891205070801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15749042898824594136713867 23623564348236891205070801)
              ·
                refine ⟨17717673261177668403803101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23623564348236891205070801 17717673261177668403803101)
                ·
                  refine ⟨6644127472941625651426163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17717673261177668403803101 6644127472941625651426163)
                  ·
                    refine ⟨9966191209412438477139245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6644127472941625651426163 9966191209412438477139245)
                    ·
                      refine ⟨3737321703529664428927217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9966191209412438477139245 3737321703529664428927217)
                      ·
                        rfl

theorem cell23_7278408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_7278408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278408 prefixEnd_7278408 := by exact prefixLift 7278408
  have htrace : WordTrace (prefixWord ++ tailWord_7278408) baseStart_7278408 baseEnd_7278408 := by
    simpa [prefixWord, tailWord_7278408, baseEnd_7278408] using wordTrace_append hprefix tailTrace_7278408
  have hstable : (prefixWord ++ tailWord_7278408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278408).length < 2 ^ (prefixWord ++ tailWord_7278408).sum := by decide
  have hdescent : baseEnd_7278408 < baseStart_7278408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278418 : List Nat := [3, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2]
def baseStart_7278418 : Nat := 118140960795 + 7278418 * 2 ^ 59
def prefixEnd_7278418 : Nat := 4983230072969 + 3 ^ 40 * 7278418 * 2
def baseEnd_7278418 : Nat := 3737326838336209389802171

theorem tailTrace_7278418 : CollatzResearch.WordTrace tailWord_7278418 prefixEnd_7278418 3737326838336209389802171 := by
  unfold tailWord_7278418
  simp only [CollatzResearch.WordTrace]
  refine ⟨66366428336385528918714977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176977142230361410449906605 66366428336385528918714977)
  ·
    refine ⟨49774821252289146689036233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66366428336385528918714977 49774821252289146689036233)
    ·
      refine ⟨37331115939216860016777175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49774821252289146689036233 37331115939216860016777175)
      ·
        refine ⟨55996673908825290025165763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37331115939216860016777175 55996673908825290025165763)
        ·
          refine ⟨83995010863237935037748645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55996673908825290025165763 83995010863237935037748645)
          ·
            refine ⟨15749064536857112819577871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83995010863237935037748645 15749064536857112819577871)
            ·
              refine ⟨23623596805285669229366807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15749064536857112819577871 23623596805285669229366807)
              ·
                refine ⟨35435395207928503844050211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23623596805285669229366807 35435395207928503844050211)
                ·
                  refine ⟨53153092811892755766075317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35435395207928503844050211 53153092811892755766075317)
                  ·
                    refine ⟨4983102451114945853069561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53153092811892755766075317 4983102451114945853069561)
                    ·
                      refine ⟨3737326838336209389802171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4983102451114945853069561 3737326838336209389802171)
                      ·
                        rfl

theorem cell23_7278418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_7278418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278418 prefixEnd_7278418 := by exact prefixLift 7278418
  have htrace : WordTrace (prefixWord ++ tailWord_7278418) baseStart_7278418 baseEnd_7278418 := by
    simpa [prefixWord, tailWord_7278418, baseEnd_7278418] using wordTrace_append hprefix tailTrace_7278418
  have hstable : (prefixWord ++ tailWord_7278418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278418).length < 2 ^ (prefixWord ++ tailWord_7278418).sum := by decide
  have hdescent : baseEnd_7278418 < baseStart_7278418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278425 : List Nat := [1, 2, 1, 2, 2, 3, 4, 3, 1, 1, 3]
def baseStart_7278425 : Nat := 118140960795 + 7278425 * 2 ^ 59
def prefixEnd_7278425 : Nat := 4983230072969 + 3 ^ 40 * 7278425 * 2
def baseEnd_7278425 : Nat := 3737330432700790862414639

theorem tailTrace_7278425 : CollatzResearch.WordTrace tailWord_7278425 prefixEnd_7278425 3737330432700790862414639 := by
  unfold tailWord_7278425
  simp only [CollatzResearch.WordTrace]
  refine ⟨265465968656516755870364729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176977312437677837246909819 265465968656516755870364729)
  ·
    refine ⟨199099476492387566902773547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265465968656516755870364729 199099476492387566902773547)
    ·
      refine ⟨298649214738581350354160321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199099476492387566902773547 298649214738581350354160321)
      ·
        refine ⟨223986911053936012765620241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298649214738581350354160321 223986911053936012765620241)
        ·
          refine ⟨167990183290452009574215181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223986911053936012765620241 167990183290452009574215181)
          ·
            refine ⟨62996318733919503590330693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167990183290452009574215181 62996318733919503590330693)
            ·
              refine ⟨11811809762609906923187005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62996318733919503590330693 11811809762609906923187005)
              ·
                refine ⟨4429428660978715096195127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11811809762609906923187005 4429428660978715096195127)
                ·
                  refine ⟨6644142991468072644292691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4429428660978715096195127 6644142991468072644292691)
                  ·
                    refine ⟨9966214487202108966439037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6644142991468072644292691 9966214487202108966439037)
                    ·
                      refine ⟨3737330432700790862414639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9966214487202108966439037 3737330432700790862414639)
                      ·
                        rfl

theorem cell23_7278425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 3, 1, 1, 3].length) (baseStart_7278425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278425 prefixEnd_7278425 := by exact prefixLift 7278425
  have htrace : WordTrace (prefixWord ++ tailWord_7278425) baseStart_7278425 baseEnd_7278425 := by
    simpa [prefixWord, tailWord_7278425, baseEnd_7278425] using wordTrace_append hprefix tailTrace_7278425
  have hstable : (prefixWord ++ tailWord_7278425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278425).length < 2 ^ (prefixWord ++ tailWord_7278425).sum := by decide
  have hdescent : baseEnd_7278425 < baseStart_7278425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278442 : List Nat := [3, 1, 3, 4, 1, 1, 2, 1, 3, 1, 3]
def baseStart_7278442 : Nat := 118140960795 + 7278442 * 2 ^ 59
def prefixEnd_7278442 : Nat := 4983230072969 + 3 ^ 40 * 7278442 * 2
def baseEnd_7278442 : Nat := 3737339161871917295902061

theorem tailTrace_7278442 : CollatzResearch.WordTrace tailWord_7278442 prefixEnd_7278442 3737339161871917295902061 := by
  unfold tailWord_7278442
  simp only [CollatzResearch.WordTrace]
  refine ⟨66366647174363791943433395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176977725798303445182489053 66366647174363791943433395)
  ·
    refine ⟨99549970761545687915150093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66366647174363791943433395 99549970761545687915150093)
    ·
      refine ⟨37331239035579632968181285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99549970761545687915150093 37331239035579632968181285)
      ·
        refine ⟨6999607319171181181533991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37331239035579632968181285 6999607319171181181533991)
        ·
          refine ⟨10499410978756771772300987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6999607319171181181533991 10499410978756771772300987)
          ·
            refine ⟨15749116468135157658451481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10499410978756771772300987 15749116468135157658451481)
            ·
              refine ⟨11811837351101368243838611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15749116468135157658451481 11811837351101368243838611)
              ·
                refine ⟨17717756026652052365757917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11811837351101368243838611 17717756026652052365757917)
                ·
                  refine ⟨6644158509994519637159219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17717756026652052365757917 6644158509994519637159219)
                  ·
                    refine ⟨9966237764991779455738829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6644158509994519637159219 9966237764991779455738829)
                    ·
                      refine ⟨3737339161871917295902061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9966237764991779455738829 3737339161871917295902061)
                      ·
                        rfl

theorem cell23_7278442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_7278442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278442 prefixEnd_7278442 := by exact prefixLift 7278442
  have htrace : WordTrace (prefixWord ++ tailWord_7278442) baseStart_7278442 baseEnd_7278442 := by
    simpa [prefixWord, tailWord_7278442, baseEnd_7278442] using wordTrace_append hprefix tailTrace_7278442
  have hstable : (prefixWord ++ tailWord_7278442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278442).length < 2 ^ (prefixWord ++ tailWord_7278442).sum := by decide
  have hdescent : baseEnd_7278442 < baseStart_7278442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278468 : List Nat := [2, 3, 2, 1, 1, 1, 3, 4, 1, 2, 3]
def baseStart_7278468 : Nat := 118140960795 + 7278468 * 2 ^ 59
def prefixEnd_7278468 : Nat := 4983230072969 + 3 ^ 40 * 7278468 * 2
def baseEnd_7278468 : Nat := 3737352512368934194176941

theorem tailTrace_7278468 : CollatzResearch.WordTrace tailWord_7278468 prefixEnd_7278468 3737352512368934194176941 := by
  unfold tailWord_7278468
  simp only [CollatzResearch.WordTrace]
  refine ⟨132733768497680487107090029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176978357996907316142786705 132733768497680487107090029)
  ·
    refine ⟨49775163186630182665158761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132733768497680487107090029 49775163186630182665158761)
    ·
      refine ⟨37331372389972636998869071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49775163186630182665158761 37331372389972636998869071)
      ·
        refine ⟨55997058584958955498303607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37331372389972636998869071 55997058584958955498303607)
        ·
          refine ⟨83995587877438433247455411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55997058584958955498303607 83995587877438433247455411)
          ·
            refine ⟨125993381816157649871183117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83995587877438433247455411 125993381816157649871183117)
            ·
              refine ⟨47247518181059118701693669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125993381816157649871183117 47247518181059118701693669)
              ·
                refine ⟨8858909658948584756567563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47247518181059118701693669 8858909658948584756567563)
                ·
                  refine ⟨13288364488422877134851345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8858909658948584756567563 13288364488422877134851345)
                  ·
                    refine ⟨9966273366317157851138509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13288364488422877134851345 9966273366317157851138509)
                    ·
                      refine ⟨3737352512368934194176941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9966273366317157851138509 3737352512368934194176941)
                      ·
                        rfl

theorem cell23_7278468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_7278468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278468 prefixEnd_7278468 := by exact prefixLift 7278468
  have htrace : WordTrace (prefixWord ++ tailWord_7278468) baseStart_7278468 baseEnd_7278468 := by
    simpa [prefixWord, tailWord_7278468, baseEnd_7278468] using wordTrace_append hprefix tailTrace_7278468
  have hstable : (prefixWord ++ tailWord_7278468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278468).length < 2 ^ (prefixWord ++ tailWord_7278468).sum := by decide
  have hdescent : baseEnd_7278468 < baseStart_7278468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278471 : List Nat := [1, 1, 4, 2, 4, 1, 1, 9]
def baseStart_7278471 : Nat := 118140960795 + 7278471 * 2 ^ 59
def prefixEnd_7278471 : Nat := 4983230072969 + 3 ^ 40 * 7278471 * 2
def baseEnd_7278471 : Nat := 138420520474477691942201

theorem tailTrace_7278471 : CollatzResearch.WordTrace tailWord_7278471 prefixEnd_7278471 138420520474477691942201 := by
  unfold tailWord_7278471
  simp only [CollatzResearch.WordTrace]
  refine ⟨265467646414350105726539267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176978430942900070484359511 265467646414350105726539267)
  ·
    refine ⟨398201469621525158589808901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265467646414350105726539267 398201469621525158589808901)
    ·
      refine ⟨74662775554035967235589169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 398201469621525158589808901 74662775554035967235589169)
      ·
        refine ⟨55997081665526975426691877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74662775554035967235589169 55997081665526975426691877)
        ·
          refine ⟨10499452812286307892504727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55997081665526975426691877 10499452812286307892504727)
          ·
            refine ⟨15749179218429461838757091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10499452812286307892504727 15749179218429461838757091)
            ·
              refine ⟨23623768827644192758135637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15749179218429461838757091 23623768827644192758135637)
              ·
                refine ⟨138420520474477691942201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23623768827644192758135637 138420520474477691942201)
                ·
                  rfl

theorem cell23_7278471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 9].length) (baseStart_7278471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278471 prefixEnd_7278471 := by exact prefixLift 7278471
  have htrace : WordTrace (prefixWord ++ tailWord_7278471) baseStart_7278471 baseEnd_7278471 := by
    simpa [prefixWord, tailWord_7278471, baseEnd_7278471] using wordTrace_append hprefix tailTrace_7278471
  have hstable : (prefixWord ++ tailWord_7278471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278471).length < 2 ^ (prefixWord ++ tailWord_7278471).sum := by decide
  have hdescent : baseEnd_7278471 < baseStart_7278471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278481 : List Nat := [1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 3]
def baseStart_7278481 : Nat := 118140960795 + 7278481 * 2 ^ 59
def prefixEnd_7278481 : Nat := 4983230072969 + 3 ^ 40 * 7278481 * 2
def baseEnd_7278481 : Nat := 3737359187617442643314381

theorem tailTrace_7278481 : CollatzResearch.WordTrace tailWord_7278481 prefixEnd_7278481 3737359187617442643314381 := by
  unfold tailWord_7278481
  simp only [CollatzResearch.WordTrace]
  refine ⟨265468011144313877434403297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176978674096209251622935531 265468011144313877434403297)
  ·
    refine ⟨199101008358235408075802473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265468011144313877434403297 199101008358235408075802473)
    ·
      refine ⟨149325756268676556056851855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199101008358235408075802473 149325756268676556056851855)
      ·
        refine ⟨223988634403014834085277783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149325756268676556056851855 223988634403014834085277783)
        ·
          refine ⟨335982951604522251127916675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223988634403014834085277783 335982951604522251127916675)
          ·
            refine ⟨503974427406783376691875013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335982951604522251127916675 503974427406783376691875013)
            ·
              refine ⟨94495205138771883129726565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 503974427406783376691875013 94495205138771883129726565)
              ·
                refine ⟨17717850963519728086823731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94495205138771883129726565 17717850963519728086823731)
                ·
                  refine ⟨26576776445279592130235597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17717850963519728086823731 26576776445279592130235597)
                  ·
                    refine ⟨9966291166979847048838349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26576776445279592130235597 9966291166979847048838349)
                    ·
                      refine ⟨3737359187617442643314381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9966291166979847048838349 3737359187617442643314381)
                      ·
                        rfl

theorem cell23_7278481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 3].length) (baseStart_7278481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278481 prefixEnd_7278481 := by exact prefixLift 7278481
  have htrace : WordTrace (prefixWord ++ tailWord_7278481) baseStart_7278481 baseEnd_7278481 := by
    simpa [prefixWord, tailWord_7278481, baseEnd_7278481] using wordTrace_append hprefix tailTrace_7278481
  have hstable : (prefixWord ++ tailWord_7278481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278481).length < 2 ^ (prefixWord ++ tailWord_7278481).sum := by decide
  have hdescent : baseEnd_7278481 < baseStart_7278481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278488 : List Nat := [2, 1, 2, 6, 1, 2, 9]
def baseStart_7278488 : Nat := 118140960795 + 7278488 * 2 ^ 59
def prefixEnd_7278488 : Nat := 4983230072969 + 3 ^ 40 * 7278488 * 2
def baseEnd_7278488 : Nat := 46140281259037334764529

theorem tailTrace_7278488 : CollatzResearch.WordTrace tailWord_7278488 prefixEnd_7278488 46140281259037334764529 := by
  unfold tailWord_7278488
  simp only [CollatzResearch.WordTrace]
  refine ⟨132734133227644258814954059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176978844303525678419938745 132734133227644258814954059)
  ·
    refine ⟨199101199841466388222431089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132734133227644258814954059 199101199841466388222431089)
    ·
      refine ⟨149325899881099791166823317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199101199841466388222431089 149325899881099791166823317)
      ·
        refine ⟨6999651556926552710944843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 149325899881099791166823317 6999651556926552710944843)
        ·
          refine ⟨10499477335389829066417265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6999651556926552710944843 10499477335389829066417265)
          ·
            refine ⟨7874608001542371799812949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10499477335389829066417265 7874608001542371799812949)
            ·
              refine ⟨46140281259037334764529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7874608001542371799812949 46140281259037334764529)
              ·
                rfl

theorem cell23_7278488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 9].length) (baseStart_7278488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278488 prefixEnd_7278488 := by exact prefixLift 7278488
  have htrace : WordTrace (prefixWord ++ tailWord_7278488) baseStart_7278488 baseEnd_7278488 := by
    simpa [prefixWord, tailWord_7278488, baseEnd_7278488] using wordTrace_append hprefix tailTrace_7278488
  have hstable : (prefixWord ++ tailWord_7278488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278488).length < 2 ^ (prefixWord ++ tailWord_7278488).sum := by decide
  have hdescent : baseEnd_7278488 < baseStart_7278488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278525 : List Nat := [1, 4, 1, 2, 3, 2, 1, 1, 3, 3, 2]
def baseStart_7278525 : Nat := 118140960795 + 7278525 * 2 ^ 59
def prefixEnd_7278525 : Nat := 4983230072969 + 3 ^ 40 * 7278525 * 2
def baseEnd_7278525 : Nat := 3737381780766240471164179

theorem tailTrace_7278525 : CollatzResearch.WordTrace tailWord_7278525 prefixEnd_7278525 3737381780766240471164179 := by
  unfold tailWord_7278525
  simp only [CollatzResearch.WordTrace]
  refine ⟨265469615956154472949005029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176979743970769648632670019 265469615956154472949005029)
  ·
    refine ⟨49775552991778963677938443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265469615956154472949005029 49775552991778963677938443)
    ·
      refine ⟨74663329487668445516907665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49775552991778963677938443 74663329487668445516907665)
      ·
        refine ⟨55997497115751334137680749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74663329487668445516907665 55997497115751334137680749)
        ·
          refine ⟨20999061418406750301630281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55997497115751334137680749 20999061418406750301630281)
          ·
            refine ⟨15749296063805062726222711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20999061418406750301630281 15749296063805062726222711)
            ·
              refine ⟨23623944095707594089334067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15749296063805062726222711 23623944095707594089334067)
              ·
                refine ⟨35435916143561391134001101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23623944095707594089334067 35435916143561391134001101)
                ·
                  refine ⟨13288468553835521675250413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35435916143561391134001101 13288468553835521675250413)
                  ·
                    refine ⟨4983175707688320628218905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13288468553835521675250413 4983175707688320628218905)
                    ·
                      refine ⟨3737381780766240471164179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4983175707688320628218905 3737381780766240471164179)
                      ·
                        rfl

theorem cell23_7278525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_7278525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278525 prefixEnd_7278525 := by exact prefixLift 7278525
  have htrace : WordTrace (prefixWord ++ tailWord_7278525) baseStart_7278525 baseEnd_7278525 := by
    simpa [prefixWord, tailWord_7278525, baseEnd_7278525] using wordTrace_append hprefix tailTrace_7278525
  have hstable : (prefixWord ++ tailWord_7278525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278525).length < 2 ^ (prefixWord ++ tailWord_7278525).sum := by decide
  have hdescent : baseEnd_7278525 < baseStart_7278525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278538 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 3, 4, 2]
def baseStart_7278538 : Nat := 118140960795 + 7278538 * 2 ^ 59
def prefixEnd_7278538 : Nat := 4983230072969 + 3 ^ 40 * 7278538 * 2
def baseEnd_7278538 : Nat := 3737388456014748920301619

theorem tailTrace_7278538 : CollatzResearch.WordTrace tailWord_7278538 prefixEnd_7278538 3737388456014748920301619 := by
  unfold tailWord_7278538
  simp only [CollatzResearch.WordTrace]
  refine ⟨66367522526276844042307067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176980060070071584112818845 66367522526276844042307067)
  ·
    refine ⟨99551283789415266063460601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66367522526276844042307067 99551283789415266063460601)
    ·
      refine ⟨74663462842061449547595451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99551283789415266063460601 74663462842061449547595451)
      ·
        refine ⟨111995194263092174321393177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74663462842061449547595451 111995194263092174321393177)
        ·
          refine ⟨83996395697319130741044883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111995194263092174321393177 83996395697319130741044883)
          ·
            refine ⟨125994593545978696111567325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83996395697319130741044883 125994593545978696111567325)
            ·
              refine ⟨47247972579742011041837747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125994593545978696111567325 47247972579742011041837747)
              ·
                refine ⟨70871958869613016562756621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47247972579742011041837747 70871958869613016562756621)
                ·
                  refine ⟨26576984576104881211033733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70871958869613016562756621 26576984576104881211033733)
                  ·
                    refine ⟨4983184608019665227068825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26576984576104881211033733 4983184608019665227068825)
                    ·
                      refine ⟨3737388456014748920301619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4983184608019665227068825 3737388456014748920301619)
                      ·
                        rfl

theorem cell23_7278538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 3, 4, 2].length) (baseStart_7278538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278538 prefixEnd_7278538 := by exact prefixLift 7278538
  have htrace : WordTrace (prefixWord ++ tailWord_7278538) baseStart_7278538 baseEnd_7278538 := by
    simpa [prefixWord, tailWord_7278538, baseEnd_7278538] using wordTrace_append hprefix tailTrace_7278538
  have hstable : (prefixWord ++ tailWord_7278538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278538).length < 2 ^ (prefixWord ++ tailWord_7278538).sum := by decide
  have hdescent : baseEnd_7278538 < baseStart_7278538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278542 : List Nat := [4, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2]
def baseStart_7278542 : Nat := 118140960795 + 7278542 * 2 ^ 59
def prefixEnd_7278542 : Nat := 4983230072969 + 3 ^ 40 * 7278542 * 2
def baseEnd_7278542 : Nat := 3737390509937366904651601

theorem tailTrace_7278542 : CollatzResearch.WordTrace tailWord_7278542 prefixEnd_7278542 3737390509937366904651601 := by
  unfold tailWord_7278542
  simp only [CollatzResearch.WordTrace]
  refine ⟨33183779499636610606546735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176980157331395256568249253 33183779499636610606546735)
  ·
    refine ⟨49775669249454915909820103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33183779499636610606546735 49775669249454915909820103)
    ·
      refine ⟨74663503874182373864730155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49775669249454915909820103 74663503874182373864730155)
      ·
        refine ⟨111995255811273560797095233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74663503874182373864730155 111995255811273560797095233)
        ·
          refine ⟨83996441858455170597821425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111995255811273560797095233 83996441858455170597821425)
          ·
            refine ⟨62997331393841377948366069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83996441858455170597821425 62997331393841377948366069)
            ·
              refine ⟨5905999818172629182659319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62997331393841377948366069 5905999818172629182659319)
              ·
                refine ⟨8858999727258943773988979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5905999818172629182659319 8858999727258943773988979)
                ·
                  refine ⟨13288499590888415660983469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8858999727258943773988979 13288499590888415660983469)
                  ·
                    refine ⟨4983187346583155872868801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13288499590888415660983469 4983187346583155872868801)
                    ·
                      refine ⟨3737390509937366904651601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4983187346583155872868801 3737390509937366904651601)
                      ·
                        rfl

theorem cell23_7278542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2].length) (baseStart_7278542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278542 prefixEnd_7278542 := by exact prefixLift 7278542
  have htrace : WordTrace (prefixWord ++ tailWord_7278542) baseStart_7278542 baseEnd_7278542 := by
    simpa [prefixWord, tailWord_7278542, baseEnd_7278542] using wordTrace_append hprefix tailTrace_7278542
  have hstable : (prefixWord ++ tailWord_7278542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278542).length < 2 ^ (prefixWord ++ tailWord_7278542).sum := by decide
  have hdescent : baseEnd_7278542 < baseStart_7278542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278550 : List Nat := [5, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2]
def baseStart_7278550 : Nat := 118140960795 + 7278550 * 2 ^ 59
def prefixEnd_7278550 : Nat := 4983230072969 + 3 ^ 40 * 7278550 * 2
def baseEnd_7278550 : Nat := 3737394617782602873351565

theorem tailTrace_7278550 : CollatzResearch.WordTrace tailWord_7278550 prefixEnd_7278550 3737394617782602873351565 := by
  unfold tailWord_7278550
  simp only [CollatzResearch.WordTrace]
  refine ⟨16591907986316493888666569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176980351854042601479110069 16591907986316493888666569)
  ·
    refine ⟨12443930989737370416499927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16591907986316493888666569 12443930989737370416499927)
    ·
      refine ⟨18665896484606055624749891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12443930989737370416499927 18665896484606055624749891)
      ·
        refine ⟨27998844726909083437124837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18665896484606055624749891 27998844726909083437124837)
        ·
          refine ⟨5249783386295453144460907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27998844726909083437124837 5249783386295453144460907)
          ·
            refine ⟨7874675079443179716691361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5249783386295453144460907 7874675079443179716691361)
            ·
              refine ⟨5906006309582384787518521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7874675079443179716691361 5906006309582384787518521)
              ·
                refine ⟨4429504732186788590638891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5906006309582384787518521 4429504732186788590638891)
                ·
                  refine ⟨6644257098280182885958337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4429504732186788590638891 6644257098280182885958337)
                  ·
                    refine ⟨4983192823710137164468753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6644257098280182885958337 4983192823710137164468753)
                    ·
                      refine ⟨3737394617782602873351565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4983192823710137164468753 3737394617782602873351565)
                      ·
                        rfl

theorem cell23_7278550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_7278550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278550 prefixEnd_7278550 := by exact prefixLift 7278550
  have htrace : WordTrace (prefixWord ++ tailWord_7278550) baseStart_7278550 baseEnd_7278550 := by
    simpa [prefixWord, tailWord_7278550, baseEnd_7278550] using wordTrace_append hprefix tailTrace_7278550
  have hstable : (prefixWord ++ tailWord_7278550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278550).length < 2 ^ (prefixWord ++ tailWord_7278550).sum := by decide
  have hdescent : baseEnd_7278550 < baseStart_7278550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278551 : List Nat := [1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 4]
def baseStart_7278551 : Nat := 118140960795 + 7278551 * 2 ^ 59
def prefixEnd_7278551 : Nat := 4983230072969 + 3 ^ 40 * 7278551 * 2
def baseEnd_7278551 : Nat := 3737395131263257369439059

theorem tailTrace_7278551 : CollatzResearch.WordTrace tailWord_7278551 prefixEnd_7278551 3737395131263257369439059 := by
  unfold tailWord_7278551
  simp only [CollatzResearch.WordTrace]
  refine ⟨265470564254060279389451507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176980376169373519592967671 265470564254060279389451507)
  ·
    refine ⟨398205846381090419084177261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265470564254060279389451507 398205846381090419084177261)
    ·
      refine ⟨149327192392908907156566473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 398205846381090419084177261 149327192392908907156566473)
      ·
        refine ⟨111995394294681680367424855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149327192392908907156566473 111995394294681680367424855)
        ·
          refine ⟨167993091442022520551137283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111995394294681680367424855 167993091442022520551137283)
          ·
            refine ⟨251989637163033780826705925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167993091442022520551137283 251989637163033780826705925)
            ·
              refine ⟨47248056968068833905007361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 251989637163033780826705925 47248056968068833905007361)
              ·
                refine ⟨35436042726051625428755521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47248056968068833905007361 35436042726051625428755521)
                ·
                  refine ⟨26577032044538719071566641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35436042726051625428755521 26577032044538719071566641)
                  ·
                    refine ⟨19932774033404039303674981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26577032044538719071566641 19932774033404039303674981)
                    ·
                      refine ⟨3737395131263257369439059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19932774033404039303674981 3737395131263257369439059)
                      ·
                        rfl

theorem cell23_7278551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_7278551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278551 prefixEnd_7278551 := by exact prefixLift 7278551
  have htrace : WordTrace (prefixWord ++ tailWord_7278551) baseStart_7278551 baseEnd_7278551 := by
    simpa [prefixWord, tailWord_7278551, baseEnd_7278551] using wordTrace_append hprefix tailTrace_7278551
  have hstable : (prefixWord ++ tailWord_7278551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278551).length < 2 ^ (prefixWord ++ tailWord_7278551).sum := by decide
  have hdescent : baseEnd_7278551 < baseStart_7278551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278612 : List Nat := [2, 4, 3, 2, 1, 1, 2, 1, 7]
def baseStart_7278612 : Nat := 118140960795 + 7278612 * 2 ^ 59
def prefixEnd_7278612 : Nat := 4983230072969 + 3 ^ 40 * 7278612 * 2
def baseEnd_7278612 : Nat := 415269605953686847864031

theorem tailTrace_7278612 : CollatzResearch.WordTrace tailWord_7278612 prefixEnd_7278612 415269605953686847864031 := by
  unfold tailWord_7278612
  simp only [CollatzResearch.WordTrace]
  refine ⟨132736394553419643403711045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176981859404559524538281393 132736394553419643403711045)
  ·
    refine ⟨24888073978766183138195821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132736394553419643403711045 24888073978766183138195821)
    ·
      refine ⟨9333027742037318676823433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24888073978766183138195821 9333027742037318676823433)
      ·
        refine ⟨6999770806527989007617575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9333027742037318676823433 6999770806527989007617575)
        ·
          refine ⟨10499656209791983511426363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6999770806527989007617575 10499656209791983511426363)
          ·
            refine ⟨15749484314687975267139545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10499656209791983511426363 15749484314687975267139545)
            ·
              refine ⟨11812113236015981450354659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15749484314687975267139545 11812113236015981450354659)
              ·
                refine ⟨17718169854023972175531989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11812113236015981450354659 17718169854023972175531989)
                ·
                  refine ⟨415269605953686847864031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17718169854023972175531989 415269605953686847864031)
                  ·
                    rfl

theorem cell23_7278612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_7278612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278612 prefixEnd_7278612 := by exact prefixLift 7278612
  have htrace : WordTrace (prefixWord ++ tailWord_7278612) baseStart_7278612 baseEnd_7278612 := by
    simpa [prefixWord, tailWord_7278612, baseEnd_7278612] using wordTrace_append hprefix tailTrace_7278612
  have hstable : (prefixWord ++ tailWord_7278612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278612).length < 2 ^ (prefixWord ++ tailWord_7278612).sum := by decide
  have hdescent : baseEnd_7278612 < baseStart_7278612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278662 : List Nat := [6, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_7278662 : Nat := 118140960795 + 7278662 * 2 ^ 59
def prefixEnd_7278662 : Nat := 4983230072969 + 3 ^ 40 * 7278662 * 2
def baseEnd_7278662 : Nat := 3737452127615906435151049

theorem tailTrace_7278662 : CollatzResearch.WordTrace tailWord_7278662 prefixEnd_7278662 3737452127615906435151049 := by
  unfold tailWord_7278662
  simp only [CollatzResearch.WordTrace]
  refine ⟨8296081648645567042085695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 176983075171105430231161493 8296081648645567042085695)
  ·
    refine ⟨12444122472968350563128543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8296081648645567042085695 12444122472968350563128543)
    ·
      refine ⟨18666183709452525844692815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12444122472968350563128543 18666183709452525844692815)
      ·
        refine ⟨27999275564178788767039223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18666183709452525844692815 27999275564178788767039223)
        ·
          refine ⟨41998913346268183150558835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27999275564178788767039223 41998913346268183150558835)
          ·
            refine ⟨62998370019402274725838253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41998913346268183150558835 62998370019402274725838253)
            ·
              refine ⟨23624388757275853022189345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62998370019402274725838253 23624388757275853022189345)
              ·
                refine ⟨17718291567956889766642009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23624388757275853022189345 17718291567956889766642009)
                ·
                  refine ⟨13288718675967667324981507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17718291567956889766642009 13288718675967667324981507)
                  ·
                    refine ⟨19933078013951500987472261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13288718675967667324981507 19933078013951500987472261)
                    ·
                      refine ⟨3737452127615906435151049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19933078013951500987472261 3737452127615906435151049)
                      ·
                        rfl

theorem cell23_7278662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_7278662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278662 prefixEnd_7278662 := by exact prefixLift 7278662
  have htrace : WordTrace (prefixWord ++ tailWord_7278662) baseStart_7278662 baseEnd_7278662 := by
    simpa [prefixWord, tailWord_7278662, baseEnd_7278662] using wordTrace_append hprefix tailTrace_7278662
  have hstable : (prefixWord ++ tailWord_7278662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278662).length < 2 ^ (prefixWord ++ tailWord_7278662).sum := by decide
  have hdescent : baseEnd_7278662 < baseStart_7278662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278695 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 5, 1, 3]
def baseStart_7278695 : Nat := 118140960795 + 7278695 * 2 ^ 59
def prefixEnd_7278695 : Nat := 4983230072969 + 3 ^ 40 * 7278695 * 2
def baseEnd_7278695 : Nat := 3737469072477504806038397

theorem tailTrace_7278695 : CollatzResearch.WordTrace tailWord_7278695 prefixEnd_7278695 3737469072477504806038397 := by
  unfold tailWord_7278695
  simp only [CollatzResearch.WordTrace]
  refine ⟨265475816365538591982693539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176983877577025727988462359 265475816365538591982693539)
  ·
    refine ⟨398213724548307887974040309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265475816365538591982693539 398213724548307887974040309)
    ·
      refine ⟨37332536676403864497566279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 398213724548307887974040309 37332536676403864497566279)
      ·
        refine ⟨55998805014605796746349419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37332536676403864497566279 55998805014605796746349419)
        ·
          refine ⟨83998207521908695119524129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55998805014605796746349419 83998207521908695119524129)
          ·
            refine ⟨62998655641431521339643097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83998207521908695119524129 62998655641431521339643097)
            ·
              refine ⟨47248991731073641004732323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62998655641431521339643097 47248991731073641004732323)
              ·
                refine ⟨70873487596610461507098485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47248991731073641004732323 70873487596610461507098485)
                ·
                  refine ⟨6644389462182230766290483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70873487596610461507098485 6644389462182230766290483)
                  ·
                    refine ⟨9966584193273346149435725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6644389462182230766290483 9966584193273346149435725)
                    ·
                      refine ⟨3737469072477504806038397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9966584193273346149435725 3737469072477504806038397)
                      ·
                        rfl

theorem cell23_7278695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_7278695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278695 prefixEnd_7278695 := by exact prefixLift 7278695
  have htrace : WordTrace (prefixWord ++ tailWord_7278695) baseStart_7278695 baseEnd_7278695 := by
    simpa [prefixWord, tailWord_7278695, baseEnd_7278695] using wordTrace_append hprefix tailTrace_7278695
  have hstable : (prefixWord ++ tailWord_7278695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278695).length < 2 ^ (prefixWord ++ tailWord_7278695).sum := by decide
  have hdescent : baseEnd_7278695 < baseStart_7278695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278712 : List Nat := [2, 1, 2, 1, 1, 1, 3, 7, 1, 1, 3]
def baseStart_7278712 : Nat := 118140960795 + 7278712 * 2 ^ 59
def prefixEnd_7278712 : Nat := 4983230072969 + 3 ^ 40 * 7278712 * 2
def baseEnd_7278712 : Nat := 3737477801648631239525819

theorem tailTrace_7278712 : CollatzResearch.WordTrace tailWord_7278712 prefixEnd_7278712 3737477801648631239525819 := by
  unfold tailWord_7278712
  simp only [CollatzResearch.WordTrace]
  refine ⟨132738218203238501943031195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176984290937651335924041593 132738218203238501943031195)
  ·
    refine ⟨199107327304857752914546793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132738218203238501943031195 199107327304857752914546793)
    ·
      refine ⟨149330495478643314685910095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199107327304857752914546793 149330495478643314685910095)
      ·
        refine ⟨223995743217964972028865143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149330495478643314685910095 223995743217964972028865143)
        ·
          refine ⟨335993614826947458043297715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223995743217964972028865143 335993614826947458043297715)
          ·
            refine ⟨503990422240421187064946573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335993614826947458043297715 503990422240421187064946573)
            ·
              refine ⟨188996408340157945149354965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 503990422240421187064946573 188996408340157945149354965)
              ·
                refine ⟨4429603320472451839438007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 188996408340157945149354965 4429603320472451839438007)
                ·
                  refine ⟨6644404980708677759157011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4429603320472451839438007 6644404980708677759157011)
                  ·
                    refine ⟨9966607471063016638735517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6644404980708677759157011 9966607471063016638735517)
                    ·
                      refine ⟨3737477801648631239525819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9966607471063016638735517 3737477801648631239525819)
                      ·
                        rfl

theorem cell23_7278712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 7, 1, 1, 3].length) (baseStart_7278712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278712 prefixEnd_7278712 := by exact prefixLift 7278712
  have htrace : WordTrace (prefixWord ++ tailWord_7278712) baseStart_7278712 baseEnd_7278712 := by
    simpa [prefixWord, tailWord_7278712, baseEnd_7278712] using wordTrace_append hprefix tailTrace_7278712
  have hstable : (prefixWord ++ tailWord_7278712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278712).length < 2 ^ (prefixWord ++ tailWord_7278712).sum := by decide
  have hdescent : baseEnd_7278712 < baseStart_7278712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278752 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 5, 2, 2]
def baseStart_7278752 : Nat := 118140960795 + 7278752 * 2 ^ 59
def prefixEnd_7278752 : Nat := 4983230072969 + 3 ^ 40 * 7278752 * 2
def baseEnd_7278752 : Nat := 3737498340874811083025635

theorem tailTrace_7278752 : CollatzResearch.WordTrace tailWord_7278752 prefixEnd_7278752 3737498340874811083025635 := by
  unfold tailWord_7278752
  simp only [CollatzResearch.WordTrace]
  refine ⟨132738947663166045358759255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176985263550888060478345673 132738947663166045358759255)
  ·
    refine ⟨199108421494749068038138883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132738947663166045358759255 199108421494749068038138883)
    ·
      refine ⟨298662632242123602057208325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199108421494749068038138883 298662632242123602057208325)
      ·
        refine ⟨55999243545398175385726561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 298662632242123602057208325 55999243545398175385726561)
        ·
          refine ⟨41999432659048631539294921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55999243545398175385726561 41999432659048631539294921)
          ·
            refine ⟨31499574494286473654471191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41999432659048631539294921 31499574494286473654471191)
            ·
              refine ⟨47249361741429710481706787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31499574494286473654471191 47249361741429710481706787)
              ·
                refine ⟨70874042612144565722560181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47249361741429710481706787 70874042612144565722560181)
                ·
                  refine ⟨6644441494888553036490017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70874042612144565722560181 6644441494888553036490017)
                  ·
                    refine ⟨4983331121166414777367513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6644441494888553036490017 4983331121166414777367513)
                    ·
                      refine ⟨3737498340874811083025635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4983331121166414777367513 3737498340874811083025635)
                      ·
                        rfl

theorem cell23_7278752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_7278752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278752 prefixEnd_7278752 := by exact prefixLift 7278752
  have htrace : WordTrace (prefixWord ++ tailWord_7278752) baseStart_7278752 baseEnd_7278752 := by
    simpa [prefixWord, tailWord_7278752, baseEnd_7278752] using wordTrace_append hprefix tailTrace_7278752
  have hstable : (prefixWord ++ tailWord_7278752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278752).length < 2 ^ (prefixWord ++ tailWord_7278752).sum := by decide
  have hdescent : baseEnd_7278752 < baseStart_7278752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278756 : List Nat := [2, 3, 1, 2, 5, 1, 1, 1, 2, 3, 2]
def baseStart_7278756 : Nat := 118140960795 + 7278756 * 2 ^ 59
def prefixEnd_7278756 : Nat := 4983230072969 + 3 ^ 40 * 7278756 * 2
def baseEnd_7278756 : Nat := 3737500394797429067375617

theorem tailTrace_7278756 : CollatzResearch.WordTrace tailWord_7278756 prefixEnd_7278756 3737500394797429067375617 := by
  unfold tailWord_7278756
  simp only [CollatzResearch.WordTrace]
  refine ⟨132739020609158799700332061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176985360812211732933776081 132739020609158799700332061)
  ·
    refine ⟨49777132728434549887624523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132739020609158799700332061 49777132728434549887624523)
    ·
      refine ⟨74665699092651824831436785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49777132728434549887624523 74665699092651824831436785)
      ·
        refine ⟨55999274319488868623577589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74665699092651824831436785 55999274319488868623577589)
        ·
          refine ⟨5249931967452081433460399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55999274319488868623577589 5249931967452081433460399)
          ·
            refine ⟨7874897951178122150190599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5249931967452081433460399 7874897951178122150190599)
            ·
              refine ⟨11812346926767183225285899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7874897951178122150190599 11812346926767183225285899)
              ·
                refine ⟨17718520390150774837928849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11812346926767183225285899 17718520390150774837928849)
                ·
                  refine ⟨13288890292613081128446637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17718520390150774837928849 13288890292613081128446637)
                  ·
                    refine ⟨4983333859729905423167489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13288890292613081128446637 4983333859729905423167489)
                    ·
                      refine ⟨3737500394797429067375617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4983333859729905423167489 3737500394797429067375617)
                      ·
                        rfl

theorem cell23_7278756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_7278756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278756 prefixEnd_7278756 := by exact prefixLift 7278756
  have htrace : WordTrace (prefixWord ++ tailWord_7278756) baseStart_7278756 baseEnd_7278756 := by
    simpa [prefixWord, tailWord_7278756, baseEnd_7278756] using wordTrace_append hprefix tailTrace_7278756
  have hstable : (prefixWord ++ tailWord_7278756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278756).length < 2 ^ (prefixWord ++ tailWord_7278756).sum := by decide
  have hdescent : baseEnd_7278756 < baseStart_7278756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278796 : List Nat := [2, 2, 1, 6, 1, 1, 3, 1, 2, 4]
def baseStart_7278796 : Nat := 118140960795 + 7278796 * 2 ^ 59
def prefixEnd_7278796 : Nat := 4983230072969 + 3 ^ 40 * 7278796 * 2
def baseEnd_7278796 : Nat := 1245840311341202970291811

theorem tailTrace_7278796 : CollatzResearch.WordTrace tailWord_7278796 prefixEnd_7278796 1245840311341202970291811 := by
  unfold tailWord_7278796
  simp only [CollatzResearch.WordTrace]
  refine ⟨132739750069086343116060121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176986333425448457488080161 132739750069086343116060121)
  ·
    refine ⟨99554812551814757337045091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132739750069086343116060121 99554812551814757337045091)
    ·
      refine ⟨149332218827722136005567637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99554812551814757337045091 149332218827722136005567637)
      ·
        refine ⟨6999947757549475125260983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 149332218827722136005567637 6999947757549475125260983)
        ·
          refine ⟨10499921636324212687891475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6999947757549475125260983 10499921636324212687891475)
          ·
            refine ⟨15749882454486319031837213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10499921636324212687891475 15749882454486319031837213)
            ·
              refine ⟨5906205920432369636938955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15749882454486319031837213 5906205920432369636938955)
              ·
                refine ⟨8859308880648554455408433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5906205920432369636938955 8859308880648554455408433)
                ·
                  refine ⟨6644481660486415841556325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8859308880648554455408433 6644481660486415841556325)
                  ·
                    refine ⟨1245840311341202970291811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6644481660486415841556325 1245840311341202970291811)
                    ·
                      rfl

theorem cell23_7278796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 2, 4].length) (baseStart_7278796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278796 prefixEnd_7278796 := by exact prefixLift 7278796
  have htrace : WordTrace (prefixWord ++ tailWord_7278796) baseStart_7278796 baseEnd_7278796 := by
    simpa [prefixWord, tailWord_7278796, baseEnd_7278796] using wordTrace_append hprefix tailTrace_7278796
  have hstable : (prefixWord ++ tailWord_7278796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278796).length < 2 ^ (prefixWord ++ tailWord_7278796).sum := by decide
  have hdescent : baseEnd_7278796 < baseStart_7278796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278802 : List Nat := [3, 2, 2, 2, 1, 2, 3, 1, 1, 3, 3]
def baseStart_7278802 : Nat := 118140960795 + 7278802 * 2 ^ 59
def prefixEnd_7278802 : Nat := 4983230072969 + 3 ^ 40 * 7278802 * 2
def baseEnd_7278802 : Nat := 3737524014907535887400405

theorem tailTrace_7278802 : CollatzResearch.WordTrace tailWord_7278802 prefixEnd_7278802 3737524014907535887400405 := by
  unfold tailWord_7278802
  simp only [CollatzResearch.WordTrace]
  refine ⟨66369929744037737314209665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176986479317433966171225773 66369929744037737314209665)
  ·
    refine ⟨49777447308028302985657249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66369929744037737314209665 49777447308028302985657249)
    ·
      refine ⟨37333085481021227239242937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49777447308028302985657249 37333085481021227239242937)
      ·
        refine ⟨27999814110765920429432203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37333085481021227239242937 27999814110765920429432203)
        ·
          refine ⟨41999721166148880644148305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27999814110765920429432203 41999721166148880644148305)
          ·
            refine ⟨31499790874611660483111229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41999721166148880644148305 31499790874611660483111229)
            ·
              refine ⟨11812421577979372681166711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31499790874611660483111229 11812421577979372681166711)
              ·
                refine ⟨17718632366969059021750067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11812421577979372681166711 17718632366969059021750067)
                ·
                  refine ⟨26577948550453588532625101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17718632366969059021750067 26577948550453588532625101)
                  ·
                    refine ⟨9966730706420095699734413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26577948550453588532625101 9966730706420095699734413)
                    ·
                      refine ⟨3737524014907535887400405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9966730706420095699734413 3737524014907535887400405)
                      ·
                        rfl

theorem cell23_7278802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_7278802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278802 prefixEnd_7278802 := by exact prefixLift 7278802
  have htrace : WordTrace (prefixWord ++ tailWord_7278802) baseStart_7278802 baseEnd_7278802 := by
    simpa [prefixWord, tailWord_7278802, baseEnd_7278802] using wordTrace_append hprefix tailTrace_7278802
  have hstable : (prefixWord ++ tailWord_7278802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278802).length < 2 ^ (prefixWord ++ tailWord_7278802).sum := by decide
  have hdescent : baseEnd_7278802 < baseStart_7278802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278806 : List Nat := [5, 2, 1, 2, 1, 2, 2, 2, 1, 2, 3]
def baseStart_7278806 : Nat := 118140960795 + 7278806 * 2 ^ 59
def prefixEnd_7278806 : Nat := 4983230072969 + 3 ^ 40 * 7278806 * 2
def baseEnd_7278806 : Nat := 3737526068830153871750387

theorem tailTrace_7278806 : CollatzResearch.WordTrace tailWord_7278806 prefixEnd_7278806 3737526068830153871750387 := by
  unfold tailWord_7278806
  simp only [CollatzResearch.WordTrace]
  refine ⟨16592491554258528621249017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176986576578757638626656181 16592491554258528621249017)
  ·
    refine ⟨12444368665693896465936763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16592491554258528621249017 12444368665693896465936763)
    ·
      refine ⟨18666552998540844698905145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12444368665693896465936763 18666552998540844698905145)
      ·
        refine ⟨13999914748905633524178859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18666552998540844698905145 13999914748905633524178859)
        ·
          refine ⟨20999872123358450286268289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13999914748905633524178859 20999872123358450286268289)
          ·
            refine ⟨15749904092518837714701217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20999872123358450286268289 15749904092518837714701217)
            ·
              refine ⟨11812428069389128286025913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15749904092518837714701217 11812428069389128286025913)
              ·
                refine ⟨8859321052041846214519435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11812428069389128286025913 8859321052041846214519435)
                ·
                  refine ⟨13288981578062769321779153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8859321052041846214519435 13288981578062769321779153)
                  ·
                    refine ⟨9966736183547076991334365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13288981578062769321779153 9966736183547076991334365)
                    ·
                      refine ⟨3737526068830153871750387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9966736183547076991334365 3737526068830153871750387)
                      ·
                        rfl

theorem cell23_7278806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_7278806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278806 prefixEnd_7278806 := by exact prefixLift 7278806
  have htrace : WordTrace (prefixWord ++ tailWord_7278806) baseStart_7278806 baseEnd_7278806 := by
    simpa [prefixWord, tailWord_7278806, baseEnd_7278806] using wordTrace_append hprefix tailTrace_7278806
  have hstable : (prefixWord ++ tailWord_7278806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278806).length < 2 ^ (prefixWord ++ tailWord_7278806).sum := by decide
  have hdescent : baseEnd_7278806 < baseStart_7278806 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278859 : List Nat := [1, 1, 1, 1, 5, 2, 3, 3, 2, 2, 2]
def baseStart_7278859 : Nat := 118140960795 + 7278859 * 2 ^ 59
def prefixEnd_7278859 : Nat := 4983230072969 + 3 ^ 40 * 7278859 * 2
def baseEnd_7278859 : Nat := 3737553283304842164387643

theorem tailTrace_7278859 : CollatzResearch.WordTrace tailWord_7278859 prefixEnd_7278859 3737553283304842164387643 := by
  unfold tailWord_7278859
  simp only [CollatzResearch.WordTrace]
  refine ⟨265481797936944447991663631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176987865291296298661109087 265481797936944447991663631)
  ·
    refine ⟨398222696905416671987495447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265481797936944447991663631 398222696905416671987495447)
    ·
      refine ⟨597334045358125007981243171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398222696905416671987495447 597334045358125007981243171)
      ·
        refine ⟨896001068037187511971864757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597334045358125007981243171 896001068037187511971864757)
        ·
          refine ⟨84000100128486329247362321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 896001068037187511971864757 84000100128486329247362321)
          ·
            refine ⟨63000075096364746935521741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84000100128486329247362321 63000075096364746935521741)
            ·
              refine ⟨23625028161136780100820653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63000075096364746935521741 23625028161136780100820653)
              ·
                refine ⟨8859385560426292537807745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23625028161136780100820653 8859385560426292537807745)
                ·
                  refine ⟨6644539170319719403355809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8859385560426292537807745 6644539170319719403355809)
                  ·
                    refine ⟨4983404377739789552516857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6644539170319719403355809 4983404377739789552516857)
                    ·
                      refine ⟨3737553283304842164387643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4983404377739789552516857 3737553283304842164387643)
                      ·
                        rfl

theorem cell23_7278859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 2, 2, 2].length) (baseStart_7278859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278859 prefixEnd_7278859 := by exact prefixLift 7278859
  have htrace : WordTrace (prefixWord ++ tailWord_7278859) baseStart_7278859 baseEnd_7278859 := by
    simpa [prefixWord, tailWord_7278859, baseEnd_7278859] using wordTrace_append hprefix tailTrace_7278859
  have hstable : (prefixWord ++ tailWord_7278859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278859).length < 2 ^ (prefixWord ++ tailWord_7278859).sum := by decide
  have hdescent : baseEnd_7278859 < baseStart_7278859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278895 : List Nat := [1, 1, 2, 1, 2, 1, 6, 2, 2, 5]
def baseStart_7278895 : Nat := 118140960795 + 7278895 * 2 ^ 59
def prefixEnd_7278895 : Nat := 4983230072969 + 3 ^ 40 * 7278895 * 2
def baseEnd_7278895 : Nat := 1245857256202801341179159

theorem tailTrace_7278895 : CollatzResearch.WordTrace tailWord_7278895 prefixEnd_7278895 1245857256202801341179159 := by
  unfold tailWord_7278895
  simp only [CollatzResearch.WordTrace]
  refine ⟨265483110964814026139974139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176988740643209350759982759 265483110964814026139974139)
  ·
    refine ⟨398224666447221039209961209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265483110964814026139974139 398224666447221039209961209)
    ·
      refine ⟨298668499835415779407470907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398224666447221039209961209 298668499835415779407470907)
      ·
        refine ⟨448002749753123669111206361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298668499835415779407470907 448002749753123669111206361)
        ·
          refine ⟨336002062314842751833404771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448002749753123669111206361 336002062314842751833404771)
          ·
            refine ⟨504003093472264127750107157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336002062314842751833404771 504003093472264127750107157)
            ·
              refine ⟨23625145006512380988286273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 504003093472264127750107157 23625145006512380988286273)
              ·
                refine ⟨17718858754884285741214705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23625145006512380988286273 17718858754884285741214705)
                ·
                  refine ⟨13289144066163214305911029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17718858754884285741214705 13289144066163214305911029)
                  ·
                    refine ⟨1245857256202801341179159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13289144066163214305911029 1245857256202801341179159)
                    ·
                      rfl

theorem cell23_7278895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 5].length) (baseStart_7278895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278895 prefixEnd_7278895 := by exact prefixLift 7278895
  have htrace : WordTrace (prefixWord ++ tailWord_7278895) baseStart_7278895 baseEnd_7278895 := by
    simpa [prefixWord, tailWord_7278895, baseEnd_7278895] using wordTrace_append hprefix tailTrace_7278895
  have hstable : (prefixWord ++ tailWord_7278895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278895).length < 2 ^ (prefixWord ++ tailWord_7278895).sum := by decide
  have hdescent : baseEnd_7278895 < baseStart_7278895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278915 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 4]
def baseStart_7278915 : Nat := 118140960795 + 7278915 * 2 ^ 59
def prefixEnd_7278915 : Nat := 4983230072969 + 3 ^ 40 * 7278915 * 2
def baseEnd_7278915 : Nat := 3737582038221493945287385

theorem tailTrace_7278915 : CollatzResearch.WordTrace tailWord_7278915 prefixEnd_7278915 3737582038221493945287385 := by
  unfold tailWord_7278915
  simp only [CollatzResearch.WordTrace]
  refine ⟨265483840424741569555702199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176989226949827713037134799 265483840424741569555702199)
  ·
    refine ⟨398225760637112354333553299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265483840424741569555702199 398225760637112354333553299)
    ·
      refine ⟨597338640955668531500329949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398225760637112354333553299 597338640955668531500329949)
      ·
        refine ⟨224001990358375699312623731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 597338640955668531500329949 224001990358375699312623731)
        ·
          refine ⟨336002985537563548968935597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224001990358375699312623731 336002985537563548968935597)
          ·
            refine ⟨126001119576586330863350849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 336002985537563548968935597 126001119576586330863350849)
            ·
              refine ⟨94500839682439748147513137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126001119576586330863350849 94500839682439748147513137)
              ·
                refine ⟨70875629761829811110634853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94500839682439748147513137 70875629761829811110634853)
                ·
                  refine ⟨13289180580343089583244035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70875629761829811110634853 13289180580343089583244035)
                  ·
                    refine ⟨19933770870514634374866053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13289180580343089583244035 19933770870514634374866053)
                    ·
                      refine ⟨3737582038221493945287385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19933770870514634374866053 3737582038221493945287385)
                      ·
                        rfl

theorem cell23_7278915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_7278915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278915 prefixEnd_7278915 := by exact prefixLift 7278915
  have htrace : WordTrace (prefixWord ++ tailWord_7278915) baseStart_7278915 baseEnd_7278915 := by
    simpa [prefixWord, tailWord_7278915, baseEnd_7278915] using wordTrace_append hprefix tailTrace_7278915
  have hstable : (prefixWord ++ tailWord_7278915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278915).length < 2 ^ (prefixWord ++ tailWord_7278915).sum := by decide
  have hdescent : baseEnd_7278915 < baseStart_7278915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7278932 : List Nat := [2, 4, 1, 1, 2, 3, 1, 1, 1, 3, 4]
def baseStart_7278932 : Nat := 118140960795 + 7278932 * 2 ^ 59
def prefixEnd_7278932 : Nat := 4983230072969 + 3 ^ 40 * 7278932 * 2
def baseEnd_7278932 : Nat := 3737590767392620378774807

theorem tailTrace_7278932 : CollatzResearch.WordTrace tailWord_7278932 prefixEnd_7278932 3737590767392620378774807 := by
  unfold tailWord_7278932
  simp only [CollatzResearch.WordTrace]
  refine ⟨132742230232839990729535525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176989640310453320972714033 132742230232839990729535525)
  ·
    refine ⟨24889168168657498261787911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132742230232839990729535525 24889168168657498261787911)
    ·
      refine ⟨37333752252986247392681867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24889168168657498261787911 37333752252986247392681867)
      ·
        refine ⟨56000628379479371089022801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37333752252986247392681867 56000628379479371089022801)
        ·
          refine ⟨42000471284609528316767101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56000628379479371089022801 42000471284609528316767101)
          ·
            refine ⟨15750176731728573118787663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42000471284609528316767101 15750176731728573118787663)
            ·
              refine ⟨23625265097592859678181495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15750176731728573118787663 23625265097592859678181495)
              ·
                refine ⟨35437897646389289517272243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23625265097592859678181495 35437897646389289517272243)
                ·
                  refine ⟨53156846469583934275908365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35437897646389289517272243 53156846469583934275908365)
                  ·
                    refine ⟨19933817426093975353465637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53156846469583934275908365 19933817426093975353465637)
                    ·
                      refine ⟨3737590767392620378774807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19933817426093975353465637 3737590767392620378774807)
                      ·
                        rfl

theorem cell23_7278932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_7278932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7278932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7278932 prefixEnd_7278932 := by exact prefixLift 7278932
  have htrace : WordTrace (prefixWord ++ tailWord_7278932) baseStart_7278932 baseEnd_7278932 := by
    simpa [prefixWord, tailWord_7278932, baseEnd_7278932] using wordTrace_append hprefix tailTrace_7278932
  have hstable : (prefixWord ++ tailWord_7278932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7278932).length < 2 ^ (prefixWord ++ tailWord_7278932).sum := by decide
  have hdescent : baseEnd_7278932 < baseStart_7278932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7278932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279036 : List Nat := [2, 2, 2, 4, 1, 3, 1, 2, 1, 5]
def baseStart_7279036 : Nat := 118140960795 + 7279036 * 2 ^ 59
def prefixEnd_7279036 : Nat := 4983230072969 + 3 ^ 40 * 7279036 * 2
def baseEnd_7279036 : Nat := 1245881389793562657291443

theorem tailTrace_7279036 : CollatzResearch.WordTrace tailWord_7279036 prefixEnd_7279036 1245881389793562657291443 := by
  unfold tailWord_7279036
  simp only [CollatzResearch.WordTrace]
  refine ⟨132744126828651603610428481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176992169104868804813904641 132744126828651603610428481)
  ·
    refine ⟨99558095121488702707821361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132744126828651603610428481 99558095121488702707821361)
    ·
      refine ⟨74668571341116527030866021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99558095121488702707821361 74668571341116527030866021)
      ·
        refine ⟨14000357126459348818287379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74668571341116527030866021 14000357126459348818287379)
        ·
          refine ⟨21000535689689023227431069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14000357126459348818287379 21000535689689023227431069)
          ·
            refine ⟨7875200883633383710286651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21000535689689023227431069 7875200883633383710286651)
            ·
              refine ⟨11812801325450075565429977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7875200883633383710286651 11812801325450075565429977)
              ·
                refine ⟨8859600994087556674072483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11812801325450075565429977 8859600994087556674072483)
                ·
                  refine ⟨13289401491131335011108725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8859600994087556674072483 13289401491131335011108725)
                  ·
                    refine ⟨1245881389793562657291443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13289401491131335011108725 1245881389793562657291443)
                    ·
                      rfl

theorem cell23_7279036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_7279036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279036 prefixEnd_7279036 := by exact prefixLift 7279036
  have htrace : WordTrace (prefixWord ++ tailWord_7279036) baseStart_7279036 baseEnd_7279036 := by
    simpa [prefixWord, tailWord_7279036, baseEnd_7279036] using wordTrace_append hprefix tailTrace_7279036
  have hstable : (prefixWord ++ tailWord_7279036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279036).length < 2 ^ (prefixWord ++ tailWord_7279036).sum := by decide
  have hdescent : baseEnd_7279036 < baseStart_7279036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279072 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 3]
def baseStart_7279072 : Nat := 118140960795 + 7279072 * 2 ^ 59
def prefixEnd_7279072 : Nat := 4983230072969 + 3 ^ 40 * 7279072 * 2
def baseEnd_7279072 : Nat := 3737662654684249831024163

theorem tailTrace_7279072 : CollatzResearch.WordTrace tailWord_7279072 prefixEnd_7279072 3737662654684249831024163 := by
  unfold tailWord_7279072
  simp only [CollatzResearch.WordTrace]
  refine ⟨132744783342586392684583735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176993044456781856912778313 132744783342586392684583735)
  ·
    refine ⟨199117175013879589026875603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132744783342586392684583735 199117175013879589026875603)
    ·
      refine ⟨298675762520819383540313405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199117175013879589026875603 298675762520819383540313405)
      ·
        refine ⟨112003410945307268827617527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298675762520819383540313405 112003410945307268827617527)
        ·
          refine ⟨168005116417960903241426291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112003410945307268827617527 168005116417960903241426291)
          ·
            refine ⟨252007674626941354862139437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168005116417960903241426291 252007674626941354862139437)
            ·
              refine ⟨94502877985103008073302289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252007674626941354862139437 94502877985103008073302289)
              ·
                refine ⟨70877158488827256054976717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94502877985103008073302289 70877158488827256054976717)
                ·
                  refine ⟨26578934433310221020616269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70877158488827256054976717 26578934433310221020616269)
                  ·
                    refine ⟨9967100412491332882731101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26578934433310221020616269 9967100412491332882731101)
                    ·
                      refine ⟨3737662654684249831024163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9967100412491332882731101 3737662654684249831024163)
                      ·
                        rfl

theorem cell23_7279072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_7279072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279072 prefixEnd_7279072 := by exact prefixLift 7279072
  have htrace : WordTrace (prefixWord ++ tailWord_7279072) baseStart_7279072 baseEnd_7279072 := by
    simpa [prefixWord, tailWord_7279072, baseEnd_7279072] using wordTrace_append hprefix tailTrace_7279072
  have hstable : (prefixWord ++ tailWord_7279072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279072).length < 2 ^ (prefixWord ++ tailWord_7279072).sum := by decide
  have hdescent : baseEnd_7279072 < baseStart_7279072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279073 : List Nat := [1, 2, 3, 1, 2, 2, 3, 4, 1, 2, 2]
def baseStart_7279073 : Nat := 118140960795 + 7279073 * 2 ^ 59
def prefixEnd_7279073 : Nat := 4983230072969 + 3 ^ 40 * 7279073 * 2
def baseEnd_7279073 : Nat := 3737663168164904327111659

theorem tailTrace_7279073 : CollatzResearch.WordTrace tailWord_7279073 prefixEnd_7279073 3737663168164904327111659 := by
  unfold tailWord_7279073
  simp only [CollatzResearch.WordTrace]
  refine ⟨265489603158169162539953873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176993068772112775026635915 265489603158169162539953873)
  ·
    refine ⟨199117202368626871904965405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265489603158169162539953873 199117202368626871904965405)
    ·
      refine ⟨74668950888235076964362027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199117202368626871904965405 74668950888235076964362027)
      ·
        refine ⟨112003426332352615446543041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74668950888235076964362027 112003426332352615446543041)
        ·
          refine ⟨84002569749264461584907281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112003426332352615446543041 84002569749264461584907281)
          ·
            refine ⟨63001927311948346188680461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84002569749264461584907281 63001927311948346188680461)
            ·
              refine ⟨23625722741980629820755173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63001927311948346188680461 23625722741980629820755173)
              ·
                refine ⟨4429823014121368091391595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23625722741980629820755173 4429823014121368091391595)
                ·
                  refine ⟨6644734521182052137087393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4429823014121368091391595 6644734521182052137087393)
                  ·
                    refine ⟨4983550890886539102815545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6644734521182052137087393 4983550890886539102815545)
                    ·
                      refine ⟨3737663168164904327111659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4983550890886539102815545 3737663168164904327111659)
                      ·
                        rfl

theorem cell23_7279073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 4, 1, 2, 2].length) (baseStart_7279073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279073 prefixEnd_7279073 := by exact prefixLift 7279073
  have htrace : WordTrace (prefixWord ++ tailWord_7279073) baseStart_7279073 baseEnd_7279073 := by
    simpa [prefixWord, tailWord_7279073, baseEnd_7279073] using wordTrace_append hprefix tailTrace_7279073
  have hstable : (prefixWord ++ tailWord_7279073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279073).length < 2 ^ (prefixWord ++ tailWord_7279073).sum := by decide
  have hdescent : baseEnd_7279073 < baseStart_7279073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279089 : List Nat := [1, 2, 2, 2, 3, 1, 4, 1, 1, 3, 3]
def baseStart_7279089 : Nat := 118140960795 + 7279089 * 2 ^ 59
def prefixEnd_7279089 : Nat := 4983230072969 + 3 ^ 40 * 7279089 * 2
def baseEnd_7279089 : Nat := 3737671383855376264511585

theorem tailTrace_7279089 : CollatzResearch.WordTrace tailWord_7279089 prefixEnd_7279089 3737671383855376264511585 := by
  unfold tailWord_7279089
  simp only [CollatzResearch.WordTrace]
  refine ⟨265490186726111197272536321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176993457817407464848357547 265490186726111197272536321)
  ·
    refine ⟨199117640044583397954402241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265490186726111197272536321 199117640044583397954402241)
    ·
      refine ⟨149338230033437548465801681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199117640044583397954402241 149338230033437548465801681)
      ·
        refine ⟨112003672525078161349351261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149338230033437548465801681 112003672525078161349351261)
        ·
          refine ⟨42001377196904310506006723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112003672525078161349351261 42001377196904310506006723)
          ·
            refine ⟨63002065795356465759010085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42001377196904310506006723 63002065795356465759010085)
            ·
              refine ⟨11812887336629337329814391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63002065795356465759010085 11812887336629337329814391)
              ·
                refine ⟨17719331004944005994721587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11812887336629337329814391 17719331004944005994721587)
                ·
                  refine ⟨26578996507416008992082381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17719331004944005994721587 26578996507416008992082381)
                  ·
                    refine ⟨9967123690281003372030893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26578996507416008992082381 9967123690281003372030893)
                    ·
                      refine ⟨3737671383855376264511585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9967123690281003372030893 3737671383855376264511585)
                      ·
                        rfl

theorem cell23_7279089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_7279089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279089 prefixEnd_7279089 := by exact prefixLift 7279089
  have htrace : WordTrace (prefixWord ++ tailWord_7279089) baseStart_7279089 baseEnd_7279089 := by
    simpa [prefixWord, tailWord_7279089, baseEnd_7279089] using wordTrace_append hprefix tailTrace_7279089
  have hstable : (prefixWord ++ tailWord_7279089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279089).length < 2 ^ (prefixWord ++ tailWord_7279089).sum := by decide
  have hdescent : baseEnd_7279089 < baseStart_7279089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279140 : List Nat := [2, 3, 1, 5, 2, 1, 1, 1, 1, 3, 3]
def baseStart_7279140 : Nat := 118140960795 + 7279140 * 2 ^ 59
def prefixEnd_7279140 : Nat := 4983230072969 + 3 ^ 40 * 7279140 * 2
def baseEnd_7279140 : Nat := 3737697571368755564973851

theorem tailTrace_7279140 : CollatzResearch.WordTrace tailWord_7279140 prefixEnd_7279140 3737697571368755564973851 := by
  unfold tailWord_7279140
  simp only [CollatzResearch.WordTrace]
  refine ⟨132746023424463216491321437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176994697899284288655095249 132746023424463216491321437)
  ·
    refine ⟨49779758784173706184245539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132746023424463216491321437 49779758784173706184245539)
    ·
      refine ⟨74669638176260559276368309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49779758784173706184245539 74669638176260559276368309)
      ·
        refine ⟨7000278579024427432159529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74669638176260559276368309 7000278579024427432159529)
        ·
          refine ⟨5250208934268320574119647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7000278579024427432159529 5250208934268320574119647)
          ·
            refine ⟨7875313401402480861179471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5250208934268320574119647 7875313401402480861179471)
            ·
              refine ⟨11812970102103721291769207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7875313401402480861179471 11812970102103721291769207)
              ·
                refine ⟨17719455153155581937653811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11812970102103721291769207 17719455153155581937653811)
                ·
                  refine ⟨26579182729733372906480717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17719455153155581937653811 26579182729733372906480717)
                  ·
                    refine ⟨9967193523650014839930269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26579182729733372906480717 9967193523650014839930269)
                    ·
                      refine ⟨3737697571368755564973851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9967193523650014839930269 3737697571368755564973851)
                      ·
                        rfl

theorem cell23_7279140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_7279140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279140 prefixEnd_7279140 := by exact prefixLift 7279140
  have htrace : WordTrace (prefixWord ++ tailWord_7279140) baseStart_7279140 baseEnd_7279140 := by
    simpa [prefixWord, tailWord_7279140, baseEnd_7279140] using wordTrace_append hprefix tailTrace_7279140
  have hstable : (prefixWord ++ tailWord_7279140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279140).length < 2 ^ (prefixWord ++ tailWord_7279140).sum := by decide
  have hdescent : baseEnd_7279140 < baseStart_7279140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279150 : List Nat := [4, 1, 3, 1, 3, 1, 2, 2, 1, 3, 2]
def baseStart_7279150 : Nat := 118140960795 + 7279150 * 2 ^ 59
def prefixEnd_7279150 : Nat := 4983230072969 + 3 ^ 40 * 7279150 * 2
def baseEnd_7279150 : Nat := 3737702706175300525848805

theorem tailTrace_7279150 : CollatzResearch.WordTrace tailWord_7279150 prefixEnd_7279150 3737702706175300525848805 := by
  unfold tailWord_7279150
  simp only [CollatzResearch.WordTrace]
  refine ⟨33186551447361275586313363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176994941052593469793671269 33186551447361275586313363)
  ·
    refine ⟨49779827171041913379470045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33186551447361275586313363 49779827171041913379470045)
    ·
      refine ⟨18667435189140717517301267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49779827171041913379470045 18667435189140717517301267)
      ·
        refine ⟨28001152783711076275951901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18667435189140717517301267 28001152783711076275951901)
        ·
          refine ⟨10500432293891653603481963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28001152783711076275951901 10500432293891653603481963)
          ·
            refine ⟨15750648440837480405222945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10500432293891653603481963 15750648440837480405222945)
            ·
              refine ⟨11812986330628110303917209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15750648440837480405222945 11812986330628110303917209)
              ·
                refine ⟨8859739747971082727937907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11812986330628110303917209 8859739747971082727937907)
                ·
                  refine ⟨13289609621956624091906861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8859739747971082727937907 13289609621956624091906861)
                  ·
                    refine ⟨4983603608233734034465073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13289609621956624091906861 4983603608233734034465073)
                    ·
                      refine ⟨3737702706175300525848805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4983603608233734034465073 3737702706175300525848805)
                      ·
                        rfl

theorem cell23_7279150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_7279150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279150 prefixEnd_7279150 := by exact prefixLift 7279150
  have htrace : WordTrace (prefixWord ++ tailWord_7279150) baseStart_7279150 baseEnd_7279150 := by
    simpa [prefixWord, tailWord_7279150, baseEnd_7279150] using wordTrace_append hprefix tailTrace_7279150
  have hstable : (prefixWord ++ tailWord_7279150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279150).length < 2 ^ (prefixWord ++ tailWord_7279150).sum := by decide
  have hdescent : baseEnd_7279150 < baseStart_7279150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279152 : List Nat := [2, 1, 1, 1, 2, 3, 4, 2, 7]
def baseStart_7279152 : Nat := 118140960795 + 7279152 * 2 ^ 59
def prefixEnd_7279152 : Nat := 4983230072969 + 3 ^ 40 * 7279152 * 2
def baseEnd_7279152 : Nat := 415300414792956613113755

theorem tailTrace_7279152 : CollatzResearch.WordTrace tailWord_7279152 prefixEnd_7279152 415300414792956613113755 := by
  unfold tailWord_7279152
  simp only [CollatzResearch.WordTrace]
  refine ⟨132746242262441479516039855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176994989683255306021386473 132746242262441479516039855)
  ·
    refine ⟨199119363393662219274059783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132746242262441479516039855 199119363393662219274059783)
    ·
      refine ⟨298679045090493328911089675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199119363393662219274059783 298679045090493328911089675)
      ·
        refine ⟨448018567635739993366634513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298679045090493328911089675 448018567635739993366634513)
        ·
          refine ⟨336013925726804995024975885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448018567635739993366634513 336013925726804995024975885)
          ·
            refine ⟨126005222147551873134365957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 336013925726804995024975885 126005222147551873134365957)
            ·
              refine ⟨23625979152665976212693617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126005222147551873134365957 23625979152665976212693617)
              ·
                refine ⟨17719484364499482159520213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23625979152665976212693617 17719484364499482159520213)
                ·
                  refine ⟨415300414792956613113755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17719484364499482159520213 415300414792956613113755)
                  ·
                    rfl

theorem cell23_7279152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 7].length) (baseStart_7279152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279152 prefixEnd_7279152 := by exact prefixLift 7279152
  have htrace : WordTrace (prefixWord ++ tailWord_7279152) baseStart_7279152 baseEnd_7279152 := by
    simpa [prefixWord, tailWord_7279152, baseEnd_7279152] using wordTrace_append hprefix tailTrace_7279152
  have hstable : (prefixWord ++ tailWord_7279152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279152).length < 2 ^ (prefixWord ++ tailWord_7279152).sum := by decide
  have hdescent : baseEnd_7279152 < baseStart_7279152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279192 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 1, 1, 7]
def baseStart_7279192 : Nat := 118140960795 + 7279192 * 2 ^ 59
def prefixEnd_7279192 : Nat := 4983230072969 + 3 ^ 40 * 7279192 * 2
def baseEnd_7279192 : Nat := 3737724272362789361523611

theorem tailTrace_7279192 : CollatzResearch.WordTrace tailWord_7279192 prefixEnd_7279192 3737724272362789361523611 := by
  unfold tailWord_7279192
  simp only [CollatzResearch.WordTrace]
  refine ⟨132746971722369022931767915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176995962296492030575690553 132746971722369022931767915)
  ·
    refine ⟨199120457583553534397651873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132746971722369022931767915 199120457583553534397651873)
    ·
      refine ⟨149340343187665150798238905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199120457583553534397651873 149340343187665150798238905)
      ·
        refine ⟨112005257390748863098679179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149340343187665150798238905 112005257390748863098679179)
        ·
          refine ⟨168007886086123294648018769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112005257390748863098679179 168007886086123294648018769)
          ·
            refine ⟨126005914564592470986014077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168007886086123294648018769 126005914564592470986014077)
            ·
              refine ⟨47252217961722176619755279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126005914564592470986014077 47252217961722176619755279)
              ·
                refine ⟨70878326942583264929632919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47252217961722176619755279 70878326942583264929632919)
                ·
                  refine ⟨106317490413874897394449379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70878326942583264929632919 106317490413874897394449379)
                  ·
                    refine ⟨159476235620812346091674069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106317490413874897394449379 159476235620812346091674069)
                    ·
                      refine ⟨3737724272362789361523611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 159476235620812346091674069 3737724272362789361523611)
                      ·
                        rfl

theorem cell23_7279192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_7279192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279192 prefixEnd_7279192 := by exact prefixLift 7279192
  have htrace : WordTrace (prefixWord ++ tailWord_7279192) baseStart_7279192 baseEnd_7279192 := by
    simpa [prefixWord, tailWord_7279192, baseEnd_7279192] using wordTrace_append hprefix tailTrace_7279192
  have hstable : (prefixWord ++ tailWord_7279192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279192).length < 2 ^ (prefixWord ++ tailWord_7279192).sum := by decide
  have hdescent : baseEnd_7279192 < baseStart_7279192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279212 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 2, 8]
def baseStart_7279212 : Nat := 118140960795 + 7279212 * 2 ^ 59
def prefixEnd_7279212 : Nat := 4983230072969 + 3 ^ 40 * 7279212 * 2
def baseEnd_7279212 : Nat := 1245911513991959761091173

theorem tailTrace_7279212 : CollatzResearch.WordTrace tailWord_7279212 prefixEnd_7279212 1245911513991959761091173 := by
  unfold tailWord_7279212
  simp only [CollatzResearch.WordTrace]
  refine ⟨132747336452332794639631945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176996448603110392852842593 132747336452332794639631945)
  ·
    refine ⟨99560502339249595979723959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132747336452332794639631945 99560502339249595979723959)
    ·
      refine ⟨149340753508874393969585939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99560502339249595979723959 149340753508874393969585939)
      ·
        refine ⟨224011130263311590954378909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149340753508874393969585939 224011130263311590954378909)
        ·
          refine ⟨84004173848741846607892091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224011130263311590954378909 84004173848741846607892091)
          ·
            refine ⟨126006260773112769911838137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84004173848741846607892091 126006260773112769911838137)
            ·
              refine ⟨94504695579834577433878603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126006260773112769911838137 94504695579834577433878603)
              ·
                refine ⟨141757043369751866150817905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94504695579834577433878603 141757043369751866150817905)
                ·
                  refine ⟨106317782527313899613113429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141757043369751866150817905 106317782527313899613113429)
                  ·
                    refine ⟨1245911513991959761091173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 106317782527313899613113429 1245911513991959761091173)
                    ·
                      rfl

theorem cell23_7279212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 8].length) (baseStart_7279212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279212 prefixEnd_7279212 := by exact prefixLift 7279212
  have htrace : WordTrace (prefixWord ++ tailWord_7279212) baseStart_7279212 baseEnd_7279212 := by
    simpa [prefixWord, tailWord_7279212, baseEnd_7279212] using wordTrace_append hprefix tailTrace_7279212
  have hstable : (prefixWord ++ tailWord_7279212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279212).length < 2 ^ (prefixWord ++ tailWord_7279212).sum := by decide
  have hdescent : baseEnd_7279212 < baseStart_7279212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279216 : List Nat := [2, 1, 1, 1, 7, 1, 2, 1, 2, 5]
def baseStart_7279216 : Nat := 118140960795 + 7279216 * 2 ^ 59
def prefixEnd_7279216 : Nat := 4983230072969 + 3 ^ 40 * 7279216 * 2
def baseEnd_7279216 : Nat := 1245912198632832422541167

theorem tailTrace_7279216 : CollatzResearch.WordTrace tailWord_7279216 prefixEnd_7279216 1245912198632832422541167 := by
  unfold tailWord_7279216
  simp only [CollatzResearch.WordTrace]
  refine ⟨132747409398325548981204751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176996545864434065308273001 132747409398325548981204751)
  ·
    refine ⟨199121114097488323471807127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132747409398325548981204751 199121114097488323471807127)
    ·
      refine ⟨298681671146232485207710691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199121114097488323471807127 298681671146232485207710691)
      ·
        refine ⟨448022506719348727811566037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298681671146232485207710691 448022506719348727811566037)
        ·
          refine ⟨10500527501234735808083579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 448022506719348727811566037 10500527501234735808083579)
          ·
            refine ⟨15750791251852103712125369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10500527501234735808083579 15750791251852103712125369)
            ·
              refine ⟨11813093438889077784094027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15750791251852103712125369 11813093438889077784094027)
              ·
                refine ⟨17719640158333616676141041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11813093438889077784094027 17719640158333616676141041)
                ·
                  refine ⟨13289730118750212507105781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17719640158333616676141041 13289730118750212507105781)
                  ·
                    refine ⟨1245912198632832422541167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13289730118750212507105781 1245912198632832422541167)
                    ·
                      rfl

theorem cell23_7279216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 2, 5].length) (baseStart_7279216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279216 prefixEnd_7279216 := by exact prefixLift 7279216
  have htrace : WordTrace (prefixWord ++ tailWord_7279216) baseStart_7279216 baseEnd_7279216 := by
    simpa [prefixWord, tailWord_7279216, baseEnd_7279216] using wordTrace_append hprefix tailTrace_7279216
  have hstable : (prefixWord ++ tailWord_7279216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279216).length < 2 ^ (prefixWord ++ tailWord_7279216).sum := by decide
  have hdescent : baseEnd_7279216 < baseStart_7279216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279219 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 3, 6, 2]
def baseStart_7279219 : Nat := 118140960795 + 7279219 * 2 ^ 59
def prefixEnd_7279219 : Nat := 4983230072969 + 3 ^ 40 * 7279219 * 2
def baseEnd_7279219 : Nat := 3737738136340460755885987

theorem tailTrace_7279219 : CollatzResearch.WordTrace tailWord_7279219 prefixEnd_7279219 3737738136340460755885987 := by
  unfold tailWord_7279219
  simp only [CollatzResearch.WordTrace]
  refine ⟨265494928215640229474768711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176996618810426819649845807 265494928215640229474768711)
  ·
    refine ⟨398242392323460344212153067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265494928215640229474768711 398242392323460344212153067)
    ·
      refine ⟨597363588485190516318229601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398242392323460344212153067 597363588485190516318229601)
      ·
        refine ⟨448022691363892887238672201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 597363588485190516318229601 448022691363892887238672201)
        ·
          refine ⟨336017018522919665429004151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448022691363892887238672201 336017018522919665429004151)
          ·
            refine ⟨504025527784379498143506227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336017018522919665429004151 504025527784379498143506227)
            ·
              refine ⟨756038291676569247215259341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504025527784379498143506227 756038291676569247215259341)
              ·
                refine ⟨283514359378713467705722253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 756038291676569247215259341 283514359378713467705722253)
                ·
                  refine ⟨106317884767017550389645845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 283514359378713467705722253 106317884767017550389645845)
                  ·
                    refine ⟨4983650848453947674514649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106317884767017550389645845 4983650848453947674514649)
                    ·
                      refine ⟨3737738136340460755885987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4983650848453947674514649 3737738136340460755885987)
                      ·
                        rfl

theorem cell23_7279219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 6, 2].length) (baseStart_7279219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279219 prefixEnd_7279219 := by exact prefixLift 7279219
  have htrace : WordTrace (prefixWord ++ tailWord_7279219) baseStart_7279219 baseEnd_7279219 := by
    simpa [prefixWord, tailWord_7279219, baseEnd_7279219] using wordTrace_append hprefix tailTrace_7279219
  have hstable : (prefixWord ++ tailWord_7279219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279219).length < 2 ^ (prefixWord ++ tailWord_7279219).sum := by decide
  have hdescent : baseEnd_7279219 < baseStart_7279219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279236 : List Nat := [2, 3, 2, 1, 3, 1, 2, 2, 2, 1, 4]
def baseStart_7279236 : Nat := 118140960795 + 7279236 * 2 ^ 59
def prefixEnd_7279236 : Nat := 4983230072969 + 3 ^ 40 * 7279236 * 2
def baseEnd_7279236 : Nat := 3737746865511587189373409

theorem tailTrace_7279236 : CollatzResearch.WordTrace tailWord_7279236 prefixEnd_7279236 3737746865511587189373409 := by
  unfold tailWord_7279236
  simp only [CollatzResearch.WordTrace]
  refine ⟨132747774128289320689068781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176997032171052427585425041 132747774128289320689068781)
  ·
    refine ⟨49780415298108495258400793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132747774128289320689068781 49780415298108495258400793)
    ·
      refine ⟨37335311473581371443800595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49780415298108495258400793 37335311473581371443800595)
      ·
        refine ⟨56002967210372057165700893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37335311473581371443800595 56002967210372057165700893)
        ·
          refine ⟨21001112703889521437137835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56002967210372057165700893 21001112703889521437137835)
          ·
            refine ⟨31501669055834282155706753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21001112703889521437137835 31501669055834282155706753)
            ·
              refine ⟨23626251791875711616780065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31501669055834282155706753 23626251791875711616780065)
              ·
                refine ⟨17719688843906783712585049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23626251791875711616780065 17719688843906783712585049)
                ·
                  refine ⟨13289766632930087784438787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17719688843906783712585049 13289766632930087784438787)
                  ·
                    refine ⟨19934649949395131676658181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13289766632930087784438787 19934649949395131676658181)
                    ·
                      refine ⟨3737746865511587189373409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19934649949395131676658181 3737746865511587189373409)
                      ·
                        rfl

theorem cell23_7279236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_7279236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279236 prefixEnd_7279236 := by exact prefixLift 7279236
  have htrace : WordTrace (prefixWord ++ tailWord_7279236) baseStart_7279236 baseEnd_7279236 := by
    simpa [prefixWord, tailWord_7279236, baseEnd_7279236] using wordTrace_append hprefix tailTrace_7279236
  have hstable : (prefixWord ++ tailWord_7279236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279236).length < 2 ^ (prefixWord ++ tailWord_7279236).sum := by decide
  have hdescent : baseEnd_7279236 < baseStart_7279236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279246 : List Nat := [4, 1, 1, 3, 1, 1, 2, 3, 3, 4]
def baseStart_7279246 : Nat := 118140960795 + 7279246 * 2 ^ 59
def prefixEnd_7279246 : Nat := 4983230072969 + 3 ^ 40 * 7279246 * 2
def baseEnd_7279246 : Nat := 1245917333439377383416121

theorem tailTrace_7279246 : CollatzResearch.WordTrace tailWord_7279246 prefixEnd_7279246 1245917333439377383416121 := by
  unfold tailWord_7279246
  simp only [CollatzResearch.WordTrace]
  refine ⟨33186989123317801635750199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176997275324361608724001061 33186989123317801635750199)
  ·
    refine ⟨49780483684976702453625299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33186989123317801635750199 49780483684976702453625299)
    ·
      refine ⟨74670725527465053680437949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49780483684976702453625299 74670725527465053680437949)
      ·
        refine ⟨28001522072799395130164231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74670725527465053680437949 28001522072799395130164231)
        ·
          refine ⟨42002283109199092695246347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28001522072799395130164231 42002283109199092695246347)
          ·
            refine ⟨63003424663798639042869521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42002283109199092695246347 63003424663798639042869521)
            ·
              refine ⟨47252568497848979282152141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63003424663798639042869521 47252568497848979282152141)
              ·
                refine ⟨17719713186693367230807053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47252568497848979282152141 17719713186693367230807053)
                ·
                  refine ⟨6644892445010012711552645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17719713186693367230807053 6644892445010012711552645)
                  ·
                    refine ⟨1245917333439377383416121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6644892445010012711552645 1245917333439377383416121)
                    ·
                      rfl

theorem cell23_7279246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_7279246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279246 prefixEnd_7279246 := by exact prefixLift 7279246
  have htrace : WordTrace (prefixWord ++ tailWord_7279246) baseStart_7279246 baseEnd_7279246 := by
    simpa [prefixWord, tailWord_7279246, baseEnd_7279246] using wordTrace_append hprefix tailTrace_7279246
  have hstable : (prefixWord ++ tailWord_7279246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279246).length < 2 ^ (prefixWord ++ tailWord_7279246).sum := by decide
  have hdescent : baseEnd_7279246 < baseStart_7279246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279339 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 4]
def baseStart_7279339 : Nat := 118140960795 + 7279339 * 2 ^ 59
def prefixEnd_7279339 : Nat := 4983230072969 + 3 ^ 40 * 7279339 * 2
def baseEnd_7279339 : Nat := 3737799754019000286385435

theorem tailTrace_7279339 : CollatzResearch.WordTrace tailWord_7279339 prefixEnd_7279339 3737799754019000286385435 := by
  unfold tailWord_7279339
  simp only [CollatzResearch.WordTrace]
  refine ⟨265499304975205489969137071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176999536650136993312758047 265499304975205489969137071)
  ·
    refine ⟨398248957462808234953705607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265499304975205489969137071 398248957462808234953705607)
    ·
      refine ⟨597373436194212352430558411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398248957462808234953705607 597373436194212352430558411)
      ·
        refine ⟨896060154291318528645837617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597373436194212352430558411 896060154291318528645837617)
        ·
          refine ⟨672045115718488896484378213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 896060154291318528645837617 672045115718488896484378213)
          ·
            refine ⟨126008459197216668090820915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 672045115718488896484378213 126008459197216668090820915)
            ·
              refine ⟨189012688795825002136231373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126008459197216668090820915 189012688795825002136231373)
              ·
                refine ⟨70879758298434375801086765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189012688795825002136231373 70879758298434375801086765)
                ·
                  refine ⟨26579909361912890925407537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70879758298434375801086765 26579909361912890925407537)
                  ·
                    refine ⟨19934932021434668194055653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26579909361912890925407537 19934932021434668194055653)
                    ·
                      refine ⟨3737799754019000286385435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19934932021434668194055653 3737799754019000286385435)
                      ·
                        rfl

theorem cell23_7279339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 4].length) (baseStart_7279339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279339 prefixEnd_7279339 := by exact prefixLift 7279339
  have htrace : WordTrace (prefixWord ++ tailWord_7279339) baseStart_7279339 baseEnd_7279339 := by
    simpa [prefixWord, tailWord_7279339, baseEnd_7279339] using wordTrace_append hprefix tailTrace_7279339
  have hstable : (prefixWord ++ tailWord_7279339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279339).length < 2 ^ (prefixWord ++ tailWord_7279339).sum := by decide
  have hdescent : baseEnd_7279339 < baseStart_7279339 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279346 : List Nat := [3, 2, 1, 3, 1, 2, 1, 3, 1, 1, 5]
def baseStart_7279346 : Nat := 118140960795 + 7279346 * 2 ^ 59
def prefixEnd_7279346 : Nat := 4983230072969 + 3 ^ 40 * 7279346 * 2
def baseEnd_7279346 : Nat := 3737803348383581758997903

theorem tailTrace_7279346 : CollatzResearch.WordTrace tailWord_7279346 prefixEnd_7279346 3737803348383581758997903 := by
  unfold tailWord_7279346
  simp only [CollatzResearch.WordTrace]
  refine ⟨66374890071545032541160473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176999706857453420109761261 66374890071545032541160473)
  ·
    refine ⟨49781167553658774405870355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66374890071545032541160473 49781167553658774405870355)
    ·
      refine ⟨74671751330488161608805533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49781167553658774405870355 74671751330488161608805533)
      ·
        refine ⟨28001906748933060603302075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74671751330488161608805533 28001906748933060603302075)
        ·
          refine ⟨42002860123399590904953113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28001906748933060603302075 42002860123399590904953113)
          ·
            refine ⟨31502145092549693178714835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42002860123399590904953113 31502145092549693178714835)
            ·
              refine ⟨47253217638824539768072253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31502145092549693178714835 47253217638824539768072253)
              ·
                refine ⟨17719956614559202413027095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47253217638824539768072253 17719956614559202413027095)
                ·
                  refine ⟨26579934921838803619540643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17719956614559202413027095 26579934921838803619540643)
                  ·
                    refine ⟨39869902382758205429310965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26579934921838803619540643 39869902382758205429310965)
                    ·
                      refine ⟨3737803348383581758997903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39869902382758205429310965 3737803348383581758997903)
                      ·
                        rfl

theorem cell23_7279346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_7279346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279346 prefixEnd_7279346 := by exact prefixLift 7279346
  have htrace : WordTrace (prefixWord ++ tailWord_7279346) baseStart_7279346 baseEnd_7279346 := by
    simpa [prefixWord, tailWord_7279346, baseEnd_7279346] using wordTrace_append hprefix tailTrace_7279346
  have hstable : (prefixWord ++ tailWord_7279346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279346).length < 2 ^ (prefixWord ++ tailWord_7279346).sum := by decide
  have hdescent : baseEnd_7279346 < baseStart_7279346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279410 : List Nat := [3, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3]
def baseStart_7279410 : Nat := 118140960795 + 7279410 * 2 ^ 59
def prefixEnd_7279410 : Nat := 4983230072969 + 3 ^ 40 * 7279410 * 2
def baseEnd_7279410 : Nat := 3737836211145469508597609

theorem tailTrace_7279410 : CollatzResearch.WordTrace tailWord_7279410 prefixEnd_7279410 3737836211145469508597609 := by
  unfold tailWord_7279410
  simp only [CollatzResearch.WordTrace]
  refine ⟨66375473639487067273742921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177001263038632179396647789 66375473639487067273742921)
  ·
    refine ⟨49781605229615300455307191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66375473639487067273742921 49781605229615300455307191)
    ·
      refine ⟨74672407844422950682960787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49781605229615300455307191 74672407844422950682960787)
      ·
        refine ⟨112008611766634426024441181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74672407844422950682960787 112008611766634426024441181)
        ·
          refine ⟨42003229412487909759165443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112008611766634426024441181 42003229412487909759165443)
          ·
            refine ⟨63004844118731864638748165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42003229412487909759165443 63004844118731864638748165)
            ·
              refine ⟨11813408272262224619765281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63004844118731864638748165 11813408272262224619765281)
              ·
                refine ⟨8860056204196668464823961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11813408272262224619765281 8860056204196668464823961)
                ·
                  refine ⟨6645042153147501348617971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8860056204196668464823961 6645042153147501348617971)
                  ·
                    refine ⟨9967563229721252022926957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6645042153147501348617971 9967563229721252022926957)
                    ·
                      refine ⟨3737836211145469508597609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9967563229721252022926957 3737836211145469508597609)
                      ·
                        rfl

theorem cell23_7279410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_7279410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279410 prefixEnd_7279410 := by exact prefixLift 7279410
  have htrace : WordTrace (prefixWord ++ tailWord_7279410) baseStart_7279410 baseEnd_7279410 := by
    simpa [prefixWord, tailWord_7279410, baseEnd_7279410] using wordTrace_append hprefix tailTrace_7279410
  have hstable : (prefixWord ++ tailWord_7279410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279410).length < 2 ^ (prefixWord ++ tailWord_7279410).sum := by decide
  have hdescent : baseEnd_7279410 < baseStart_7279410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279433 : List Nat := [1, 2, 1, 1, 2, 5, 1, 3, 1, 4, 2]
def baseStart_7279433 : Nat := 118140960795 + 7279433 * 2 ^ 59
def prefixEnd_7279433 : Nat := 4983230072969 + 3 ^ 40 * 7279433 * 2
def baseEnd_7279433 : Nat := 3737848021200522918610003

theorem tailTrace_7279433 : CollatzResearch.WordTrace tailWord_7279433 prefixEnd_7279433 3737848021200522918610003 := by
  unfold tailWord_7279433
  simp only [CollatzResearch.WordTrace]
  refine ⟨265502733436864944023058953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177001822291243296015372635 265502733436864944023058953)
  ·
    refine ⟨199127050077648708017294215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265502733436864944023058953 199127050077648708017294215)
    ·
      refine ⟨298690575116473062025941323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199127050077648708017294215 298690575116473062025941323)
      ·
        refine ⟨448035862674709593038911985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298690575116473062025941323 448035862674709593038911985)
        ·
          refine ⟨336026897006032194779183989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448035862674709593038911985 336026897006032194779183989)
          ·
            refine ⟨31502521594315518260548499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 336026897006032194779183989 31502521594315518260548499)
            ·
              refine ⟨47253782391473277390822749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31502521594315518260548499 47253782391473277390822749)
              ·
                refine ⟨17720168396802479021558531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47253782391473277390822749 17720168396802479021558531)
                ·
                  refine ⟨26580252595203718532337797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17720168396802479021558531 26580252595203718532337797)
                  ·
                    refine ⟨4983797361600697224813337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26580252595203718532337797 4983797361600697224813337)
                    ·
                      refine ⟨3737848021200522918610003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4983797361600697224813337 3737848021200522918610003)
                      ·
                        rfl

theorem cell23_7279433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 4, 2].length) (baseStart_7279433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279433 prefixEnd_7279433 := by exact prefixLift 7279433
  have htrace : WordTrace (prefixWord ++ tailWord_7279433) baseStart_7279433 baseEnd_7279433 := by
    simpa [prefixWord, tailWord_7279433, baseEnd_7279433] using wordTrace_append hprefix tailTrace_7279433
  have hstable : (prefixWord ++ tailWord_7279433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279433).length < 2 ^ (prefixWord ++ tailWord_7279433).sum := by decide
  have hdescent : baseEnd_7279433 < baseStart_7279433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279473 : List Nat := [1, 2, 2, 2, 1, 4, 2, 4, 5]
def baseStart_7279473 : Nat := 118140960795 + 7279473 * 2 ^ 59
def prefixEnd_7279473 : Nat := 4983230072969 + 3 ^ 40 * 7279473 * 2
def baseEnd_7279473 : Nat := 415318728936300306901091

theorem tailTrace_7279473 : CollatzResearch.WordTrace tailWord_7279473 prefixEnd_7279473 415318728936300306901091 := by
  unfold tailWord_7279473
  simp only [CollatzResearch.WordTrace]
  refine ⟨265504192356720030854515073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177002794904480020569676715 265504192356720030854515073)
  ·
    refine ⟨199128144267540023140886305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265504192356720030854515073 199128144267540023140886305)
    ·
      refine ⟨149346108200655017355664729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199128144267540023140886305 149346108200655017355664729)
      ·
        refine ⟨112009581150491263016748547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149346108200655017355664729 112009581150491263016748547)
        ·
          refine ⟨168014371725736894525122821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112009581150491263016748547 168014371725736894525122821)
          ·
            refine ⟨31502694698575667723460529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168014371725736894525122821 31502694698575667723460529)
            ·
              refine ⟨23627021023931750792595397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31502694698575667723460529 23627021023931750792595397)
              ·
                refine ⟨4430066441987203273611637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23627021023931750792595397 4430066441987203273611637)
                ·
                  refine ⟨415318728936300306901091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4430066441987203273611637 415318728936300306901091)
                  ·
                    rfl

theorem cell23_7279473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 4, 5].length) (baseStart_7279473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279473 prefixEnd_7279473 := by exact prefixLift 7279473
  have htrace : WordTrace (prefixWord ++ tailWord_7279473) baseStart_7279473 baseEnd_7279473 := by
    simpa [prefixWord, tailWord_7279473, baseEnd_7279473] using wordTrace_append hprefix tailTrace_7279473
  have hstable : (prefixWord ++ tailWord_7279473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279473).length < 2 ^ (prefixWord ++ tailWord_7279473).sum := by decide
  have hdescent : baseEnd_7279473 < baseStart_7279473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279523 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 4, 4, 2]
def baseStart_7279523 : Nat := 118140960795 + 7279523 * 2 ^ 59
def prefixEnd_7279523 : Nat := 4983230072969 + 3 ^ 40 * 7279523 * 2
def baseEnd_7279523 : Nat := 3737894234459427566484589

theorem tailTrace_7279523 : CollatzResearch.WordTrace tailWord_7279523 prefixEnd_7279523 3737894234459427566484589 := by
  unfold tailWord_7279523
  simp only [CollatzResearch.WordTrace]
  refine ⟨265506016006538889393835223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177004010671025926262556815 265506016006538889393835223)
  ·
    refine ⟨398259024009808334090752835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265506016006538889393835223 398259024009808334090752835)
    ·
      refine ⟨597388536014712501136129253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398259024009808334090752835 597388536014712501136129253)
      ·
        refine ⟨112010350502758593963024235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 597388536014712501136129253 112010350502758593963024235)
        ·
          refine ⟨168015525754137890944536353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112010350502758593963024235 168015525754137890944536353)
          ·
            refine ⟨126011644315603418208402265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168015525754137890944536353 126011644315603418208402265)
            ·
              refine ⟨94508733236702563656301699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126011644315603418208402265 94508733236702563656301699)
              ·
                refine ⟨141763099855053845484452549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94508733236702563656301699 141763099855053845484452549)
                ·
                  refine ⟨26580581222822596028334853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141763099855053845484452549 26580581222822596028334853)
                  ·
                    refine ⟨4983858979279236755312785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26580581222822596028334853 4983858979279236755312785)
                    ·
                      refine ⟨3737894234459427566484589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4983858979279236755312785 3737894234459427566484589)
                      ·
                        rfl

theorem cell23_7279523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 4, 2].length) (baseStart_7279523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279523 prefixEnd_7279523 := by exact prefixLift 7279523
  have htrace : WordTrace (prefixWord ++ tailWord_7279523) baseStart_7279523 baseEnd_7279523 := by
    simpa [prefixWord, tailWord_7279523, baseEnd_7279523] using wordTrace_append hprefix tailTrace_7279523
  have hstable : (prefixWord ++ tailWord_7279523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279523).length < 2 ^ (prefixWord ++ tailWord_7279523).sum := by decide
  have hdescent : baseEnd_7279523 < baseStart_7279523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279617 : List Nat := [1, 2, 4, 1, 2, 2, 3, 1, 2, 3, 2]
def baseStart_7279617 : Nat := 118140960795 + 7279617 * 2 ^ 59
def prefixEnd_7279617 : Nat := 4983230072969 + 3 ^ 40 * 7279617 * 2
def baseEnd_7279617 : Nat := 3737942501640950198709157

theorem tailTrace_7279617 : CollatzResearch.WordTrace tailWord_7279617 prefixEnd_7279617 3737942501640950198709157 := by
  unfold tailWord_7279617
  simp only [CollatzResearch.WordTrace]
  refine ⟨265509444468198343447757105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177006296312132228965171403 265509444468198343447757105)
  ·
    refine ⟨199132083351148757585817829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265509444468198343447757105 199132083351148757585817829)
    ·
      refine ⟨37337265628340392047340843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199132083351148757585817829 37337265628340392047340843)
      ·
        refine ⟨56005898442510588071011265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37337265628340392047340843 56005898442510588071011265)
        ·
          refine ⟨42004423831882941053258449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56005898442510588071011265 42004423831882941053258449)
          ·
            refine ⟨31503317873912205789943837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42004423831882941053258449 31503317873912205789943837)
            ·
              refine ⟨11813744202717077171228939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31503317873912205789943837 11813744202717077171228939)
              ·
                refine ⟨17720616304075615756843409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11813744202717077171228939 17720616304075615756843409)
                ·
                  refine ⟨13290462228056711817632557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17720616304075615756843409 13290462228056711817632557)
                  ·
                    refine ⟨4983923335521266931612209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13290462228056711817632557 4983923335521266931612209)
                    ·
                      refine ⟨3737942501640950198709157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4983923335521266931612209 3737942501640950198709157)
                      ·
                        rfl

theorem cell23_7279617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_7279617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279617 prefixEnd_7279617 := by exact prefixLift 7279617
  have htrace : WordTrace (prefixWord ++ tailWord_7279617) baseStart_7279617 baseEnd_7279617 := by
    simpa [prefixWord, tailWord_7279617, baseEnd_7279617] using wordTrace_append hprefix tailTrace_7279617
  have hstable : (prefixWord ++ tailWord_7279617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279617).length < 2 ^ (prefixWord ++ tailWord_7279617).sum := by decide
  have hdescent : baseEnd_7279617 < baseStart_7279617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279623 : List Nat := [1, 1, 4, 3, 1, 1, 1, 4, 1, 6]
def baseStart_7279623 : Nat := 118140960795 + 7279623 * 2 ^ 59
def prefixEnd_7279623 : Nat := 4983230072969 + 3 ^ 40 * 7279623 * 2
def baseEnd_7279623 : Nat := 1245981860841625725078043

theorem tailTrace_7279623 : CollatzResearch.WordTrace tailWord_7279623 prefixEnd_7279623 1245981860841625725078043 := by
  unfold tailWord_7279623
  simp only [CollatzResearch.WordTrace]
  refine ⟨265509663306176606472475523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177006442204117737648317015 265509663306176606472475523)
  ·
    refine ⟨398264494959264909708713285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265509663306176606472475523 398264494959264909708713285)
    ·
      refine ⟨74674592804862170570383741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 398264494959264909708713285 74674592804862170570383741)
      ·
        refine ⟨28002972301823313963893903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74674592804862170570383741 28002972301823313963893903)
        ·
          refine ⟨42004458452734970945840855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28002972301823313963893903 42004458452734970945840855)
          ·
            refine ⟨63006687679102456418761283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42004458452734970945840855 63006687679102456418761283)
            ·
              refine ⟨94510031518653684628141925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63006687679102456418761283 94510031518653684628141925)
              ·
                refine ⟨17720630909747565867776611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94510031518653684628141925 17720630909747565867776611)
                ·
                  refine ⟨26580946364621348801664917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17720630909747565867776611 26580946364621348801664917)
                  ·
                    refine ⟨1245981860841625725078043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26580946364621348801664917 1245981860841625725078043)
                    ·
                      rfl

theorem cell23_7279623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_7279623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279623 prefixEnd_7279623 := by exact prefixLift 7279623
  have htrace : WordTrace (prefixWord ++ tailWord_7279623) baseStart_7279623 baseEnd_7279623 := by
    simpa [prefixWord, tailWord_7279623, baseEnd_7279623] using wordTrace_append hprefix tailTrace_7279623
  have hstable : (prefixWord ++ tailWord_7279623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279623).length < 2 ^ (prefixWord ++ tailWord_7279623).sum := by decide
  have hdescent : baseEnd_7279623 < baseStart_7279623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279624 : List Nat := [2, 1, 3, 2, 1, 4, 2, 3, 1, 1, 3]
def baseStart_7279624 : Nat := 118140960795 + 7279624 * 2 ^ 59
def prefixEnd_7279624 : Nat := 4983230072969 + 3 ^ 40 * 7279624 * 2
def baseEnd_7279624 : Nat := 3737946096005531671321625

theorem tailTrace_7279624 : CollatzResearch.WordTrace tailWord_7279624 prefixEnd_7279624 3737946096005531671321625 := by
  unfold tailWord_7279624
  simp only [CollatzResearch.WordTrace]
  refine ⟨132754849889586491821630963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177006466519448655762174617 132754849889586491821630963)
  ·
    refine ⟨199132274834379737732446445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132754849889586491821630963 199132274834379737732446445)
    ·
      refine ⟨74674603062892401649667417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199132274834379737732446445 74674603062892401649667417)
      ·
        refine ⟨56005952297169301237250563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74674603062892401649667417 56005952297169301237250563)
        ·
          refine ⟨84008928445753951855875845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56005952297169301237250563 84008928445753951855875845)
          ·
            refine ⟨15751674083578865972976721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84008928445753951855875845 15751674083578865972976721)
            ·
              refine ⟨11813755562684149479732541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15751674083578865972976721 11813755562684149479732541)
              ·
                refine ⟨4430158336006556054899703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11813755562684149479732541 4430158336006556054899703)
                ·
                  refine ⟨6645237504009834082349555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4430158336006556054899703 6645237504009834082349555)
                  ·
                    refine ⟨9967856256014751123524333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6645237504009834082349555 9967856256014751123524333)
                    ·
                      refine ⟨3737946096005531671321625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9967856256014751123524333 3737946096005531671321625)
                      ·
                        rfl

theorem cell23_7279624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_7279624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279624 prefixEnd_7279624 := by exact prefixLift 7279624
  have htrace : WordTrace (prefixWord ++ tailWord_7279624) baseStart_7279624 baseEnd_7279624 := by
    simpa [prefixWord, tailWord_7279624, baseEnd_7279624] using wordTrace_append hprefix tailTrace_7279624
  have hstable : (prefixWord ++ tailWord_7279624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279624).length < 2 ^ (prefixWord ++ tailWord_7279624).sum := by decide
  have hdescent : baseEnd_7279624 < baseStart_7279624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279627 : List Nat := [1, 1, 1, 1, 6, 4, 2, 1, 1, 5]
def baseStart_7279627 : Nat := 118140960795 + 7279627 * 2 ^ 59
def prefixEnd_7279627 : Nat := 4983230072969 + 3 ^ 40 * 7279627 * 2
def baseEnd_7279627 : Nat := 1245982545482498386528037

theorem tailTrace_7279627 : CollatzResearch.WordTrace tailWord_7279627 prefixEnd_7279627 1245982545482498386528037 := by
  unfold tailWord_7279627
  simp only [CollatzResearch.WordTrace]
  refine ⟨265509809198162115155621135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177006539465441410103747423 265509809198162115155621135)
  ·
    refine ⟨398264713797243172733431703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265509809198162115155621135 398264713797243172733431703)
    ·
      refine ⟨597397070695864759100147555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398264713797243172733431703 597397070695864759100147555)
      ·
        refine ⟨896095606043797138650221333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597397070695864759100147555 896095606043797138650221333)
        ·
          refine ⟨42004481533302990874229125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 896095606043797138650221333 42004481533302990874229125)
          ·
            refine ⟨7875840287494310788917961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42004481533302990874229125 7875840287494310788917961)
            ·
              refine ⟨5906880215620733091688471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7875840287494310788917961 5906880215620733091688471)
              ·
                refine ⟨8860320323431099637532707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5906880215620733091688471 8860320323431099637532707)
                ·
                  refine ⟨13290480485146649456299061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8860320323431099637532707 13290480485146649456299061)
                  ·
                    refine ⟨1245982545482498386528037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13290480485146649456299061 1245982545482498386528037)
                    ·
                      rfl

theorem cell23_7279627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 1, 5].length) (baseStart_7279627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279627 prefixEnd_7279627 := by exact prefixLift 7279627
  have htrace : WordTrace (prefixWord ++ tailWord_7279627) baseStart_7279627 baseEnd_7279627 := by
    simpa [prefixWord, tailWord_7279627, baseEnd_7279627] using wordTrace_append hprefix tailTrace_7279627
  have hstable : (prefixWord ++ tailWord_7279627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279627).length < 2 ^ (prefixWord ++ tailWord_7279627).sum := by decide
  have hdescent : baseEnd_7279627 < baseStart_7279627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279640 : List Nat := [2, 1, 2, 3, 2, 3, 1, 1, 4, 4]
def baseStart_7279640 : Nat := 118140960795 + 7279640 * 2 ^ 59
def prefixEnd_7279640 : Nat := 4983230072969 + 3 ^ 40 * 7279640 * 2
def baseEnd_7279640 : Nat := 1245984770565334536240517

theorem tailTrace_7279640 : CollatzResearch.WordTrace tailWord_7279640 prefixEnd_7279640 1245984770565334536240517 := by
  unfold tailWord_7279640
  simp only [CollatzResearch.WordTrace]
  refine ⟨132755141673557509187922187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177006855564743345583896249 132755141673557509187922187)
  ·
    refine ⟨199132712510336263781883281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132755141673557509187922187 199132712510336263781883281)
    ·
      refine ⟨149349534382752197836412461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199132712510336263781883281 149349534382752197836412461)
      ·
        refine ⟨56006075393532074188654673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149349534382752197836412461 56006075393532074188654673)
        ·
          refine ⟨42004556545149055641491005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56006075393532074188654673 42004556545149055641491005)
          ·
            refine ⟨15751708704430895865559127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42004556545149055641491005 15751708704430895865559127)
            ·
              refine ⟨23627563056646343798338691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15751708704430895865559127 23627563056646343798338691)
              ·
                refine ⟨35441344584969515697508037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23627563056646343798338691 35441344584969515697508037)
                ·
                  refine ⟨6645252109681784193282757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35441344584969515697508037 6645252109681784193282757)
                  ·
                    refine ⟨1245984770565334536240517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6645252109681784193282757 1245984770565334536240517)
                    ·
                      rfl

theorem cell23_7279640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 4, 4].length) (baseStart_7279640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279640 prefixEnd_7279640 := by exact prefixLift 7279640
  have htrace : WordTrace (prefixWord ++ tailWord_7279640) baseStart_7279640 baseEnd_7279640 := by
    simpa [prefixWord, tailWord_7279640, baseEnd_7279640] using wordTrace_append hprefix tailTrace_7279640
  have hstable : (prefixWord ++ tailWord_7279640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279640).length < 2 ^ (prefixWord ++ tailWord_7279640).sum := by decide
  have hdescent : baseEnd_7279640 < baseStart_7279640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279647 : List Nat := [1, 1, 2, 4, 1, 3, 1, 3, 3, 2, 2]
def baseStart_7279647 : Nat := 118140960795 + 7279647 * 2 ^ 59
def prefixEnd_7279647 : Nat := 4983230072969 + 3 ^ 40 * 7279647 * 2
def baseEnd_7279647 : Nat := 3737957906060585081334019

theorem tailTrace_7279647 : CollatzResearch.WordTrace tailWord_7279647 prefixEnd_7279647 3737957906060585081334019 := by
  unfold tailWord_7279647
  simp only [CollatzResearch.WordTrace]
  refine ⟨265510538658089658571349195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177007025772059772380899463 265510538658089658571349195)
  ·
    refine ⟨398265807987134487857023793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265510538658089658571349195 398265807987134487857023793)
    ·
      refine ⟨298699355990350865892767845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398265807987134487857023793 298699355990350865892767845)
      ·
        refine ⟨56006129248190787354893971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 298699355990350865892767845 56006129248190787354893971)
        ·
          refine ⟨84009193872286181032340957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56006129248190787354893971 84009193872286181032340957)
          ·
            refine ⟨31503447702107317887127859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84009193872286181032340957 31503447702107317887127859)
            ·
              refine ⟨47255171553160976830691789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31503447702107317887127859 47255171553160976830691789)
              ·
                refine ⟨17720689332435366311509421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47255171553160976830691789 17720689332435366311509421)
                ·
                  refine ⟨6645258499663262366816033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17720689332435366311509421 6645258499663262366816033)
                  ·
                    refine ⟨4983943874747446775112025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6645258499663262366816033 4983943874747446775112025)
                    ·
                      refine ⟨3737957906060585081334019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4983943874747446775112025 3737957906060585081334019)
                      ·
                        rfl

theorem cell23_7279647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_7279647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279647 prefixEnd_7279647 := by exact prefixLift 7279647
  have htrace : WordTrace (prefixWord ++ tailWord_7279647) baseStart_7279647 baseEnd_7279647 := by
    simpa [prefixWord, tailWord_7279647, baseEnd_7279647] using wordTrace_append hprefix tailTrace_7279647
  have hstable : (prefixWord ++ tailWord_7279647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279647).length < 2 ^ (prefixWord ++ tailWord_7279647).sum := by decide
  have hdescent : baseEnd_7279647 < baseStart_7279647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279650 : List Nat := [3, 3, 1, 1, 1, 4, 1, 2, 1, 1, 5]
def baseStart_7279650 : Nat := 118140960795 + 7279650 * 2 ^ 59
def prefixEnd_7279650 : Nat := 4983230072969 + 3 ^ 40 * 7279650 * 2
def baseEnd_7279650 : Nat := 3737959446502548569596505

theorem tailTrace_7279650 : CollatzResearch.WordTrace tailWord_7279650 prefixEnd_7279650 3737959446502548569596505 := by
  unfold tailWord_7279650
  simp only [CollatzResearch.WordTrace]
  refine ⟨66377662019269697520927101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177007098718052526722472269 66377662019269697520927101)
  ·
    refine ⟨24891623257226136570347663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66377662019269697520927101 24891623257226136570347663)
    ·
      refine ⟨37337434885839204855521495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24891623257226136570347663 37337434885839204855521495)
      ·
        refine ⟨56006152328758807283282243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37337434885839204855521495 56006152328758807283282243)
        ·
          refine ⟨84009228493138210924923365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56006152328758807283282243 84009228493138210924923365)
          ·
            refine ⟨15751730342463414548423131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84009228493138210924923365 15751730342463414548423131)
            ·
              refine ⟨23627595513695121822634697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15751730342463414548423131 23627595513695121822634697)
              ·
                refine ⟨17720696635271341366976023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23627595513695121822634697 17720696635271341366976023)
                ·
                  refine ⟨26581044952907012050464035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17720696635271341366976023 26581044952907012050464035)
                  ·
                    refine ⟨39871567429360518075696053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26581044952907012050464035 39871567429360518075696053)
                    ·
                      refine ⟨3737959446502548569596505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39871567429360518075696053 3737959446502548569596505)
                      ·
                        rfl

theorem cell23_7279650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_7279650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279650 prefixEnd_7279650 := by exact prefixLift 7279650
  have htrace : WordTrace (prefixWord ++ tailWord_7279650) baseStart_7279650 baseEnd_7279650 := by
    simpa [prefixWord, tailWord_7279650, baseEnd_7279650] using wordTrace_append hprefix tailTrace_7279650
  have hstable : (prefixWord ++ tailWord_7279650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279650).length < 2 ^ (prefixWord ++ tailWord_7279650).sum := by decide
  have hdescent : baseEnd_7279650 < baseStart_7279650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279670 : List Nat := [5, 1, 2, 1, 1, 3, 1, 9]
def baseStart_7279670 : Nat := 118140960795 + 7279670 * 2 ^ 59
def prefixEnd_7279670 : Nat := 4983230072969 + 3 ^ 40 * 7279670 * 2
def baseEnd_7279670 : Nat := 138443322819097721901719

theorem tailTrace_7279670 : CollatzResearch.WordTrace tailWord_7279670 prefixEnd_7279670 138443322819097721901719 := by
  unfold tailWord_7279670
  simp only [CollatzResearch.WordTrace]
  refine ⟨16594461096062895843714779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177007585024670888999624309 16594461096062895843714779)
  ·
    refine ⟨24891691644094343765572169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16594461096062895843714779 24891691644094343765572169)
    ·
      refine ⟨18668768733070757824179127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24891691644094343765572169 18668768733070757824179127)
      ·
        refine ⟨28003153099606136736268691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18668768733070757824179127 28003153099606136736268691)
        ·
          refine ⟨42004729649409205104403037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28003153099606136736268691 42004729649409205104403037)
          ·
            refine ⟨15751773618528451914151139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42004729649409205104403037 15751773618528451914151139)
            ·
              refine ⟨23627660427792677871226709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15751773618528451914151139 23627660427792677871226709)
              ·
                refine ⟨138443322819097721901719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23627660427792677871226709 138443322819097721901719)
                ·
                  rfl

theorem cell23_7279670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 9].length) (baseStart_7279670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279670 prefixEnd_7279670 := by exact prefixLift 7279670
  have htrace : WordTrace (prefixWord ++ tailWord_7279670) baseStart_7279670 baseEnd_7279670 := by
    simpa [prefixWord, tailWord_7279670, baseEnd_7279670] using wordTrace_append hprefix tailTrace_7279670
  have hstable : (prefixWord ++ tailWord_7279670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279670).length < 2 ^ (prefixWord ++ tailWord_7279670).sum := by decide
  have hdescent : baseEnd_7279670 < baseStart_7279670 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279680 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 6, 1, 3]
def baseStart_7279680 : Nat := 118140960795 + 7279680 * 2 ^ 59
def prefixEnd_7279680 : Nat := 4983230072969 + 3 ^ 40 * 7279680 * 2
def baseEnd_7279680 : Nat := 3737974850922183452221367

theorem tailTrace_7279680 : CollatzResearch.WordTrace tailWord_7279680 prefixEnd_7279680 3737974850922183452221367 := by
  unfold tailWord_7279680
  simp only [CollatzResearch.WordTrace]
  refine ⟨132755871133485052603650247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177007828177980070138200329 132755871133485052603650247)
  ·
    refine ⟨199133806700227578905475371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132755871133485052603650247 199133806700227578905475371)
    ·
      refine ⟨298700710050341368358213057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199133806700227578905475371 298700710050341368358213057)
      ·
        refine ⟨224025532537756026268659793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298700710050341368358213057 224025532537756026268659793)
        ·
          refine ⟨168019149403317019701494845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224025532537756026268659793 168019149403317019701494845)
          ·
            refine ⟨63007181026243882388060567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168019149403317019701494845 63007181026243882388060567)
            ·
              refine ⟨94510771539365823582090851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63007181026243882388060567 94510771539365823582090851)
              ·
                refine ⟨141766157309048735373136277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94510771539365823582090851 141766157309048735373136277)
                ·
                  refine ⟨6645288623861659470615763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 141766157309048735373136277 6645288623861659470615763)
                  ·
                    refine ⟨9967932935792489205923645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6645288623861659470615763 9967932935792489205923645)
                    ·
                      refine ⟨3737974850922183452221367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9967932935792489205923645 3737974850922183452221367)
                      ·
                        rfl

theorem cell23_7279680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 6, 1, 3].length) (baseStart_7279680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279680 prefixEnd_7279680 := by exact prefixLift 7279680
  have htrace : WordTrace (prefixWord ++ tailWord_7279680) baseStart_7279680 baseEnd_7279680 := by
    simpa [prefixWord, tailWord_7279680, baseEnd_7279680] using wordTrace_append hprefix tailTrace_7279680
  have hstable : (prefixWord ++ tailWord_7279680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279680).length < 2 ^ (prefixWord ++ tailWord_7279680).sum := by decide
  have hdescent : baseEnd_7279680 < baseStart_7279680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279698 : List Nat := [3, 2, 2, 1, 3, 2, 3, 2, 1, 2, 2]
def baseStart_7279698 : Nat := 118140960795 + 7279698 * 2 ^ 59
def prefixEnd_7279698 : Nat := 4983230072969 + 3 ^ 40 * 7279698 * 2
def baseEnd_7279698 : Nat := 3737984093573964381796285

theorem tailTrace_7279698 : CollatzResearch.WordTrace tailWord_7279698 prefixEnd_7279698 3737984093573964381796285 := by
  unfold tailWord_7279698
  simp only [CollatzResearch.WordTrace]
  refine ⟨66378099695226223570363937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177008265853936596187637165 66378099695226223570363937)
  ·
    refine ⟨49783574771419667677772953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66378099695226223570363937 49783574771419667677772953)
    ·
      refine ⟨37337681078564750758329715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49783574771419667677772953 37337681078564750758329715)
      ·
        refine ⟨56006521617847126137494573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37337681078564750758329715 56006521617847126137494573)
        ·
          refine ⟨21002445606692672301560465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56006521617847126137494573 21002445606692672301560465)
          ·
            refine ⟨15751834205019504226170349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21002445606692672301560465 15751834205019504226170349)
            ·
              refine ⟨5906937826882314084813881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15751834205019504226170349 5906937826882314084813881)
              ·
                refine ⟨4430203370161735563610411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5906937826882314084813881 4430203370161735563610411)
                ·
                  refine ⟨6645305055242603345415617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4430203370161735563610411 6645305055242603345415617)
                  ·
                    refine ⟨4983978791431952509061713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6645305055242603345415617 4983978791431952509061713)
                    ·
                      refine ⟨3737984093573964381796285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4983978791431952509061713 3737984093573964381796285)
                      ·
                        rfl

theorem cell23_7279698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_7279698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279698 prefixEnd_7279698 := by exact prefixLift 7279698
  have htrace : WordTrace (prefixWord ++ tailWord_7279698) baseStart_7279698 baseEnd_7279698 := by
    simpa [prefixWord, tailWord_7279698, baseEnd_7279698] using wordTrace_append hprefix tailTrace_7279698
  have hstable : (prefixWord ++ tailWord_7279698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279698).length < 2 ^ (prefixWord ++ tailWord_7279698).sum := by decide
  have hdescent : baseEnd_7279698 < baseStart_7279698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279703 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 4]
def baseStart_7279703 : Nat := 118140960795 + 7279703 * 2 ^ 59
def prefixEnd_7279703 : Nat := 4983230072969 + 3 ^ 40 * 7279703 * 2
def baseEnd_7279703 : Nat := 3737986660977236862233761

theorem tailTrace_7279703 : CollatzResearch.WordTrace tailWord_7279703 prefixEnd_7279703 3737986660977236862233761 := by
  unfold tailWord_7279703
  simp only [CollatzResearch.WordTrace]
  refine ⟨265512581145886780135387763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177008387430591186756925175 265512581145886780135387763)
  ·
    refine ⟨398268871718830170203081645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265512581145886780135387763 398268871718830170203081645)
    ·
      refine ⟨149350826894561313826155617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 398268871718830170203081645 149350826894561313826155617)
      ·
        refine ⟨112013120170920985369616713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149350826894561313826155617 112013120170920985369616713)
        ·
          refine ⟨84009840128190739027212535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112013120170920985369616713 84009840128190739027212535)
          ·
            refine ⟨126014760192286108540818803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84009840128190739027212535 126014760192286108540818803)
            ·
              refine ⟨189022140288429162811228205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126014760192286108540818803 189022140288429162811228205)
              ·
                refine ⟨70883302608160936054210577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189022140288429162811228205 70883302608160936054210577)
                ·
                  refine ⟨53162476956120702040657933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70883302608160936054210577 53162476956120702040657933)
                  ·
                    refine ⟨19935928858545263265246725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53162476956120702040657933 19935928858545263265246725)
                    ·
                      refine ⟨3737986660977236862233761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19935928858545263265246725 3737986660977236862233761)
                      ·
                        rfl

theorem cell23_7279703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_7279703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279703 prefixEnd_7279703 := by exact prefixLift 7279703
  have htrace : WordTrace (prefixWord ++ tailWord_7279703) baseStart_7279703 baseEnd_7279703 := by
    simpa [prefixWord, tailWord_7279703, baseEnd_7279703] using wordTrace_append hprefix tailTrace_7279703
  have hstable : (prefixWord ++ tailWord_7279703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279703).length < 2 ^ (prefixWord ++ tailWord_7279703).sum := by decide
  have hdescent : baseEnd_7279703 < baseStart_7279703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279713 : List Nat := [1, 2, 3, 1, 1, 2, 2, 3, 2, 6]
def baseStart_7279713 : Nat := 118140960795 + 7279713 * 2 ^ 59
def prefixEnd_7279713 : Nat := 4983230072969 + 3 ^ 40 * 7279713 * 2
def baseEnd_7279713 : Nat := 1245997265261260607702905

theorem tailTrace_7279713 : CollatzResearch.WordTrace tailWord_7279713 prefixEnd_7279713 1245997265261260607702905 := by
  unfold tailWord_7279713
  simp only [CollatzResearch.WordTrace]
  refine ⟨265512945875850551843251793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177008630583900367895501195 265512945875850551843251793)
  ·
    refine ⟨199134709406887913882438845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265512945875850551843251793 199134709406887913882438845)
    ·
      refine ⟨74675516027582967705914567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199134709406887913882438845 74675516027582967705914567)
      ·
        refine ⟨112013274041374451558871851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74675516027582967705914567 112013274041374451558871851)
        ·
          refine ⟨168019911062061677338307777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112013274041374451558871851 168019911062061677338307777)
          ·
            refine ⟨126014933296546258003730833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168019911062061677338307777 126014933296546258003730833)
            ·
              refine ⟨94511199972409693502798125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126014933296546258003730833 94511199972409693502798125)
              ·
                refine ⟨35441699989653635063549297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94511199972409693502798125 35441699989653635063549297)
                ·
                  refine ⟨26581274992240226297661973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35441699989653635063549297 26581274992240226297661973)
                  ·
                    refine ⟨1245997265261260607702905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26581274992240226297661973 1245997265261260607702905)
                    ·
                      rfl

theorem cell23_7279713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_7279713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279713 prefixEnd_7279713 := by exact prefixLift 7279713
  have htrace : WordTrace (prefixWord ++ tailWord_7279713) baseStart_7279713 baseEnd_7279713 := by
    simpa [prefixWord, tailWord_7279713, baseEnd_7279713] using wordTrace_append hprefix tailTrace_7279713
  have hstable : (prefixWord ++ tailWord_7279713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279713).length < 2 ^ (prefixWord ++ tailWord_7279713).sum := by decide
  have hdescent : baseEnd_7279713 < baseStart_7279713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279850 : List Nat := [3, 1, 3, 1, 1, 3, 1, 2, 8]
def baseStart_7279850 : Nat := 118140960795 + 7279850 * 2 ^ 59
def prefixEnd_7279850 : Nat := 4983230072969 + 3 ^ 40 * 7279850 * 2
def baseEnd_7279850 : Nat := 415340238070383087455065

theorem tailTrace_7279850 : CollatzResearch.WordTrace tailWord_7279850 prefixEnd_7279850 415340238070383087455065 := by
  unfold tailWord_7279850
  simp only [CollatzResearch.WordTrace]
  refine ⟨66379485669088556060247251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177011961784236149493992669 66379485669088556060247251)
  ·
    refine ⟨99569228503632834090370877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66379485669088556060247251 99569228503632834090370877)
    ·
      refine ⟨37338460688862312783889079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99569228503632834090370877 37338460688862312783889079)
      ·
        refine ⟨56007691033293469175833619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37338460688862312783889079 56007691033293469175833619)
        ·
          refine ⟨84011536549940203763750429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56007691033293469175833619 84011536549940203763750429)
          ·
            refine ⟨31504326206227576411406411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84011536549940203763750429 31504326206227576411406411)
            ·
              refine ⟨47256489309341364617109617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31504326206227576411406411 47256489309341364617109617)
              ·
                refine ⟨35442366982006023462832213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47256489309341364617109617 35442366982006023462832213)
                ·
                  refine ⟨415340238070383087455065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35442366982006023462832213 415340238070383087455065)
                  ·
                    rfl

theorem cell23_7279850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 8].length) (baseStart_7279850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279850 prefixEnd_7279850 := by exact prefixLift 7279850
  have htrace : WordTrace (prefixWord ++ tailWord_7279850) baseStart_7279850 baseEnd_7279850 := by
    simpa [prefixWord, tailWord_7279850, baseEnd_7279850] using wordTrace_append hprefix tailTrace_7279850
  have hstable : (prefixWord ++ tailWord_7279850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279850).length < 2 ^ (prefixWord ++ tailWord_7279850).sum := by decide
  have hdescent : baseEnd_7279850 < baseStart_7279850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279871 : List Nat := [1, 1, 2, 2, 1, 6, 3, 2, 1, 4]
def baseStart_7279871 : Nat := 118140960795 + 7279871 * 2 ^ 59
def prefixEnd_7279871 : Nat := 4983230072969 + 3 ^ 40 * 7279871 * 2
def baseEnd_7279871 : Nat := 1246024308575730734977663

theorem tailTrace_7279871 : CollatzResearch.WordTrace tailWord_7279871 prefixEnd_7279871 1246024308575730734977663 := by
  unfold tailWord_7279871
  simp only [CollatzResearch.WordTrace]
  refine ⟨265518708609278144827503467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177012472406185429885002311 265518708609278144827503467)
  ·
    refine ⟨398278062913917217241255201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265518708609278144827503467 398278062913917217241255201)
    ·
      refine ⟨298708547185437912930941401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398278062913917217241255201 298708547185437912930941401)
      ·
        refine ⟨224031410389078434698206051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298708547185437912930941401 224031410389078434698206051)
        ·
          refine ⟨336047115583617652047309077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224031410389078434698206051 336047115583617652047309077)
          ·
            refine ⟨15752208542982077439717613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 336047115583617652047309077 15752208542982077439717613)
            ·
              refine ⟨5907078203618279039894105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15752208542982077439717613 5907078203618279039894105)
              ·
                refine ⟨4430308652713709279920579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5907078203618279039894105 4430308652713709279920579)
                ·
                  refine ⟨6645462979070563919880869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4430308652713709279920579 6645462979070563919880869)
                  ·
                    refine ⟨1246024308575730734977663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6645462979070563919880869 1246024308575730734977663)
                    ·
                      rfl

theorem cell23_7279871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 2, 1, 4].length) (baseStart_7279871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279871 prefixEnd_7279871 := by exact prefixLift 7279871
  have htrace : WordTrace (prefixWord ++ tailWord_7279871) baseStart_7279871 baseEnd_7279871 := by
    simpa [prefixWord, tailWord_7279871, baseEnd_7279871] using wordTrace_append hprefix tailTrace_7279871
  have hstable : (prefixWord ++ tailWord_7279871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279871).length < 2 ^ (prefixWord ++ tailWord_7279871).sum := by decide
  have hdescent : baseEnd_7279871 < baseStart_7279871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279884 : List Nat := [2, 2, 1, 2, 2, 5, 2, 1, 6]
def baseStart_7279884 : Nat := 118140960795 + 7279884 * 2 ^ 59
def prefixEnd_7279884 : Nat := 4983230072969 + 3 ^ 40 * 7279884 * 2
def baseEnd_7279884 : Nat := 415342177886188961563381

theorem tailTrace_7279884 : CollatzResearch.WordTrace tailWord_7279884 prefixEnd_7279884 415342177886188961563381 := by
  unfold tailWord_7279884
  simp only [CollatzResearch.WordTrace]
  refine ⟨132759591379115524023863353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177012788505487365365151137 132759591379115524023863353)
  ·
    refine ⟨99569693534336643017897515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132759591379115524023863353 99569693534336643017897515)
    ·
      refine ⟨149354540301504964526846273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99569693534336643017897515 149354540301504964526846273)
      ·
        refine ⟨112015905226128723395134705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149354540301504964526846273 112015905226128723395134705)
        ·
          refine ⟨84011928919596542546351029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112015905226128723395134705 84011928919596542546351029)
          ·
            refine ⟨7876118336212175863720409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84011928919596542546351029 7876118336212175863720409)
            ·
              refine ⟨5907088752159131897790307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7876118336212175863720409 5907088752159131897790307)
              ·
                refine ⟨8860633128238697846685461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5907088752159131897790307 8860633128238697846685461)
                ·
                  refine ⟨415342177886188961563381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8860633128238697846685461 415342177886188961563381)
                  ·
                    rfl

theorem cell23_7279884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 6].length) (baseStart_7279884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279884 prefixEnd_7279884 := by exact prefixLift 7279884
  have htrace : WordTrace (prefixWord ++ tailWord_7279884) baseStart_7279884 baseEnd_7279884 := by
    simpa [prefixWord, tailWord_7279884, baseEnd_7279884] using wordTrace_append hprefix tailTrace_7279884
  have hstable : (prefixWord ++ tailWord_7279884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279884).length < 2 ^ (prefixWord ++ tailWord_7279884).sum := by decide
  have hdescent : baseEnd_7279884 < baseStart_7279884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279954 : List Nat := [3, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3]
def baseStart_7279954 : Nat := 118140960795 + 7279954 * 2 ^ 59
def prefixEnd_7279954 : Nat := 4983230072969 + 3 ^ 40 * 7279954 * 2
def baseEnd_7279954 : Nat := 3738115544621515380195107

theorem tailTrace_7279954 : CollatzResearch.WordTrace tailWord_7279954 prefixEnd_7279954 3738115544621515380195107 := by
  unfold tailWord_7279954
  simp only [CollatzResearch.WordTrace]
  refine ⟨66380433966994362500693729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177014490578651633335183277 66380433966994362500693729)
  ·
    refine ⟨49785325475245771875520297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66380433966994362500693729 49785325475245771875520297)
    ·
      refine ⟨37338994106434328906640223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49785325475245771875520297 37338994106434328906640223)
      ·
        refine ⟨56008491159651493359960335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37338994106434328906640223 56008491159651493359960335)
        ·
          refine ⟨84012736739477240039940503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56008491159651493359960335 84012736739477240039940503)
          ·
            refine ⟨126019105109215860059910755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84012736739477240039940503 126019105109215860059910755)
            ·
              refine ⟨189028657663823790089866133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126019105109215860059910755 189028657663823790089866133)
              ·
                refine ⟨8860718327991740160462475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 189028657663823790089866133 8860718327991740160462475)
                ·
                  refine ⟨13291077491987610240693713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8860718327991740160462475 13291077491987610240693713)
                  ·
                    refine ⟨9968308118990707680520285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13291077491987610240693713 9968308118990707680520285)
                    ·
                      refine ⟨3738115544621515380195107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9968308118990707680520285 3738115544621515380195107)
                      ·
                        rfl

theorem cell23_7279954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_7279954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279954 prefixEnd_7279954 := by exact prefixLift 7279954
  have htrace : WordTrace (prefixWord ++ tailWord_7279954) baseStart_7279954 baseEnd_7279954 := by
    simpa [prefixWord, tailWord_7279954, baseEnd_7279954] using wordTrace_append hprefix tailTrace_7279954
  have hstable : (prefixWord ++ tailWord_7279954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279954).length < 2 ^ (prefixWord ++ tailWord_7279954).sum := by decide
  have hdescent : baseEnd_7279954 < baseStart_7279954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279968 : List Nat := [2, 1, 1, 3, 4, 1, 1, 5, 1, 2, 2]
def baseStart_7279968 : Nat := 118140960795 + 7279968 * 2 ^ 59
def prefixEnd_7279968 : Nat := 4983230072969 + 3 ^ 40 * 7279968 * 2
def baseEnd_7279968 : Nat := 3738122733350678325420043

theorem tailTrace_7279968 : CollatzResearch.WordTrace tailWord_7279968 prefixEnd_7279968 3738122733350678325420043 := by
  unfold tailWord_7279968
  simp only [CollatzResearch.WordTrace]
  refine ⟨132761123244963365196892279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177014830993284486929189705 132761123244963365196892279)
  ·
    refine ⟨199141684867445047795338419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132761123244963365196892279 199141684867445047795338419)
    ·
      refine ⟨298712527301167571693007629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199141684867445047795338419 298712527301167571693007629)
      ·
        refine ⟨112017197737937839384877861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298712527301167571693007629 112017197737937839384877861)
        ·
          refine ⟨21003224575863344884664599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112017197737937839384877861 21003224575863344884664599)
          ·
            refine ⟨31504836863795017326996899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21003224575863344884664599 31504836863795017326996899)
            ·
              refine ⟨47257255295692525990495349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31504836863795017326996899 47257255295692525990495349)
              ·
                refine ⟨4430367683971174311608939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47257255295692525990495349 4430367683971174311608939)
                ·
                  refine ⟨6645551525956761467413409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4430367683971174311608939 6645551525956761467413409)
                  ·
                    refine ⟨4984163644467571100560057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6645551525956761467413409 4984163644467571100560057)
                    ·
                      refine ⟨3738122733350678325420043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4984163644467571100560057 3738122733350678325420043)
                      ·
                        rfl

theorem cell23_7279968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 5, 1, 2, 2].length) (baseStart_7279968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279968 prefixEnd_7279968 := by exact prefixLift 7279968
  have htrace : WordTrace (prefixWord ++ tailWord_7279968) baseStart_7279968 baseEnd_7279968 := by
    simpa [prefixWord, tailWord_7279968, baseEnd_7279968] using wordTrace_append hprefix tailTrace_7279968
  have hstable : (prefixWord ++ tailWord_7279968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279968).length < 2 ^ (prefixWord ++ tailWord_7279968).sum := by decide
  have hdescent : baseEnd_7279968 < baseStart_7279968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279971 : List Nat := [1, 1, 1, 5, 2, 2, 4, 1, 1, 2, 3]
def baseStart_7279971 : Nat := 118140960795 + 7279971 * 2 ^ 59
def prefixEnd_7279971 : Nat := 4983230072969 + 3 ^ 40 * 7279971 * 2
def baseEnd_7279971 : Nat := 3738124273792641813682529

theorem tailTrace_7279971 : CollatzResearch.WordTrace tailWord_7279971 prefixEnd_7279971 3738124273792641813682529 := by
  unfold tailWord_7279971
  simp only [CollatzResearch.WordTrace]
  refine ⟨265522355908915861906143767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177014903939277241270762511 265522355908915861906143767)
  ·
    refine ⟨398283533863373792859215651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265522355908915861906143767 398283533863373792859215651)
    ·
      refine ⟨597425300795060689288823477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398283533863373792859215651 597425300795060689288823477)
      ·
        refine ⟨56008621949536939620827201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 597425300795060689288823477 56008621949536939620827201)
        ·
          refine ⟨42006466462152704715620401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56008621949536939620827201 42006466462152704715620401)
          ·
            refine ⟨31504849846614528536715301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42006466462152704715620401 31504849846614528536715301)
            ·
              refine ⟨5907159346240224100634119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31504849846614528536715301 5907159346240224100634119)
              ·
                refine ⟨8860739019360336150951179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5907159346240224100634119 8860739019360336150951179)
                ·
                  refine ⟨13291108529040504226426769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8860739019360336150951179 13291108529040504226426769)
                  ·
                    refine ⟨9968331396780378169820077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13291108529040504226426769 9968331396780378169820077)
                    ·
                      refine ⟨3738124273792641813682529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9968331396780378169820077 3738124273792641813682529)
                      ·
                        rfl

theorem cell23_7279971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_7279971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279971 prefixEnd_7279971 := by exact prefixLift 7279971
  have htrace : WordTrace (prefixWord ++ tailWord_7279971) baseStart_7279971 baseEnd_7279971 := by
    simpa [prefixWord, tailWord_7279971, baseEnd_7279971] using wordTrace_append hprefix tailTrace_7279971
  have hstable : (prefixWord ++ tailWord_7279971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279971).length < 2 ^ (prefixWord ++ tailWord_7279971).sum := by decide
  have hdescent : baseEnd_7279971 < baseStart_7279971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279978 : List Nat := [3, 1, 3, 3, 2, 2, 1, 2, 2, 4]
def baseStart_7279978 : Nat := 118140960795 + 7279978 * 2 ^ 59
def prefixEnd_7279978 : Nat := 4983230072969 + 3 ^ 40 * 7279978 * 2
def baseEnd_7279978 : Nat := 1246042622719074428764999

theorem tailTrace_7279978 : CollatzResearch.WordTrace tailWord_7279978 prefixEnd_7279978 1246042622719074428764999 := by
  unfold tailWord_7279978
  simp only [CollatzResearch.WordTrace]
  refine ⟨66380652804972625525412147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177015074146593668067765725 66380652804972625525412147)
  ·
    refine ⟨99570979207458938288118221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66380652804972625525412147 99570979207458938288118221)
    ·
      refine ⟨37339117202797101858044333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99570979207458938288118221 37339117202797101858044333)
      ·
        refine ⟨14002168951048913196766625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37339117202797101858044333 14002168951048913196766625)
        ·
          refine ⟨10501626713286684897574969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14002168951048913196766625 10501626713286684897574969)
          ·
            refine ⟨7876220034965013673181227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10501626713286684897574969 7876220034965013673181227)
            ·
              refine ⟨11814330052447520509771841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7876220034965013673181227 11814330052447520509771841)
              ·
                refine ⟨8860747539335640382328881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11814330052447520509771841 8860747539335640382328881)
                ·
                  refine ⟨6645560654501730286746661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8860747539335640382328881 6645560654501730286746661)
                  ·
                    refine ⟨1246042622719074428764999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6645560654501730286746661 1246042622719074428764999)
                    ·
                      rfl

theorem cell23_7279978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_7279978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279978 prefixEnd_7279978 := by exact prefixLift 7279978
  have htrace : WordTrace (prefixWord ++ tailWord_7279978) baseStart_7279978 baseEnd_7279978 := by
    simpa [prefixWord, tailWord_7279978, baseEnd_7279978] using wordTrace_append hprefix tailTrace_7279978
  have hstable : (prefixWord ++ tailWord_7279978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279978).length < 2 ^ (prefixWord ++ tailWord_7279978).sum := by decide
  have hdescent : baseEnd_7279978 < baseStart_7279978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7279984 : List Nat := [2, 1, 1, 1, 4, 2, 3, 1, 4, 1, 3]
def baseStart_7279984 : Nat := 118140960795 + 7279984 * 2 ^ 59
def prefixEnd_7279984 : Nat := 4983230072969 + 3 ^ 40 * 7279984 * 2
def baseEnd_7279984 : Nat := 3738130949041150262819969

theorem tailTrace_7279984 : CollatzResearch.WordTrace tailWord_7279984 prefixEnd_7279984 3738130949041150262819969 := by
  unfold tailWord_7279984
  simp only [CollatzResearch.WordTrace]
  refine ⟨132761415028934382563183503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177015220038579176750911337 132761415028934382563183503)
  ·
    refine ⟨199142122543401573844775255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132761415028934382563183503 199142122543401573844775255)
    ·
      refine ⟨298713183815102360767162883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199142122543401573844775255 298713183815102360767162883)
      ·
        refine ⟨448069775722653541150744325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298713183815102360767162883 448069775722653541150744325)
        ·
          refine ⟨84013082947997538965764561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 448069775722653541150744325 84013082947997538965764561)
          ·
            refine ⟨63009812210998154224323421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84013082947997538965764561 63009812210998154224323421)
            ·
              refine ⟨23628679579124307834121283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63009812210998154224323421 23628679579124307834121283)
              ·
                refine ⟨35443019368686461751181925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23628679579124307834121283 35443019368686461751181925)
                ·
                  refine ⟨6645566131628711578346611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35443019368686461751181925 6645566131628711578346611)
                  ·
                    refine ⟨9968349197443067367519917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6645566131628711578346611 9968349197443067367519917)
                    ·
                      refine ⟨3738130949041150262819969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9968349197443067367519917 3738130949041150262819969)
                      ·
                        rfl

theorem cell23_7279984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 4, 1, 3].length) (baseStart_7279984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7279984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7279984 prefixEnd_7279984 := by exact prefixLift 7279984
  have htrace : WordTrace (prefixWord ++ tailWord_7279984) baseStart_7279984 baseEnd_7279984 := by
    simpa [prefixWord, tailWord_7279984, baseEnd_7279984] using wordTrace_append hprefix tailTrace_7279984
  have hstable : (prefixWord ++ tailWord_7279984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7279984).length < 2 ^ (prefixWord ++ tailWord_7279984).sum := by decide
  have hdescent : baseEnd_7279984 < baseStart_7279984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7279984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280011 : List Nat := [1, 1, 1, 1, 4, 3, 4, 2, 1, 3, 2]
def baseStart_7280011 : Nat := 118140960795 + 7280011 * 2 ^ 59
def prefixEnd_7280011 : Nat := 4983230072969 + 3 ^ 40 * 7280011 * 2
def baseEnd_7280011 : Nat := 3738144813018821657182345

theorem tailTrace_7280011 : CollatzResearch.WordTrace tailWord_7280011 prefixEnd_7280011 3738144813018821657182345 := by
  unfold tailWord_7280011
  simp only [CollatzResearch.WordTrace]
  refine ⟨265523814828770948737599887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177015876552513965825066591 265523814828770948737599887)
  ·
    refine ⟨398285722243156423106399831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265523814828770948737599887 398285722243156423106399831)
    ·
      refine ⟨597428583364734634659599747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398285722243156423106399831 597428583364734634659599747)
      ·
        refine ⟨896142875047101951989399621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597428583364734634659599747 896142875047101951989399621)
        ·
          refine ⟨168026789071331615998012429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 896142875047101951989399621 168026789071331615998012429)
          ·
            refine ⟨63010045901749355999254661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168026789071331615998012429 63010045901749355999254661)
            ·
              refine ⟨11814383606578004249860249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63010045901749355999254661 11814383606578004249860249)
              ·
                refine ⟨8860787704933503187395187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11814383606578004249860249 8860787704933503187395187)
                ·
                  refine ⟨13291181557400254781092781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8860787704933503187395187 13291181557400254781092781)
                  ·
                    refine ⟨4984193084025095542909793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13291181557400254781092781 4984193084025095542909793)
                    ·
                      refine ⟨3738144813018821657182345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4984193084025095542909793 3738144813018821657182345)
                      ·
                        rfl

theorem cell23_7280011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 3, 2].length) (baseStart_7280011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280011 prefixEnd_7280011 := by exact prefixLift 7280011
  have htrace : WordTrace (prefixWord ++ tailWord_7280011) baseStart_7280011 baseEnd_7280011 := by
    simpa [prefixWord, tailWord_7280011, baseEnd_7280011] using wordTrace_append hprefix tailTrace_7280011
  have hstable : (prefixWord ++ tailWord_7280011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280011).length < 2 ^ (prefixWord ++ tailWord_7280011).sum := by decide
  have hdescent : baseEnd_7280011 < baseStart_7280011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280037 : List Nat := [1, 3, 1, 2, 1, 1, 2, 4, 2, 2, 4]
def baseStart_7280037 : Nat := 118140960795 + 7280037 * 2 ^ 59
def prefixEnd_7280037 : Nat := 4983230072969 + 3 ^ 40 * 7280037 * 2
def baseEnd_7280037 : Nat := 3738158163515838555457225

theorem tailTrace_7280037 : CollatzResearch.WordTrace tailWord_7280037 prefixEnd_7280037 3738158163515838555457225 := by
  unfold tailWord_7280037
  simp only [CollatzResearch.WordTrace]
  refine ⟨265524763126676755178046365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177016508751117836785364243 265524763126676755178046365)
  ·
    refine ⟨99571786172503783191767387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265524763126676755178046365 99571786172503783191767387)
    ·
      refine ⟨149357679258755674787651081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99571786172503783191767387 149357679258755674787651081)
      ·
        refine ⟨112018259444066756090738311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149357679258755674787651081 112018259444066756090738311)
        ·
          refine ⟨168027389166100134136107467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112018259444066756090738311 168027389166100134136107467)
          ·
            refine ⟨252041083749150201204161201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168027389166100134136107467 252041083749150201204161201)
            ·
              refine ⟨189030812811862650903120901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252041083749150201204161201 189030812811862650903120901)
              ·
                refine ⟨35443277402224247044335169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189030812811862650903120901 35443277402224247044335169)
                ·
                  refine ⟨26582458051668185283251377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35443277402224247044335169 26582458051668185283251377)
                  ·
                    refine ⟨19936843538751138962438533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26582458051668185283251377 19936843538751138962438533)
                    ·
                      refine ⟨3738158163515838555457225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19936843538751138962438533 3738158163515838555457225)
                      ·
                        rfl

theorem cell23_7280037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_7280037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280037 prefixEnd_7280037 := by exact prefixLift 7280037
  have htrace : WordTrace (prefixWord ++ tailWord_7280037) baseStart_7280037 baseEnd_7280037 := by
    simpa [prefixWord, tailWord_7280037, baseEnd_7280037] using wordTrace_append hprefix tailTrace_7280037
  have hstable : (prefixWord ++ tailWord_7280037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280037).length < 2 ^ (prefixWord ++ tailWord_7280037).sum := by decide
  have hdescent : baseEnd_7280037 < baseStart_7280037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280101 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 2, 5, 2]
def baseStart_7280101 : Nat := 118140960795 + 7280101 * 2 ^ 59
def prefixEnd_7280101 : Nat := 4983230072969 + 3 ^ 40 * 7280101 * 2
def baseEnd_7280101 : Nat := 3738191026277726305056931

theorem tailTrace_7280101 : CollatzResearch.WordTrace tailWord_7280101 prefixEnd_7280101 3738191026277726305056931 := by
  unfold tailWord_7280101
  simp only [CollatzResearch.WordTrace]
  refine ⟨265527097398444894108376157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177018064932296596072250771 265527097398444894108376157)
  ·
    refine ⟨99572661524416835290641059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265527097398444894108376157 99572661524416835290641059)
    ·
      refine ⟨149358992286625252935961589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99572661524416835290641059 149358992286625252935961589)
      ·
        refine ⟨14002405526871117462746399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149358992286625252935961589 14002405526871117462746399)
        ·
          refine ⟨21003608290306676194119599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14002405526871117462746399 21003608290306676194119599)
          ·
            refine ⟨31505412435460014291179399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21003608290306676194119599 31505412435460014291179399)
            ·
              refine ⟨47258118653190021436769099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31505412435460014291179399 47258118653190021436769099)
              ·
                refine ⟨70887177979785032155153649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47258118653190021436769099 70887177979785032155153649)
                ·
                  refine ⟨53165383484838774116365237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70887177979785032155153649 53165383484838774116365237)
                  ·
                    refine ⟨4984254701703635073409241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53165383484838774116365237 4984254701703635073409241)
                    ·
                      refine ⟨3738191026277726305056931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4984254701703635073409241 3738191026277726305056931)
                      ·
                        rfl

theorem cell23_7280101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_7280101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280101 prefixEnd_7280101 := by exact prefixLift 7280101
  have htrace : WordTrace (prefixWord ++ tailWord_7280101) baseStart_7280101 baseEnd_7280101 := by
    simpa [prefixWord, tailWord_7280101, baseEnd_7280101] using wordTrace_append hprefix tailTrace_7280101
  have hstable : (prefixWord ++ tailWord_7280101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280101).length < 2 ^ (prefixWord ++ tailWord_7280101).sum := by decide
  have hdescent : baseEnd_7280101 < baseStart_7280101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280124 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 5, 4]
def baseStart_7280124 : Nat := 118140960795 + 7280124 * 2 ^ 59
def prefixEnd_7280124 : Nat := 4983230072969 + 3 ^ 40 * 7280124 * 2
def baseEnd_7280124 : Nat := 1246067612110926571689775

theorem tailTrace_7280124 : CollatzResearch.WordTrace tailWord_7280124 prefixEnd_7280124 1246067612110926571689775 := by
  unfold tailWord_7280124
  simp only [CollatzResearch.WordTrace]
  refine ⟨132763968138680784518231713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177018624184907712690975617 132763968138680784518231713)
  ·
    refine ⟨99572976104010588388673785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132763968138680784518231713 99572976104010588388673785)
    ·
      refine ⟨74679732078007941291505339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99572976104010588388673785 74679732078007941291505339)
      ·
        refine ⟨112019598117011911937258009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74679732078007941291505339 112019598117011911937258009)
        ·
          refine ⟨84014698587758933952943507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112019598117011911937258009 84014698587758933952943507)
          ·
            refine ⟨126022047881638400929415261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84014698587758933952943507 126022047881638400929415261)
            ·
              refine ⟨47258267955614400348530723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126022047881638400929415261 47258267955614400348530723)
              ·
                refine ⟨70887401933421600522796085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47258267955614400348530723 70887401933421600522796085)
                ·
                  refine ⟨6645693931258275049012133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70887401933421600522796085 6645693931258275049012133)
                  ·
                    refine ⟨1246067612110926571689775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6645693931258275049012133 1246067612110926571689775)
                    ·
                      rfl

theorem cell23_7280124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_7280124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280124 prefixEnd_7280124 := by exact prefixLift 7280124
  have htrace : WordTrace (prefixWord ++ tailWord_7280124) baseStart_7280124 baseEnd_7280124 := by
    simpa [prefixWord, tailWord_7280124, baseEnd_7280124] using wordTrace_append hprefix tailTrace_7280124
  have hstable : (prefixWord ++ tailWord_7280124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280124).length < 2 ^ (prefixWord ++ tailWord_7280124).sum := by decide
  have hdescent : baseEnd_7280124 < baseStart_7280124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280127 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 4]
def baseStart_7280127 : Nat := 118140960795 + 7280127 * 2 ^ 59
def prefixEnd_7280127 : Nat := 4983230072969 + 3 ^ 40 * 7280127 * 2
def baseEnd_7280127 : Nat := 3738204376774743203331811

theorem tailTrace_7280127 : CollatzResearch.WordTrace tailWord_7280127 prefixEnd_7280127 3738204376774743203331811 := by
  unfold tailWord_7280127
  simp only [CollatzResearch.WordTrace]
  refine ⟨265528045696350700548822635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177018697130900467032548423 265528045696350700548822635)
  ·
    refine ⟨398292068544526050823233953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265528045696350700548822635 398292068544526050823233953)
    ·
      refine ⟨298719051408394538117425465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398292068544526050823233953 298719051408394538117425465)
      ·
        refine ⟨224039288556295903588069099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298719051408394538117425465 224039288556295903588069099)
        ·
          refine ⟨336058932834443855382103649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224039288556295903588069099 336058932834443855382103649)
          ·
            refine ⟨252044199625832891536577737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336058932834443855382103649 252044199625832891536577737)
            ·
              refine ⟨189033149719374668652433303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252044199625832891536577737 189033149719374668652433303)
              ·
                refine ⟨283549724579062002978649955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189033149719374668652433303 283549724579062002978649955)
                ·
                  refine ⟨425324586868593004467974933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283549724579062002978649955 425324586868593004467974933)
                  ·
                    refine ⟨19937090009465297084436325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 425324586868593004467974933 19937090009465297084436325)
                    ·
                      refine ⟨3738204376774743203331811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19937090009465297084436325 3738204376774743203331811)
                      ·
                        rfl

theorem cell23_7280127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_7280127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280127 prefixEnd_7280127 := by exact prefixLift 7280127
  have htrace : WordTrace (prefixWord ++ tailWord_7280127) baseStart_7280127 baseEnd_7280127 := by
    simpa [prefixWord, tailWord_7280127, baseEnd_7280127] using wordTrace_append hprefix tailTrace_7280127
  have hstable : (prefixWord ++ tailWord_7280127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280127).length < 2 ^ (prefixWord ++ tailWord_7280127).sum := by decide
  have hdescent : baseEnd_7280127 < baseStart_7280127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280137 : List Nat := [1, 2, 1, 1, 3, 1, 4, 2, 8]
def baseStart_7280137 : Nat := 118140960795 + 7280137 * 2 ^ 59
def prefixEnd_7280137 : Nat := 4983230072969 + 3 ^ 40 * 7280137 * 2
def baseEnd_7280137 : Nat := 415356612397920907134085

theorem tailTrace_7280137 : CollatzResearch.WordTrace tailWord_7280137 prefixEnd_7280137 415356612397920907134085 := by
  unfold tailWord_7280137
  simp only [CollatzResearch.WordTrace]
  refine ⟨265528410426314472256686665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177018940284209648171124443 265528410426314472256686665)
  ·
    refine ⟨199146307819735854192514999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265528410426314472256686665 199146307819735854192514999)
    ·
      refine ⟨298719461729603781288772499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199146307819735854192514999 298719461729603781288772499)
      ·
        refine ⟨448079192594405671933158749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298719461729603781288772499 448079192594405671933158749)
        ·
          refine ⟨168029697222902126974934531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 448079192594405671933158749 168029697222902126974934531)
          ·
            refine ⟨252044545834353190462401797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168029697222902126974934531 252044545834353190462401797)
            ·
              refine ⟨47258352343941223211700337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 252044545834353190462401797 47258352343941223211700337)
              ·
                refine ⟨35443764257955917408775253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47258352343941223211700337 35443764257955917408775253)
                ·
                  refine ⟨415356612397920907134085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35443764257955917408775253 415356612397920907134085)
                  ·
                    rfl

theorem cell23_7280137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 8].length) (baseStart_7280137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280137 prefixEnd_7280137 := by exact prefixLift 7280137
  have htrace : WordTrace (prefixWord ++ tailWord_7280137) baseStart_7280137 baseEnd_7280137 := by
    simpa [prefixWord, tailWord_7280137, baseEnd_7280137] using wordTrace_append hprefix tailTrace_7280137
  have hstable : (prefixWord ++ tailWord_7280137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280137).length < 2 ^ (prefixWord ++ tailWord_7280137).sum := by decide
  have hdescent : baseEnd_7280137 < baseStart_7280137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280191 : List Nat := [1, 1, 2, 2, 3, 3, 2, 1, 1, 5, 2]
def baseStart_7280191 : Nat := 118140960795 + 7280191 * 2 ^ 59
def prefixEnd_7280191 : Nat := 4983230072969 + 3 ^ 40 * 7280191 * 2
def baseEnd_7280191 : Nat := 3738237239536630952931517

theorem tailTrace_7280191 : CollatzResearch.WordTrace tailWord_7280191 prefixEnd_7280191 3738237239536630952931517 := by
  unfold tailWord_7280191
  simp only [CollatzResearch.WordTrace]
  refine ⟨265530379968118839479152427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177020253312079226319434951 265530379968118839479152427)
  ·
    refine ⟨398295569952178259218728641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265530379968118839479152427 398295569952178259218728641)
    ·
      refine ⟨298721677464133694414046481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398295569952178259218728641 298721677464133694414046481)
      ·
        refine ⟨224041258098100270810534861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298721677464133694414046481 224041258098100270810534861)
        ·
          refine ⟨84015471786787601553950573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224041258098100270810534861 84015471786787601553950573)
          ·
            refine ⟨31505801920045350582731465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84015471786787601553950573 31505801920045350582731465)
            ·
              refine ⟨23629351440034012937048599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31505801920045350582731465 23629351440034012937048599)
              ·
                refine ⟨35444027160051019405572899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23629351440034012937048599 35444027160051019405572899)
                ·
                  refine ⟨53166040740076529108359349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35444027160051019405572899 53166040740076529108359349)
                  ·
                    refine ⟨4984316319382174603908689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53166040740076529108359349 4984316319382174603908689)
                    ·
                      refine ⟨3738237239536630952931517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4984316319382174603908689 3738237239536630952931517)
                      ·
                        rfl

theorem cell23_7280191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 5, 2].length) (baseStart_7280191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280191 prefixEnd_7280191 := by exact prefixLift 7280191
  have htrace : WordTrace (prefixWord ++ tailWord_7280191) baseStart_7280191 baseEnd_7280191 := by
    simpa [prefixWord, tailWord_7280191, baseEnd_7280191] using wordTrace_append hprefix tailTrace_7280191
  have hstable : (prefixWord ++ tailWord_7280191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280191).length < 2 ^ (prefixWord ++ tailWord_7280191).sum := by decide
  have hdescent : baseEnd_7280191 < baseStart_7280191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280224 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 3]
def baseStart_7280224 : Nat := 118140960795 + 7280224 * 2 ^ 59
def prefixEnd_7280224 : Nat := 4983230072969 + 3 ^ 40 * 7280224 * 2
def baseEnd_7280224 : Nat := 3738254184398229323818865

theorem tailTrace_7280224 : CollatzResearch.WordTrace tailWord_7280224 prefixEnd_7280224 3738254184398229323818865 := by
  unfold tailWord_7280224
  simp only [CollatzResearch.WordTrace]
  refine ⟨132765791788499643057551863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177021055717999524076735817 132765791788499643057551863)
  ·
    refine ⟨199148687682749464586327795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132765791788499643057551863 199148687682749464586327795)
    ·
      refine ⟨298723031524124196879491693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199148687682749464586327795 298723031524124196879491693)
      ·
        refine ⟨112021136821546573829809385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298723031524124196879491693 112021136821546573829809385)
        ·
          refine ⟨84015852616159930372357039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112021136821546573829809385 84015852616159930372357039)
          ·
            refine ⟨126023778924239895558535559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84015852616159930372357039 126023778924239895558535559)
            ·
              refine ⟨189035668386359843337803339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126023778924239895558535559 189035668386359843337803339)
              ·
                refine ⟨283553502579539765006705009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189035668386359843337803339 283553502579539765006705009)
                ·
                  refine ⟨212665126934654823755028757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283553502579539765006705009 212665126934654823755028757)
                  ·
                    refine ⟨9968677825061944863516973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 212665126934654823755028757 9968677825061944863516973)
                    ·
                      refine ⟨3738254184398229323818865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9968677825061944863516973 3738254184398229323818865)
                      ·
                        rfl

theorem cell23_7280224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_7280224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280224 prefixEnd_7280224 := by exact prefixLift 7280224
  have htrace : WordTrace (prefixWord ++ tailWord_7280224) baseStart_7280224 baseEnd_7280224 := by
    simpa [prefixWord, tailWord_7280224, baseEnd_7280224] using wordTrace_append hprefix tailTrace_7280224
  have hstable : (prefixWord ++ tailWord_7280224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280224).length < 2 ^ (prefixWord ++ tailWord_7280224).sum := by decide
  have hdescent : baseEnd_7280224 < baseStart_7280224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280238 : List Nat := [4, 1, 2, 2, 3, 1, 1, 1, 3, 1, 4]
def baseStart_7280238 : Nat := 118140960795 + 7280238 * 2 ^ 59
def prefixEnd_7280238 : Nat := 4983230072969 + 3 ^ 40 * 7280238 * 2
def baseEnd_7280238 : Nat := 3738261373127392269043801

theorem tailTrace_7280238 : CollatzResearch.WordTrace tailWord_7280238 prefixEnd_7280238 3738261373127392269043801 := by
  unfold tailWord_7280238
  simp only [CollatzResearch.WordTrace]
  refine ⟨33191511774868570813264171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177021396132632377670742245 33191511774868570813264171)
  ·
    refine ⟨49787267662302856219896257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33191511774868570813264171 49787267662302856219896257)
    ·
      refine ⟨37340450746727142164922193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49787267662302856219896257 37340450746727142164922193)
      ·
        refine ⟨28005338060045356623691645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37340450746727142164922193 28005338060045356623691645)
        ·
          refine ⟨10502001772517008733884367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28005338060045356623691645 10502001772517008733884367)
          ·
            refine ⟨15753002658775513100826551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10502001772517008733884367 15753002658775513100826551)
            ·
              refine ⟨23629503988163269651239827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15753002658775513100826551 23629503988163269651239827)
              ·
                refine ⟨35444255982244904476859741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23629503988163269651239827 35444255982244904476859741)
                ·
                  refine ⟨13291595993341839178822403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35444255982244904476859741 13291595993341839178822403)
                  ·
                    refine ⟨19937393990012758768233605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13291595993341839178822403 19937393990012758768233605)
                    ·
                      refine ⟨3738261373127392269043801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19937393990012758768233605 3738261373127392269043801)
                      ·
                        rfl

theorem cell23_7280238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_7280238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280238 prefixEnd_7280238 := by exact prefixLift 7280238
  have htrace : WordTrace (prefixWord ++ tailWord_7280238) baseStart_7280238 baseEnd_7280238 := by
    simpa [prefixWord, tailWord_7280238, baseEnd_7280238] using wordTrace_append hprefix tailTrace_7280238
  have hstable : (prefixWord ++ tailWord_7280238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280238).length < 2 ^ (prefixWord ++ tailWord_7280238).sum := by decide
  have hdescent : baseEnd_7280238 < baseStart_7280238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280288 : List Nat := [2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 3]
def baseStart_7280288 : Nat := 118140960795 + 7280288 * 2 ^ 59
def prefixEnd_7280288 : Nat := 4983230072969 + 3 ^ 40 * 7280288 * 2
def baseEnd_7280288 : Nat := 3738287047160117073418571

theorem tailTrace_7280288 : CollatzResearch.WordTrace tailWord_7280288 prefixEnd_7280288 3738287047160117073418571 := by
  unfold tailWord_7280288
  simp only [CollatzResearch.WordTrace]
  refine ⟨132766958924383712522716759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177022611899178283363622345 132766958924383712522716759)
  ·
    refine ⟨199150438386575568784075139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132766958924383712522716759 199150438386575568784075139)
    ·
      refine ⟨298725657579863353176112709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199150438386575568784075139 298725657579863353176112709)
      ·
        refine ⟨56011060796224378720521133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 298725657579863353176112709 56011060796224378720521133)
        ·
          refine ⟨21004147798584142020195425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56011060796224378720521133 21004147798584142020195425)
          ·
            refine ⟨15753110848938106515146569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21004147798584142020195425 15753110848938106515146569)
            ·
              refine ⟨11814833136703579886359927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15753110848938106515146569 11814833136703579886359927)
              ·
                refine ⟨17722249705055369829539891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11814833136703579886359927 17722249705055369829539891)
                ·
                  refine ⟨26583374557583054744309837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17722249705055369829539891 26583374557583054744309837)
                  ·
                    refine ⟨9968765459093645529116189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26583374557583054744309837 9968765459093645529116189)
                    ·
                      refine ⟨3738287047160117073418571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9968765459093645529116189 3738287047160117073418571)
                      ·
                        rfl

theorem cell23_7280288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_7280288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280288 prefixEnd_7280288 := by exact prefixLift 7280288
  have htrace : WordTrace (prefixWord ++ tailWord_7280288) baseStart_7280288 baseEnd_7280288 := by
    simpa [prefixWord, tailWord_7280288, baseEnd_7280288] using wordTrace_append hprefix tailTrace_7280288
  have hstable : (prefixWord ++ tailWord_7280288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280288).length < 2 ^ (prefixWord ++ tailWord_7280288).sum := by decide
  have hdescent : baseEnd_7280288 < baseStart_7280288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280301 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_7280301 : Nat := 118140960795 + 7280301 * 2 ^ 59
def prefixEnd_7280301 : Nat := 4983230072969 + 3 ^ 40 * 7280301 * 2
def baseEnd_7280301 : Nat := 3738293722408625522556011

theorem tailTrace_7280301 : CollatzResearch.WordTrace tailWord_7280301 prefixEnd_7280301 3738293722408625522556011 := by
  unfold tailWord_7280301
  simp only [CollatzResearch.WordTrace]
  refine ⟨265534391997720328265656757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177022927998480218843771171 265534391997720328265656757)
  ·
    refine ⟨24893849249786280774905321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 265534391997720328265656757 24893849249786280774905321)
    ·
      refine ⟨18670386937339710581178991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24893849249786280774905321 18670386937339710581178991)
      ·
        refine ⟨28005580406009565871768487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18670386937339710581178991 28005580406009565871768487)
        ·
          refine ⟨42008370609014348807652731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28005580406009565871768487 42008370609014348807652731)
          ·
            refine ⟨63012555913521523211479097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42008370609014348807652731 63012555913521523211479097)
            ·
              refine ⟨47259416935141142408609323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63012555913521523211479097 47259416935141142408609323)
              ·
                refine ⟨70889125402711713612913985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47259416935141142408609323 70889125402711713612913985)
                ·
                  refine ⟨53166844052033785209685489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70889125402711713612913985 53166844052033785209685489)
                  ·
                    refine ⟨39875133039025338907264117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53166844052033785209685489 39875133039025338907264117)
                    ·
                      refine ⟨3738293722408625522556011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39875133039025338907264117 3738293722408625522556011)
                      ·
                        rfl

theorem cell23_7280301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_7280301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280301 prefixEnd_7280301 := by exact prefixLift 7280301
  have htrace : WordTrace (prefixWord ++ tailWord_7280301) baseStart_7280301 baseEnd_7280301 := by
    simpa [prefixWord, tailWord_7280301, baseEnd_7280301] using wordTrace_append hprefix tailTrace_7280301
  have hstable : (prefixWord ++ tailWord_7280301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280301).length < 2 ^ (prefixWord ++ tailWord_7280301).sum := by decide
  have hdescent : baseEnd_7280301 < baseStart_7280301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280309 : List Nat := [1, 3, 3, 3, 3, 1, 2, 1, 1, 2, 3]
def baseStart_7280309 : Nat := 118140960795 + 7280309 * 2 ^ 59
def prefixEnd_7280309 : Nat := 4983230072969 + 3 ^ 40 * 7280309 * 2
def baseEnd_7280309 : Nat := 3738297830253861491255975

theorem tailTrace_7280309 : CollatzResearch.WordTrace tailWord_7280309 prefixEnd_7280309 3738297830253861491255975 := by
  unfold tailWord_7280309
  simp only [CollatzResearch.WordTrace]
  refine ⟨265534683781691345631947981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177023122521127563754631987 265534683781691345631947981)
  ·
    refine ⟨99575506418134254611980493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265534683781691345631947981 99575506418134254611980493)
    ·
      refine ⟨37340814906800345479492685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99575506418134254611980493 37340814906800345479492685)
      ·
        refine ⟨14002805590050129554809757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37340814906800345479492685 14002805590050129554809757)
        ·
          refine ⟨5251052096268798583053659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14002805590050129554809757 5251052096268798583053659)
          ·
            refine ⟨7876578144403197874580489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5251052096268798583053659 7876578144403197874580489)
            ·
              refine ⟨5907433608302398405935367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7876578144403197874580489 5907433608302398405935367)
              ·
                refine ⟨8861150412453597608903051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5907433608302398405935367 8861150412453597608903051)
                ·
                  refine ⟨13291725618680396413354577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8861150412453597608903051 13291725618680396413354577)
                  ·
                    refine ⟨9968794214010297310015933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13291725618680396413354577 9968794214010297310015933)
                    ·
                      refine ⟨3738297830253861491255975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9968794214010297310015933 3738297830253861491255975)
                      ·
                        rfl

theorem cell23_7280309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_7280309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280309 prefixEnd_7280309 := by exact prefixLift 7280309
  have htrace : WordTrace (prefixWord ++ tailWord_7280309) baseStart_7280309 baseEnd_7280309 := by
    simpa [prefixWord, tailWord_7280309, baseEnd_7280309] using wordTrace_append hprefix tailTrace_7280309
  have hstable : (prefixWord ++ tailWord_7280309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280309).length < 2 ^ (prefixWord ++ tailWord_7280309).sum := by decide
  have hdescent : baseEnd_7280309 < baseStart_7280309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280345 : List Nat := [1, 2, 1, 2, 3, 5, 1, 1, 1, 4, 2]
def baseStart_7280345 : Nat := 118140960795 + 7280345 * 2 ^ 59
def prefixEnd_7280345 : Nat := 4983230072969 + 3 ^ 40 * 7280345 * 2
def baseEnd_7280345 : Nat := 3738316315557423350405809

theorem tailTrace_7280345 : CollatzResearch.WordTrace tailWord_7280345 prefixEnd_7280345 3738316315557423350405809 := by
  unfold tailWord_7280345
  simp only [CollatzResearch.WordTrace]
  refine ⟨265535996809560923780258489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177023997873040615853505659 265535996809560923780258489)
  ·
    refine ⟨199151997607170692835193867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265535996809560923780258489 199151997607170692835193867)
    ·
      refine ⟨298727996410756039252790801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199151997607170692835193867 298727996410756039252790801)
      ·
        refine ⟨224045997308067029439593101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298727996410756039252790801 224045997308067029439593101)
        ·
          refine ⟨84017248990525136039847413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224045997308067029439593101 84017248990525136039847413)
          ·
            refine ⟨7876617092861731503735695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84017248990525136039847413 7876617092861731503735695)
            ·
              refine ⟨11814925639292597255603543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7876617092861731503735695 11814925639292597255603543)
              ·
                refine ⟨17722388458938895883405315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11814925639292597255603543 17722388458938895883405315)
                ·
                  refine ⟨26583582688408343825107973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17722388458938895883405315 26583582688408343825107973)
                  ·
                    refine ⟨4984421754076564467207745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26583582688408343825107973 4984421754076564467207745)
                    ·
                      refine ⟨3738316315557423350405809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4984421754076564467207745 3738316315557423350405809)
                      ·
                        rfl

theorem cell23_7280345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 4, 2].length) (baseStart_7280345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280345 prefixEnd_7280345 := by exact prefixLift 7280345
  have htrace : WordTrace (prefixWord ++ tailWord_7280345) baseStart_7280345 baseEnd_7280345 := by
    simpa [prefixWord, tailWord_7280345, baseEnd_7280345] using wordTrace_append hprefix tailTrace_7280345
  have hstable : (prefixWord ++ tailWord_7280345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280345).length < 2 ^ (prefixWord ++ tailWord_7280345).sum := by decide
  have hdescent : baseEnd_7280345 < baseStart_7280345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280349 : List Nat := [1, 4, 3, 3, 1, 1, 2, 2, 1, 3, 2]
def baseStart_7280349 : Nat := 118140960795 + 7280349 * 2 ^ 59
def prefixEnd_7280349 : Nat := 4983230072969 + 3 ^ 40 * 7280349 * 2
def baseEnd_7280349 : Nat := 3738318369480041334755791

theorem tailTrace_7280349 : CollatzResearch.WordTrace tailWord_7280349 prefixEnd_7280349 3738318369480041334755791 := by
  unfold tailWord_7280349
  simp only [CollatzResearch.WordTrace]
  refine ⟨265536142701546432463404101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177024095134364288308936067 265536142701546432463404101)
  ·
    refine ⟨49788026756539956086888269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265536142701546432463404101 49788026756539956086888269)
    ·
      refine ⟨18670510033702483532583101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49788026756539956086888269 18670510033702483532583101)
      ·
        refine ⟨7001441262638431324718663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18670510033702483532583101 7001441262638431324718663)
        ·
          refine ⟨10502161893957646987077995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7001441262638431324718663 10502161893957646987077995)
          ·
            refine ⟨15753242840936470480616993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10502161893957646987077995 15753242840936470480616993)
            ·
              refine ⟨11814932130702352860462745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15753242840936470480616993 11814932130702352860462745)
              ·
                refine ⟨8861199098026764645347059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11814932130702352860462745 8861199098026764645347059)
                ·
                  refine ⟨13291798647040146968020589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8861199098026764645347059 13291798647040146968020589)
                  ·
                    refine ⟨4984424492640055113007721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13291798647040146968020589 4984424492640055113007721)
                    ·
                      refine ⟨3738318369480041334755791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4984424492640055113007721 3738318369480041334755791)
                      ·
                        rfl

theorem cell23_7280349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_7280349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280349 prefixEnd_7280349 := by exact prefixLift 7280349
  have htrace : WordTrace (prefixWord ++ tailWord_7280349) baseStart_7280349 baseEnd_7280349 := by
    simpa [prefixWord, tailWord_7280349, baseEnd_7280349] using wordTrace_append hprefix tailTrace_7280349
  have hstable : (prefixWord ++ tailWord_7280349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280349).length < 2 ^ (prefixWord ++ tailWord_7280349).sum := by decide
  have hdescent : baseEnd_7280349 < baseStart_7280349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280401 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 4]
def baseStart_7280401 : Nat := 118140960795 + 7280401 * 2 ^ 59
def prefixEnd_7280401 : Nat := 4983230072969 + 3 ^ 40 * 7280401 * 2
def baseEnd_7280401 : Nat := 3738345070474075131305551

theorem tailTrace_7280401 : CollatzResearch.WordTrace tailWord_7280401 prefixEnd_7280401 3738345070474075131305551 := by
  unfold tailWord_7280401
  simp only [CollatzResearch.WordTrace]
  refine ⟨265538039297358045344297057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177025359531572030229531371 265538039297358045344297057)
  ·
    refine ⟨199153529473018534008222793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265538039297358045344297057 199153529473018534008222793)
    ·
      refine ⟨149365147104763900506167095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199153529473018534008222793 149365147104763900506167095)
      ·
        refine ⟨224047720657145850759250643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149365147104763900506167095 224047720657145850759250643)
        ·
          refine ⟨336071580985718776138875965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224047720657145850759250643 336071580985718776138875965)
          ·
            refine ⟨126026842869644541052078487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 336071580985718776138875965 126026842869644541052078487)
            ·
              refine ⟨189040264304466811578117731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126026842869644541052078487 189040264304466811578117731)
              ·
                refine ⟨283560396456700217367176597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189040264304466811578117731 283560396456700217367176597)
                ·
                  refine ⟨13291893583907822689086403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 283560396456700217367176597 13291893583907822689086403)
                  ·
                    refine ⟨19937840375861734033629605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13291893583907822689086403 19937840375861734033629605)
                    ·
                      refine ⟨3738345070474075131305551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19937840375861734033629605 3738345070474075131305551)
                      ·
                        rfl

theorem cell23_7280401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_7280401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280401 prefixEnd_7280401 := by exact prefixLift 7280401
  have htrace : WordTrace (prefixWord ++ tailWord_7280401) baseStart_7280401 baseEnd_7280401 := by
    simpa [prefixWord, tailWord_7280401, baseEnd_7280401] using wordTrace_append hprefix tailTrace_7280401
  have hstable : (prefixWord ++ tailWord_7280401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280401).length < 2 ^ (prefixWord ++ tailWord_7280401).sum := by decide
  have hdescent : baseEnd_7280401 < baseStart_7280401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280522 : List Nat := [3, 1, 2, 4, 2, 1, 2, 2, 1, 5]
def baseStart_7280522 : Nat := 118140960795 + 7280522 * 2 ^ 59
def prefixEnd_7280522 : Nat := 4983230072969 + 3 ^ 40 * 7280522 * 2
def baseEnd_7280522 : Nat := 1246135733877756385964165

theorem tailTrace_7280522 : CollatzResearch.WordTrace tailWord_7280522 prefixEnd_7280522 1246135733877756385964165 := by
  unfold tailWord_7280522
  simp only [CollatzResearch.WordTrace]
  refine ⟨66385613132479920752362955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177028301686613122006301213 66385613132479920752362955)
  ·
    refine ⟨99578419698719881128544433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66385613132479920752362955 99578419698719881128544433)
    ·
      refine ⟨74683814774039910846408325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99578419698719881128544433 74683814774039910846408325)
      ·
        refine ⟨14003215270132483283701561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74683814774039910846408325 14003215270132483283701561)
        ·
          refine ⟨10502411452599362462776171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14003215270132483283701561 10502411452599362462776171)
          ·
            refine ⟨15753617178899043694164257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10502411452599362462776171 15753617178899043694164257)
            ·
              refine ⟨11815212884174282770623193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15753617178899043694164257 11815212884174282770623193)
              ·
                refine ⟨8861409663130712077967395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11815212884174282770623193 8861409663130712077967395)
                ·
                  refine ⟨13292114494696068116951093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8861409663130712077967395 13292114494696068116951093)
                  ·
                    refine ⟨1246135733877756385964165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13292114494696068116951093 1246135733877756385964165)
                    ·
                      rfl

theorem cell23_7280522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_7280522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280522 prefixEnd_7280522 := by exact prefixLift 7280522
  have htrace : WordTrace (prefixWord ++ tailWord_7280522) baseStart_7280522 baseEnd_7280522 := by
    simpa [prefixWord, tailWord_7280522, baseEnd_7280522] using wordTrace_append hprefix tailTrace_7280522
  have hstable : (prefixWord ++ tailWord_7280522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280522).length < 2 ^ (prefixWord ++ tailWord_7280522).sum := by decide
  have hdescent : baseEnd_7280522 < baseStart_7280522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280548 : List Nat := [2, 3, 1, 2, 1, 5, 9]
def baseStart_7280548 : Nat := 118140960795 + 7280548 * 2 ^ 59
def prefixEnd_7280548 : Nat := 4983230072969 + 3 ^ 40 * 7280548 * 2
def baseEnd_7280548 : Nat := 46153340149756617977375

theorem tailTrace_7280548 : CollatzResearch.WordTrace tailWord_7280548 prefixEnd_7280548 46153340149756617977375 := by
  unfold tailWord_7280548
  simp only [CollatzResearch.WordTrace]
  refine ⟨132771700413912744724949149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177028933885216992966598865 132771700413912744724949149)
  ·
    refine ⟨49789387655217279271855931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132771700413912744724949149 49789387655217279271855931)
    ·
      refine ⟨74684081482825918907783897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49789387655217279271855931 74684081482825918907783897)
      ·
        refine ⟨56013061112119439180837923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74684081482825918907783897 56013061112119439180837923)
        ·
          refine ⟨84019591668179158771256885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56013061112119439180837923 84019591668179158771256885)
          ·
            refine ⟨7876836718891796134805333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84019591668179158771256885 7876836718891796134805333)
            ·
              refine ⟨46153340149756617977375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7876836718891796134805333 46153340149756617977375)
              ·
                rfl

theorem cell23_7280548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 9].length) (baseStart_7280548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280548 prefixEnd_7280548 := by exact prefixLift 7280548
  have htrace : WordTrace (prefixWord ++ tailWord_7280548) baseStart_7280548 baseEnd_7280548 := by
    simpa [prefixWord, tailWord_7280548, baseEnd_7280548] using wordTrace_append hprefix tailTrace_7280548
  have hstable : (prefixWord ++ tailWord_7280548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280548).length < 2 ^ (prefixWord ++ tailWord_7280548).sum := by decide
  have hdescent : baseEnd_7280548 < baseStart_7280548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280585 : List Nat := [1, 2, 1, 1, 2, 1, 2, 5, 3, 3, 2]
def baseStart_7280585 : Nat := 118140960795 + 7280585 * 2 ^ 59
def prefixEnd_7280585 : Nat := 4983230072969 + 3 ^ 40 * 7280585 * 2
def baseEnd_7280585 : Nat := 3738439550914502411404705

theorem tailTrace_7280585 : CollatzResearch.WordTrace tailWord_7280585 prefixEnd_7280585 3738439550914502411404705 := by
  unfold tailWord_7280585
  simp only [CollatzResearch.WordTrace]
  refine ⟨265544750328691444768995209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177029833552460963179330139 265544750328691444768995209)
  ·
    refine ⟨199158562746518583576746407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265544750328691444768995209 199158562746518583576746407)
    ·
      refine ⟨298737844119777875365119611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199158562746518583576746407 298737844119777875365119611)
      ·
        refine ⟨448106766179666813047679417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298737844119777875365119611 448106766179666813047679417)
        ·
          refine ⟨336080074634750109785759563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448106766179666813047679417 336080074634750109785759563)
          ·
            refine ⟨504120111952125164678639345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336080074634750109785759563 504120111952125164678639345)
            ·
              refine ⟨378090083964093873508979509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 504120111952125164678639345 378090083964093873508979509)
              ·
                refine ⟨35445945371633800641466829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 378090083964093873508979509 35445945371633800641466829)
                ·
                  refine ⟨13292229514362675240550061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35445945371633800641466829 13292229514362675240550061)
                  ·
                    refine ⟨4984586067886003215206273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13292229514362675240550061 4984586067886003215206273)
                    ·
                      refine ⟨3738439550914502411404705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4984586067886003215206273 3738439550914502411404705)
                      ·
                        rfl

theorem cell23_7280585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 3, 2].length) (baseStart_7280585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280585 prefixEnd_7280585 := by exact prefixLift 7280585
  have htrace : WordTrace (prefixWord ++ tailWord_7280585) baseStart_7280585 baseEnd_7280585 := by
    simpa [prefixWord, tailWord_7280585, baseEnd_7280585] using wordTrace_append hprefix tailTrace_7280585
  have hstable : (prefixWord ++ tailWord_7280585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280585).length < 2 ^ (prefixWord ++ tailWord_7280585).sum := by decide
  have hdescent : baseEnd_7280585 < baseStart_7280585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280625 : List Nat := [1, 2, 2, 2, 5, 1, 1, 1, 2, 6]
def baseStart_7280625 : Nat := 118140960795 + 7280625 * 2 ^ 59
def prefixEnd_7280625 : Nat := 4983230072969 + 3 ^ 40 * 7280625 * 2
def baseEnd_7280625 : Nat := 1246153363380227418301507

theorem tailTrace_7280625 : CollatzResearch.WordTrace tailWord_7280625 prefixEnd_7280625 1246153363380227418301507 := by
  unfold tailWord_7280625
  simp only [CollatzResearch.WordTrace]
  refine ⟨265546209248546531600451329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177030806165697687733634219 265546209248546531600451329)
  ·
    refine ⟨199159656936409898700338497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265546209248546531600451329 199159656936409898700338497)
    ·
      refine ⟨149369742702307424025253873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199159656936409898700338497 149369742702307424025253873)
      ·
        refine ⟨112027307026730568018940405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149369742702307424025253873 112027307026730568018940405)
        ·
          refine ⟨10502560033755990751775663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112027307026730568018940405 10502560033755990751775663)
          ·
            refine ⟨15753840050633986127663495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10502560033755990751775663 15753840050633986127663495)
            ·
              refine ⟨23630760075950979191495243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15753840050633986127663495 23630760075950979191495243)
              ·
                refine ⟨35446140113926468787242865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23630760075950979191495243 35446140113926468787242865)
                ·
                  refine ⟨26584605085444851590432149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35446140113926468787242865 26584605085444851590432149)
                  ·
                    refine ⟨1246153363380227418301507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26584605085444851590432149 1246153363380227418301507)
                    ·
                      rfl

theorem cell23_7280625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 6].length) (baseStart_7280625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280625 prefixEnd_7280625 := by exact prefixLift 7280625
  have htrace : WordTrace (prefixWord ++ tailWord_7280625) baseStart_7280625 baseEnd_7280625 := by
    simpa [prefixWord, tailWord_7280625, baseEnd_7280625] using wordTrace_append hprefix tailTrace_7280625
  have hstable : (prefixWord ++ tailWord_7280625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280625).length < 2 ^ (prefixWord ++ tailWord_7280625).sum := by decide
  have hdescent : baseEnd_7280625 < baseStart_7280625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280660 : List Nat := [2, 4, 3, 2, 2, 1, 1, 2, 2, 1, 3]
def baseStart_7280660 : Nat := 118140960795 + 7280660 * 2 ^ 59
def prefixEnd_7280660 : Nat := 4983230072969 + 3 ^ 40 * 7280660 * 2
def baseEnd_7280660 : Nat := 3738478061963589617966861

theorem tailTrace_7280660 : CollatzResearch.WordTrace tailWord_7280660 prefixEnd_7280660 3738478061963589617966861 := by
  unfold tailWord_7280660
  simp only [CollatzResearch.WordTrace]
  refine ⟨132773742901709866288987717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177031657202279821718650289 132773742901709866288987717)
  ·
    refine ⟨24895076794070599929185197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132773742901709866288987717 24895076794070599929185197)
    ·
      refine ⟨9335653797776474973444449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24895076794070599929185197 9335653797776474973444449)
      ·
        refine ⟨7001740348332356230083337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9335653797776474973444449 7001740348332356230083337)
        ·
          refine ⟨5251305261249267172562503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7001740348332356230083337 5251305261249267172562503)
          ·
            refine ⟨7876957891873900758843755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5251305261249267172562503 7876957891873900758843755)
            ·
              refine ⟨11815436837810851138265633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7876957891873900758843755 11815436837810851138265633)
              ·
                refine ⟨8861577628358138353699225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11815436837810851138265633 8861577628358138353699225)
                ·
                  refine ⟨6646183221268603765274419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8861577628358138353699225 6646183221268603765274419)
                  ·
                    refine ⟨9969274831902905647911629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6646183221268603765274419 9969274831902905647911629)
                    ·
                      refine ⟨3738478061963589617966861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9969274831902905647911629 3738478061963589617966861)
                      ·
                        rfl

theorem cell23_7280660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_7280660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280660 prefixEnd_7280660 := by exact prefixLift 7280660
  have htrace : WordTrace (prefixWord ++ tailWord_7280660) baseStart_7280660 baseEnd_7280660 := by
    simpa [prefixWord, tailWord_7280660, baseEnd_7280660] using wordTrace_append hprefix tailTrace_7280660
  have hstable : (prefixWord ++ tailWord_7280660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280660).length < 2 ^ (prefixWord ++ tailWord_7280660).sum := by decide
  have hdescent : baseEnd_7280660 < baseStart_7280660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280666 : List Nat := [3, 1, 1, 3, 1, 5, 1, 2, 2, 2, 2]
def baseStart_7280666 : Nat := 118140960795 + 7280666 * 2 ^ 59
def prefixEnd_7280666 : Nat := 4983230072969 + 3 ^ 40 * 7280666 * 2
def baseEnd_7280666 : Nat := 3738481142847516594491833

theorem tailTrace_7280666 : CollatzResearch.WordTrace tailWord_7280666 prefixEnd_7280666 3738481142847516594491833 := by
  unfold tailWord_7280666
  simp only [CollatzResearch.WordTrace]
  refine ⟨66386926160349498900673463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177031803094265330401795901 66386926160349498900673463)
  ·
    refine ⟨99580389240524248351010195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66386926160349498900673463 99580389240524248351010195)
    ·
      refine ⟨149370583860786372526515293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99580389240524248351010195 149370583860786372526515293)
      ·
        refine ⟨56013968947794889697443235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149370583860786372526515293 56013968947794889697443235)
        ·
          refine ⟨84020953421692334546164853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56013968947794889697443235 84020953421692334546164853)
          ·
            refine ⟨7876964383283656363702955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84020953421692334546164853 7876964383283656363702955)
            ·
              refine ⟨11815446574925484545554433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7876964383283656363702955 11815446574925484545554433)
              ·
                refine ⟨8861584931194113409165825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11815446574925484545554433 8861584931194113409165825)
                ·
                  refine ⟨6646188698395585056874369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8861584931194113409165825 6646188698395585056874369)
                  ·
                    refine ⟨4984641523796688792655777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6646188698395585056874369 4984641523796688792655777)
                    ·
                      refine ⟨3738481142847516594491833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4984641523796688792655777 3738481142847516594491833)
                      ·
                        rfl

theorem cell23_7280666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_7280666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280666 prefixEnd_7280666 := by exact prefixLift 7280666
  have htrace : WordTrace (prefixWord ++ tailWord_7280666) baseStart_7280666 baseEnd_7280666 := by
    simpa [prefixWord, tailWord_7280666, baseEnd_7280666] using wordTrace_append hprefix tailTrace_7280666
  have hstable : (prefixWord ++ tailWord_7280666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280666).length < 2 ^ (prefixWord ++ tailWord_7280666).sum := by decide
  have hdescent : baseEnd_7280666 < baseStart_7280666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280682 : List Nat := [3, 1, 4, 1, 2, 1, 2, 1, 2, 3, 3]
def baseStart_7280682 : Nat := 118140960795 + 7280682 * 2 ^ 59
def prefixEnd_7280682 : Nat := 4983230072969 + 3 ^ 40 * 7280682 * 2
def baseEnd_7280682 : Nat := 3738489358537988531891759

theorem tailTrace_7280682 : CollatzResearch.WordTrace tailWord_7280682 prefixEnd_7280682 3738489358537988531891759 := by
  unfold tailWord_7280682
  simp only [CollatzResearch.WordTrace]
  refine ⟨66387072052335007583819075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177032192139560020223517533 66387072052335007583819075)
  ·
    refine ⟨99580608078502511375728613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66387072052335007583819075 99580608078502511375728613)
    ·
      refine ⟨18671364014719220882949115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99580608078502511375728613 18671364014719220882949115)
      ·
        refine ⟨28007046022078831324423673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18671364014719220882949115 28007046022078831324423673)
        ·
          refine ⟨21005284516559123493317755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28007046022078831324423673 21005284516559123493317755)
          ·
            refine ⟨31507926774838685239976633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21005284516559123493317755 31507926774838685239976633)
            ·
              refine ⟨23630945081129013929982475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31507926774838685239976633 23630945081129013929982475)
              ·
                refine ⟨35446417621693520894973713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23630945081129013929982475 35446417621693520894973713)
                ·
                  refine ⟨26584813216270140671230285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35446417621693520894973713 26584813216270140671230285)
                  ·
                    refine ⟨9969304956101302751711357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26584813216270140671230285 9969304956101302751711357)
                    ·
                      refine ⟨3738489358537988531891759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9969304956101302751711357 3738489358537988531891759)
                      ·
                        rfl

theorem cell23_7280682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_7280682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280682 prefixEnd_7280682 := by exact prefixLift 7280682
  have htrace : WordTrace (prefixWord ++ tailWord_7280682) baseStart_7280682 baseEnd_7280682 := by
    simpa [prefixWord, tailWord_7280682, baseEnd_7280682] using wordTrace_append hprefix tailTrace_7280682
  have hstable : (prefixWord ++ tailWord_7280682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280682).length < 2 ^ (prefixWord ++ tailWord_7280682).sum := by decide
  have hdescent : baseEnd_7280682 < baseStart_7280682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280698 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 1, 10]
def baseStart_7280698 : Nat := 118140960795 + 7280698 * 2 ^ 59
def prefixEnd_7280698 : Nat := 4983230072969 + 3 ^ 40 * 7280698 * 2
def baseEnd_7280698 : Nat := 1246165858076153489763895

theorem tailTrace_7280698 : CollatzResearch.WordTrace tailWord_7280698 prefixEnd_7280698 1246165858076153489763895 := by
  unfold tailWord_7280698
  simp only [CollatzResearch.WordTrace]
  refine ⟨66387217944320516266964687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177032581184854710045239165 66387217944320516266964687)
  ·
    refine ⟨99580826916480774400447031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66387217944320516266964687 99580826916480774400447031)
    ·
      refine ⟨149371240374721161600670547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99580826916480774400447031 149371240374721161600670547)
      ·
        refine ⟨224056860562081742401005821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149371240374721161600670547 224056860562081742401005821)
        ·
          refine ⟨84021322710780653400377183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224056860562081742401005821 84021322710780653400377183)
          ·
            refine ⟨126031984066170980100565775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84021322710780653400377183 126031984066170980100565775)
            ·
              refine ⟨189047976099256470150848663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126031984066170980100565775 189047976099256470150848663)
              ·
                refine ⟨283571964148884705226272995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189047976099256470150848663 283571964148884705226272995)
                ·
                  refine ⟨425357946223327057839409493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283571964148884705226272995 425357946223327057839409493)
                  ·
                    refine ⟨1246165858076153489763895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 425357946223327057839409493 1246165858076153489763895)
                    ·
                      rfl

theorem cell23_7280698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 1, 10].length) (baseStart_7280698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280698 prefixEnd_7280698 := by exact prefixLift 7280698
  have htrace : WordTrace (prefixWord ++ tailWord_7280698) baseStart_7280698 baseEnd_7280698 := by
    simpa [prefixWord, tailWord_7280698, baseEnd_7280698] using wordTrace_append hprefix tailTrace_7280698
  have hstable : (prefixWord ++ tailWord_7280698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280698).length < 2 ^ (prefixWord ++ tailWord_7280698).sum := by decide
  have hdescent : baseEnd_7280698 < baseStart_7280698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280734 : List Nat := [4, 4, 1, 1, 3, 1, 2, 1, 2, 2, 2]
def baseStart_7280734 : Nat := 118140960795 + 7280734 * 2 ^ 59
def prefixEnd_7280734 : Nat := 4983230072969 + 3 ^ 40 * 7280734 * 2
def baseEnd_7280734 : Nat := 3738516059532022328441521

theorem tailTrace_7280734 : CollatzResearch.WordTrace tailWord_7280734 prefixEnd_7280734 3738516059532022328441521 := by
  unfold tailWord_7280734
  simp only [CollatzResearch.WordTrace]
  refine ⟨33193773100643955402021157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177033456536767762144112837 33193773100643955402021157)
  ·
    refine ⟨6223832456370741637878967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33193773100643955402021157 6223832456370741637878967)
    ·
      refine ⟨9335748684556112456818451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6223832456370741637878967 9335748684556112456818451)
      ·
        refine ⟨14003623026834168685227677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9335748684556112456818451 14003623026834168685227677)
        ·
          refine ⟨5251358635062813256960379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14003623026834168685227677 5251358635062813256960379)
          ·
            refine ⟨7877037952594219885440569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5251358635062813256960379 7877037952594219885440569)
            ·
              refine ⟨5907778464445664914080427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7877037952594219885440569 5907778464445664914080427)
              ·
                refine ⟨8861667696668497371120641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5907778464445664914080427 8861667696668497371120641)
                ·
                  refine ⟨6646250772501373028340481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8861667696668497371120641 6646250772501373028340481)
                  ·
                    refine ⟨4984688079376029771255361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6646250772501373028340481 4984688079376029771255361)
                    ·
                      refine ⟨3738516059532022328441521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4984688079376029771255361 3738516059532022328441521)
                      ·
                        rfl

theorem cell23_7280734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_7280734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280734 prefixEnd_7280734 := by exact prefixLift 7280734
  have htrace : WordTrace (prefixWord ++ tailWord_7280734) baseStart_7280734 baseEnd_7280734 := by
    simpa [prefixWord, tailWord_7280734, baseEnd_7280734] using wordTrace_append hprefix tailTrace_7280734
  have hstable : (prefixWord ++ tailWord_7280734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280734).length < 2 ^ (prefixWord ++ tailWord_7280734).sum := by decide
  have hdescent : baseEnd_7280734 < baseStart_7280734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280745 : List Nat := [1, 2, 1, 1, 1, 5, 3, 3, 6]
def baseStart_7280745 : Nat := 118140960795 + 7280745 * 2 ^ 59
def prefixEnd_7280745 : Nat := 4983230072969 + 3 ^ 40 * 7280745 * 2
def baseEnd_7280745 : Nat := 415391300868802420600441

theorem tailTrace_7280745 : CollatzResearch.WordTrace tailWord_7280745 prefixEnd_7280745 415391300868802420600441 := by
  unfold tailWord_7280745
  simp only [CollatzResearch.WordTrace]
  refine ⟨265550586008111792094819689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177033724005407861396546459 265550586008111792094819689)
  ·
    refine ⟨199162939506083844071114767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265550586008111792094819689 199162939506083844071114767)
    ·
      refine ⟨298744409259125766106672151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199162939506083844071114767 298744409259125766106672151)
      ·
        refine ⟨448116613888688649160008227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298744409259125766106672151 448116613888688649160008227)
        ·
          refine ⟨672174920833032973740012341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448116613888688649160008227 672174920833032973740012341)
          ·
            refine ⟨63016398828096841288126157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 672174920833032973740012341 63016398828096841288126157)
            ·
              refine ⟨23631149560536315483047309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63016398828096841288126157 23631149560536315483047309)
              ·
                refine ⟨8861681085201118306142741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23631149560536315483047309 8861681085201118306142741)
                ·
                  refine ⟨415391300868802420600441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8861681085201118306142741 415391300868802420600441)
                  ·
                    rfl

theorem cell23_7280745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 6].length) (baseStart_7280745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280745 prefixEnd_7280745 := by exact prefixLift 7280745
  have htrace : WordTrace (prefixWord ++ tailWord_7280745) baseStart_7280745 baseEnd_7280745 := by
    simpa [prefixWord, tailWord_7280745, baseEnd_7280745] using wordTrace_append hprefix tailTrace_7280745
  have hstable : (prefixWord ++ tailWord_7280745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280745).length < 2 ^ (prefixWord ++ tailWord_7280745).sum := by decide
  have hdescent : baseEnd_7280745 < baseStart_7280745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280795 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 4]
def baseStart_7280795 : Nat := 118140960795 + 7280795 * 2 ^ 59
def prefixEnd_7280795 : Nat := 4983230072969 + 3 ^ 40 * 7280795 * 2
def baseEnd_7280795 : Nat := 3738547381851946589778739

theorem tailTrace_7280795 : CollatzResearch.WordTrace tailWord_7280795 prefixEnd_7280795 3738547381851946589778739 := by
  unfold tailWord_7280795
  simp only [CollatzResearch.WordTrace]
  refine ⟨265552409657930650634139839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177034939771953767089426559 265552409657930650634139839)
  ·
    refine ⟨398328614486895975951209759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265552409657930650634139839 398328614486895975951209759)
    ·
      refine ⟨597492921730343963926814639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398328614486895975951209759 597492921730343963926814639)
      ·
        refine ⟨896239382595515945890221959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597492921730343963926814639 896239382595515945890221959)
        ·
          refine ⟨1344359073893273918835332939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 896239382595515945890221959 1344359073893273918835332939)
          ·
            refine ⟨2016538610839910878252999409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1344359073893273918835332939 2016538610839910878252999409)
            ·
              refine ⟨1512403958129933158689749557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2016538610839910878252999409 1512403958129933158689749557)
              ·
                refine ⟨141787871074681233627164021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1512403958129933158689749557 141787871074681233627164021)
                ·
                  refine ⟨13292612913251365652546627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141787871074681233627164021 13292612913251365652546627)
                  ·
                    refine ⟨19938919369877048478819941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13292612913251365652546627 19938919369877048478819941)
                    ·
                      refine ⟨3738547381851946589778739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19938919369877048478819941 3738547381851946589778739)
                      ·
                        rfl

theorem cell23_7280795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 4].length) (baseStart_7280795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280795 prefixEnd_7280795 := by exact prefixLift 7280795
  have htrace : WordTrace (prefixWord ++ tailWord_7280795) baseStart_7280795 baseEnd_7280795 := by
    simpa [prefixWord, tailWord_7280795, baseEnd_7280795] using wordTrace_append hprefix tailTrace_7280795
  have hstable : (prefixWord ++ tailWord_7280795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280795).length < 2 ^ (prefixWord ++ tailWord_7280795).sum := by decide
  have hdescent : baseEnd_7280795 < baseStart_7280795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280829 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 7, 2, 2]
def baseStart_7280829 : Nat := 118140960795 + 7280829 * 2 ^ 59
def prefixEnd_7280829 : Nat := 4983230072969 + 3 ^ 40 * 7280829 * 2
def baseEnd_7280829 : Nat := 3738564840194199456753583

theorem tailTrace_7280829 : CollatzResearch.WordTrace tailWord_7280829 prefixEnd_7280829 3738564840194199456753583 := by
  unfold tailWord_7280829
  simp only [CollatzResearch.WordTrace]
  refine ⟨265553649739807474440877541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177035766493204982960585027 265553649739807474440877541)
  ·
    refine ⟨49791309326213901457664539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265553649739807474440877541 49791309326213901457664539)
    ·
      refine ⟨74686963989320852186496809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49791309326213901457664539 74686963989320852186496809)
      ·
        refine ⟨56015222991990639139872607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74686963989320852186496809 56015222991990639139872607)
        ·
          refine ⟨84022834487985958709808911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56015222991990639139872607 84022834487985958709808911)
          ·
            refine ⟨126034251731978938064713367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84022834487985958709808911 126034251731978938064713367)
            ·
              refine ⟨189051377597968407097070051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126034251731978938064713367 189051377597968407097070051)
              ·
                refine ⟨283577066396952610645605077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189051377597968407097070051 283577066396952610645605077)
                ·
                  refine ⟨6646337493678576812006369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 283577066396952610645605077 6646337493678576812006369)
                  ·
                    refine ⟨4984753120258932609004777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6646337493678576812006369 4984753120258932609004777)
                    ·
                      refine ⟨3738564840194199456753583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4984753120258932609004777 3738564840194199456753583)
                      ·
                        rfl

theorem cell23_7280829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_7280829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280829 prefixEnd_7280829 := by exact prefixLift 7280829
  have htrace : WordTrace (prefixWord ++ tailWord_7280829) baseStart_7280829 baseEnd_7280829 := by
    simpa [prefixWord, tailWord_7280829, baseEnd_7280829] using wordTrace_append hprefix tailTrace_7280829
  have hstable : (prefixWord ++ tailWord_7280829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280829).length < 2 ^ (prefixWord ++ tailWord_7280829).sum := by decide
  have hdescent : baseEnd_7280829 < baseStart_7280829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280846 : List Nat := [4, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2]
def baseStart_7280846 : Nat := 118140960795 + 7280846 * 2 ^ 59
def prefixEnd_7280846 : Nat := 4983230072969 + 3 ^ 40 * 7280846 * 2
def baseEnd_7280846 : Nat := 3738573569365325890241005

theorem tailTrace_7280846 : CollatzResearch.WordTrace tailWord_7280846 prefixEnd_7280846 3738573569365325890241005 := by
  unfold tailWord_7280846
  simp only [CollatzResearch.WordTrace]
  refine ⟨33194283722593235793030799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177036179853830590896164261 33194283722593235793030799)
  ·
    refine ⟨49791425583889853689546199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33194283722593235793030799 49791425583889853689546199)
    ·
      refine ⟨74687138375834780534319299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49791425583889853689546199 74687138375834780534319299)
      ·
        refine ⟨112030707563752170801478949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74687138375834780534319299 112030707563752170801478949)
        ·
          refine ⟨21005757668203532025277303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112030707563752170801478949 21005757668203532025277303)
          ·
            refine ⟨31508636502305298037915955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21005757668203532025277303 31508636502305298037915955)
            ·
              refine ⟨47262954753457947056873933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31508636502305298037915955 47262954753457947056873933)
              ·
                refine ⟨17723608032546730146327725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47262954753457947056873933 17723608032546730146327725)
                ·
                  refine ⟨6646353012205023804872897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17723608032546730146327725 6646353012205023804872897)
                  ·
                    refine ⟨4984764759153767853654673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6646353012205023804872897 4984764759153767853654673)
                    ·
                      refine ⟨3738573569365325890241005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4984764759153767853654673 3738573569365325890241005)
                      ·
                        rfl

theorem cell23_7280846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2].length) (baseStart_7280846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280846 prefixEnd_7280846 := by exact prefixLift 7280846
  have htrace : WordTrace (prefixWord ++ tailWord_7280846) baseStart_7280846 baseEnd_7280846 := by
    simpa [prefixWord, tailWord_7280846, baseEnd_7280846] using wordTrace_append hprefix tailTrace_7280846
  have hstable : (prefixWord ++ tailWord_7280846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280846).length < 2 ^ (prefixWord ++ tailWord_7280846).sum := by decide
  have hdescent : baseEnd_7280846 < baseStart_7280846 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280856 : List Nat := [2, 1, 2, 2, 4, 2, 3, 1, 2, 4]
def baseStart_7280856 : Nat := 118140960795 + 7280856 * 2 ^ 59
def prefixEnd_7280856 : Nat := 4983230072969 + 3 ^ 40 * 7280856 * 2
def baseEnd_7280856 : Nat := 1246192901390623617038653

theorem tailTrace_7280856 : CollatzResearch.WordTrace tailWord_7280856 prefixEnd_7280856 1246192901390623617038653 := by
  unfold tailWord_7280856
  simp only [CollatzResearch.WordTrace]
  refine ⟨132777317255354829026055211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177036423007139772034740281 132777317255354829026055211)
  ·
    refine ⟨199165975883032243539082817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132777317255354829026055211 199165975883032243539082817)
    ·
      refine ⟨149374481912274182654312113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199165975883032243539082817 149374481912274182654312113)
      ·
        refine ⟨112030861434205636990734085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149374481912274182654312113 112030861434205636990734085)
        ·
          refine ⟨21005786518913556935762641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112030861434205636990734085 21005786518913556935762641)
          ·
            refine ⟨15754339889185167701821981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21005786518913556935762641 15754339889185167701821981)
            ·
              refine ⟨5907877458444437888183243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15754339889185167701821981 5907877458444437888183243)
              ·
                refine ⟨8861816187666656832274865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5907877458444437888183243 8861816187666656832274865)
                ·
                  refine ⟨6646362140749992624206149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8861816187666656832274865 6646362140749992624206149)
                  ·
                    refine ⟨1246192901390623617038653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6646362140749992624206149 1246192901390623617038653)
                    ·
                      rfl

theorem cell23_7280856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 2, 4].length) (baseStart_7280856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280856 prefixEnd_7280856 := by exact prefixLift 7280856
  have htrace : WordTrace (prefixWord ++ tailWord_7280856) baseStart_7280856 baseEnd_7280856 := by
    simpa [prefixWord, tailWord_7280856, baseEnd_7280856] using wordTrace_append hprefix tailTrace_7280856
  have hstable : (prefixWord ++ tailWord_7280856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280856).length < 2 ^ (prefixWord ++ tailWord_7280856).sum := by decide
  have hdescent : baseEnd_7280856 < baseStart_7280856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280869 : List Nat := [1, 3, 1, 4, 2, 3, 2, 7]
def baseStart_7280869 : Nat := 118140960795 + 7280869 * 2 ^ 59
def prefixEnd_7280869 : Nat := 4983230072969 + 3 ^ 40 * 7280869 * 2
def baseEnd_7280869 : Nat := 138466125163717751861237

theorem tailTrace_7280869 : CollatzResearch.WordTrace tailWord_7280869 prefixEnd_7280869 138466125163717751861237 := by
  unfold tailWord_7280869
  simp only [CollatzResearch.WordTrace]
  refine ⟨265555108659662561272333661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177036739106441707514889107 265555108659662561272333661)
  ·
    refine ⟨99583165747373460477125123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265555108659662561272333661 99583165747373460477125123)
    ·
      refine ⟨149374748621060190715687685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99583165747373460477125123 149374748621060190715687685)
      ·
        refine ⟨28007765366448785759191441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149374748621060190715687685 28007765366448785759191441)
        ·
          refine ⟨21005824024836589319393581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28007765366448785759191441 21005824024836589319393581)
          ·
            refine ⟨7877184009313720994772593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21005824024836589319393581 7877184009313720994772593)
            ·
              refine ⟨5907888006985290746079445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7877184009313720994772593 5907888006985290746079445)
              ·
                refine ⟨138466125163717751861237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5907888006985290746079445 138466125163717751861237)
                ·
                  rfl

theorem cell23_7280869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 7].length) (baseStart_7280869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280869 prefixEnd_7280869 := by exact prefixLift 7280869
  have htrace : WordTrace (prefixWord ++ tailWord_7280869) baseStart_7280869 baseEnd_7280869 := by
    simpa [prefixWord, tailWord_7280869, baseEnd_7280869] using wordTrace_append hprefix tailTrace_7280869
  have hstable : (prefixWord ++ tailWord_7280869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280869).length < 2 ^ (prefixWord ++ tailWord_7280869).sum := by decide
  have hdescent : baseEnd_7280869 < baseStart_7280869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280875 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 5]
def baseStart_7280875 : Nat := 118140960795 + 7280875 * 2 ^ 59
def prefixEnd_7280875 : Nat := 4983230072969 + 3 ^ 40 * 7280875 * 2
def baseEnd_7280875 : Nat := 3738588460304306276778371

theorem tailTrace_7280875 : CollatzResearch.WordTrace tailWord_7280875 prefixEnd_7280875 3738588460304306276778371 := by
  unfold tailWord_7280875
  simp only [CollatzResearch.WordTrace]
  refine ⟨265555327497640824297052079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177036884998427216198034719 265555327497640824297052079)
  ·
    refine ⟨398332991246461236445578119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265555327497640824297052079 398332991246461236445578119)
    ·
      refine ⟨597499486869691854668367179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398332991246461236445578119 597499486869691854668367179)
      ·
        refine ⟨896249230304537782002550769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597499486869691854668367179 896249230304537782002550769)
        ·
          refine ⟨672186922728403336501913077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 896249230304537782002550769 672186922728403336501913077)
          ·
            refine ⟨63017524005787812797054351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 672186922728403336501913077 63017524005787812797054351)
            ·
              refine ⟨94526286008681719195581527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63017524005787812797054351 94526286008681719195581527)
              ·
                refine ⟨141789429013022578793372291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94526286008681719195581527 141789429013022578793372291)
                ·
                  refine ⟨212684143519533868190058437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141789429013022578793372291 212684143519533868190058437)
                  ·
                    refine ⟨39878276909912600285635957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 212684143519533868190058437 39878276909912600285635957)
                    ·
                      refine ⟨3738588460304306276778371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39878276909912600285635957 3738588460304306276778371)
                      ·
                        rfl

theorem cell23_7280875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 5].length) (baseStart_7280875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280875 prefixEnd_7280875 := by exact prefixLift 7280875
  have htrace : WordTrace (prefixWord ++ tailWord_7280875) baseStart_7280875 baseEnd_7280875 := by
    simpa [prefixWord, tailWord_7280875, baseEnd_7280875] using wordTrace_append hprefix tailTrace_7280875
  have hstable : (prefixWord ++ tailWord_7280875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280875).length < 2 ^ (prefixWord ++ tailWord_7280875).sum := by decide
  have hdescent : baseEnd_7280875 < baseStart_7280875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280879 : List Nat := [1, 1, 2, 1, 6, 1, 1, 2, 4, 1, 3]
def baseStart_7280879 : Nat := 118140960795 + 7280879 * 2 ^ 59
def prefixEnd_7280879 : Nat := 4983230072969 + 3 ^ 40 * 7280879 * 2
def baseEnd_7280879 : Nat := 3738590514226924261128353

theorem tailTrace_7280879 : CollatzResearch.WordTrace tailWord_7280879 prefixEnd_7280879 3738590514226924261128353 := by
  unfold tailWord_7280879
  simp only [CollatzResearch.WordTrace]
  refine ⟨265555473389626332980197691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177036982259750888653465127 265555473389626332980197691)
  ·
    refine ⟨398333210084439499470296537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265555473389626332980197691 398333210084439499470296537)
    ·
      refine ⟨298749907563329624602722403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398333210084439499470296537 298749907563329624602722403)
      ·
        refine ⟨448124861344994436904083605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298749907563329624602722403 448124861344994436904083605)
        ·
          refine ⟨21005852875546614229878919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 448124861344994436904083605 21005852875546614229878919)
          ·
            refine ⟨31508779313319921344818379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21005852875546614229878919 31508779313319921344818379)
            ·
              refine ⟨47263168969979882017227569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31508779313319921344818379 47263168969979882017227569)
              ·
                refine ⟨35447376727484911512920677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47263168969979882017227569 35447376727484911512920677)
                ·
                  refine ⟨6646383136403420908672627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35447376727484911512920677 6646383136403420908672627)
                  ·
                    refine ⟨9969574704605131363008941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6646383136403420908672627 9969574704605131363008941)
                    ·
                      refine ⟨3738590514226924261128353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9969574704605131363008941 3738590514226924261128353)
                      ·
                        rfl

theorem cell23_7280879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 4, 1, 3].length) (baseStart_7280879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280879 prefixEnd_7280879 := by exact prefixLift 7280879
  have htrace : WordTrace (prefixWord ++ tailWord_7280879) baseStart_7280879 baseEnd_7280879 := by
    simpa [prefixWord, tailWord_7280879, baseEnd_7280879] using wordTrace_append hprefix tailTrace_7280879
  have hstable : (prefixWord ++ tailWord_7280879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280879).length < 2 ^ (prefixWord ++ tailWord_7280879).sum := by decide
  have hdescent : baseEnd_7280879 < baseStart_7280879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280913 : List Nat := [1, 2, 2, 1, 1, 7, 2, 1, 2, 1, 3]
def baseStart_7280913 : Nat := 118140960795 + 7280913 * 2 ^ 59
def prefixEnd_7280913 : Nat := 4983230072969 + 3 ^ 40 * 7280913 * 2
def baseEnd_7280913 : Nat := 3738607972569177128103197

theorem tailTrace_7280913 : CollatzResearch.WordTrace tailWord_7280913 prefixEnd_7280913 3738607972569177128103197 := by
  unfold tailWord_7280913
  simp only [CollatzResearch.WordTrace]
  refine ⟨265556713471503156786935393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177037808981002104524623595 265556713471503156786935393)
  ·
    refine ⟨199167535103627367590201545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265556713471503156786935393 199167535103627367590201545)
    ·
      refine ⟨149375651327720525692651159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199167535103627367590201545 149375651327720525692651159)
      ·
        refine ⟨224063476991580788538976739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149375651327720525692651159 224063476991580788538976739)
        ·
          refine ⟨336095215487371182808465109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224063476991580788538976739 336095215487371182808465109)
          ·
            refine ⟨7877231612985262097073401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 336095215487371182808465109 7877231612985262097073401)
            ·
              refine ⟨5907923709738946572805051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7877231612985262097073401 5907923709738946572805051)
              ·
                refine ⟨8861885564608419859207577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5907923709738946572805051 8861885564608419859207577)
                ·
                  refine ⟨6646414173456314894405683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8861885564608419859207577 6646414173456314894405683)
                  ·
                    refine ⟨9969621260184472341608525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6646414173456314894405683 9969621260184472341608525)
                    ·
                      refine ⟨3738607972569177128103197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9969621260184472341608525 3738607972569177128103197)
                      ·
                        rfl

theorem cell23_7280913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 2, 1, 3].length) (baseStart_7280913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280913 prefixEnd_7280913 := by exact prefixLift 7280913
  have htrace : WordTrace (prefixWord ++ tailWord_7280913) baseStart_7280913 baseEnd_7280913 := by
    simpa [prefixWord, tailWord_7280913, baseEnd_7280913] using wordTrace_append hprefix tailTrace_7280913
  have hstable : (prefixWord ++ tailWord_7280913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280913).length < 2 ^ (prefixWord ++ tailWord_7280913).sum := by decide
  have hdescent : baseEnd_7280913 < baseStart_7280913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280915 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 6]
def baseStart_7280915 : Nat := 118140960795 + 7280915 * 2 ^ 59
def prefixEnd_7280915 : Nat := 4983230072969 + 3 ^ 40 * 7280915 * 2
def baseEnd_7280915 : Nat := 3738608999530486120278187

theorem tailTrace_7280915 : CollatzResearch.WordTrace tailWord_7280915 prefixEnd_7280915 3738608999530486120278187 := by
  unfold tailWord_7280915
  simp only [CollatzResearch.WordTrace]
  refine ⟨265556786417495911128508199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177037857611663940752338799 265556786417495911128508199)
  ·
    refine ⟨398335179626243866692762299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265556786417495911128508199 398335179626243866692762299)
    ·
      refine ⟨597502769439365800039143449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398335179626243866692762299 597502769439365800039143449)
      ·
        refine ⟨448127077079524350029357587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 597502769439365800039143449 448127077079524350029357587)
        ·
          refine ⟨672190615619286525044036381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448127077079524350029357587 672190615619286525044036381)
          ·
            refine ⟨252071480857232446891513643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 672190615619286525044036381 252071480857232446891513643)
            ·
              refine ⟨378107221285848670337270465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252071480857232446891513643 378107221285848670337270465)
              ·
                refine ⟨283580415964386502752952849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 378107221285848670337270465 283580415964386502752952849)
                ·
                  refine ⟨212685311973289877064714637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283580415964386502752952849 212685311973289877064714637)
                  ·
                    refine ⟨79756991989983703899267989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 212685311973289877064714637 79756991989983703899267989)
                    ·
                      refine ⟨3738608999530486120278187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79756991989983703899267989 3738608999530486120278187)
                      ·
                        rfl

theorem cell23_7280915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 6].length) (baseStart_7280915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280915 prefixEnd_7280915 := by exact prefixLift 7280915
  have htrace : WordTrace (prefixWord ++ tailWord_7280915) baseStart_7280915 baseEnd_7280915 := by
    simpa [prefixWord, tailWord_7280915, baseEnd_7280915] using wordTrace_append hprefix tailTrace_7280915
  have hstable : (prefixWord ++ tailWord_7280915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280915).length < 2 ^ (prefixWord ++ tailWord_7280915).sum := by decide
  have hdescent : baseEnd_7280915 < baseStart_7280915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280953 : List Nat := [1, 2, 1, 6, 1, 1, 1, 4, 2, 2, 2]
def baseStart_7280953 : Nat := 118140960795 + 7280953 * 2 ^ 59
def prefixEnd_7280953 : Nat := 4983230072969 + 3 ^ 40 * 7280953 * 2
def baseEnd_7280953 : Nat := 3738628511795356971603013

theorem tailTrace_7280953 : CollatzResearch.WordTrace tailWord_7280953 prefixEnd_7280953 3738628511795356971603013 := by
  unfold tailWord_7280953
  simp only [CollatzResearch.WordTrace]
  refine ⟨265558172391358243618391513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177038781594238829078927675 265558172391358243618391513)
  ·
    refine ⟨199168629293518682713793635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265558172391358243618391513 199168629293518682713793635)
    ·
      refine ⟨298752943940278024070690453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199168629293518682713793635 298752943940278024070690453)
      ·
        refine ⟨14004044247200532378313615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 298752943940278024070690453 14004044247200532378313615)
        ·
          refine ⟨21006066370800798567470423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14004044247200532378313615 21006066370800798567470423)
          ·
            refine ⟨31509099556201197851205635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21006066370800798567470423 31509099556201197851205635)
            ·
              refine ⟨47263649334301796776808453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31509099556201197851205635 47263649334301796776808453)
              ·
                refine ⟨8861934250181586895651585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47263649334301796776808453 8861934250181586895651585)
                ·
                  refine ⟨6646450687636190171738689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8861934250181586895651585 6646450687636190171738689)
                  ·
                    refine ⟨4984838015727142628804017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6646450687636190171738689 4984838015727142628804017)
                    ·
                      refine ⟨3738628511795356971603013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4984838015727142628804017 3738628511795356971603013)
                      ·
                        rfl

theorem cell23_7280953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_7280953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280953 prefixEnd_7280953 := by exact prefixLift 7280953
  have htrace : WordTrace (prefixWord ++ tailWord_7280953) baseStart_7280953 baseEnd_7280953 := by
    simpa [prefixWord, tailWord_7280953, baseEnd_7280953] using wordTrace_append hprefix tailTrace_7280953
  have hstable : (prefixWord ++ tailWord_7280953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280953).length < 2 ^ (prefixWord ++ tailWord_7280953).sum := by decide
  have hdescent : baseEnd_7280953 < baseStart_7280953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280959 : List Nat := [1, 1, 2, 2, 4, 1, 3, 4, 5]
def baseStart_7280959 : Nat := 118140960795 + 7280959 * 2 ^ 59
def prefixEnd_7280959 : Nat := 4983230072969 + 3 ^ 40 * 7280959 * 2
def baseEnd_7280959 : Nat := 415403510297698216458665

theorem tailTrace_7280959 : CollatzResearch.WordTrace tailWord_7280959 prefixEnd_7280959 415403510297698216458665 := by
  unfold tailWord_7280959
  simp only [CollatzResearch.WordTrace]
  refine ⟨265558391229336506643109931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177038927486224337762073287 265558391229336506643109931)
  ·
    refine ⟨398337586844004759964664897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265558391229336506643109931 398337586844004759964664897)
    ·
      refine ⟨298753190133003569973498673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398337586844004759964664897 298753190133003569973498673)
      ·
        refine ⟨224064892599752677480124005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298753190133003569973498673 224064892599752677480124005)
        ·
          refine ⟨42012167362453627027523251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224064892599752677480124005 42012167362453627027523251)
          ·
            refine ⟨63018251043680440541284877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42012167362453627027523251 63018251043680440541284877)
            ·
              refine ⟨23631844141380165202981829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63018251043680440541284877 23631844141380165202981829)
              ·
                refine ⟨4430970776508780975559093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23631844141380165202981829 4430970776508780975559093)
                ·
                  refine ⟨415403510297698216458665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4430970776508780975559093 415403510297698216458665)
                  ·
                    rfl

theorem cell23_7280959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 4, 5].length) (baseStart_7280959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280959 prefixEnd_7280959 := by exact prefixLift 7280959
  have htrace : WordTrace (prefixWord ++ tailWord_7280959) baseStart_7280959 baseEnd_7280959 := by
    simpa [prefixWord, tailWord_7280959, baseEnd_7280959] using wordTrace_append hprefix tailTrace_7280959
  have hstable : (prefixWord ++ tailWord_7280959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280959).length < 2 ^ (prefixWord ++ tailWord_7280959).sum := by decide
  have hdescent : baseEnd_7280959 < baseStart_7280959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280972 : List Nat := [2, 2, 1, 3, 2, 1, 2, 2, 1, 7]
def baseStart_7280972 : Nat := 118140960795 + 7280972 * 2 ^ 59
def prefixEnd_7280972 : Nat := 4983230072969 + 3 ^ 40 * 7280972 * 2
def baseEnd_7280972 : Nat := 1246212755975930799088475

theorem tailTrace_7280972 : CollatzResearch.WordTrace tailWord_7280972 prefixEnd_7280972 1246212755975930799088475 := by
  unfold tailWord_7280972
  simp only [CollatzResearch.WordTrace]
  refine ⟨132779432689144704931666585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177039243585526273242222113 132779432689144704931666585)
  ·
    refine ⟨99584574516858528698749939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132779432689144704931666585 99584574516858528698749939)
    ·
      refine ⟨149376861775287793048124909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99584574516858528698749939 149376861775287793048124909)
      ·
        refine ⟨56016323165732922393046841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149376861775287793048124909 56016323165732922393046841)
        ·
          refine ⟨42012242374299691794785131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56016323165732922393046841 42012242374299691794785131)
          ·
            refine ⟨63018363561449537692177697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42012242374299691794785131 63018363561449537692177697)
            ·
              refine ⟨47263772671087153269133273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63018363561449537692177697 47263772671087153269133273)
              ·
                refine ⟨35447829503315364951849955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47263772671087153269133273 35447829503315364951849955)
                ·
                  refine ⟨53171744254973047427774933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35447829503315364951849955 53171744254973047427774933)
                  ·
                    refine ⟨1246212755975930799088475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53171744254973047427774933 1246212755975930799088475)
                    ·
                      rfl

theorem cell23_7280972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 1, 7].length) (baseStart_7280972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7280972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7280972 prefixEnd_7280972 := by exact prefixLift 7280972
  have htrace : WordTrace (prefixWord ++ tailWord_7280972) baseStart_7280972 baseEnd_7280972 := by
    simpa [prefixWord, tailWord_7280972, baseEnd_7280972] using wordTrace_append hprefix tailTrace_7280972
  have hstable : (prefixWord ++ tailWord_7280972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280972).length < 2 ^ (prefixWord ++ tailWord_7280972).sum := by decide
  have hdescent : baseEnd_7280972 < baseStart_7280972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281019 : List Nat := [1, 1, 1, 1, 1, 7, 1, 3, 3, 4]
def baseStart_7281019 : Nat := 118140960795 + 7281019 * 2 ^ 59
def prefixEnd_7281019 : Nat := 4983230072969 + 3 ^ 40 * 7281019 * 2
def baseEnd_7281019 : Nat := 1246220800506184571125903

theorem tailTrace_7281019 : CollatzResearch.WordTrace tailWord_7281019 prefixEnd_7281019 1246220800506184571125903 := by
  unfold tailWord_7281019
  simp only [CollatzResearch.WordTrace]
  refine ⟨265560579609119136890294111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177040386406079424593529407 265560579609119136890294111)
  ·
    refine ⟨398340869413678705335441167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265560579609119136890294111 398340869413678705335441167)
    ·
      refine ⟨597511304120518058003161751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398340869413678705335441167 597511304120518058003161751)
      ·
        refine ⟨896266956180777087004742627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597511304120518058003161751 896266956180777087004742627)
        ·
          refine ⟨1344400434271165630507113941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 896266956180777087004742627 1344400434271165630507113941)
          ·
            refine ⟨31509385178230444465010483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1344400434271165630507113941 31509385178230444465010483)
            ·
              refine ⟨47264077767345666697515725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31509385178230444465010483 47264077767345666697515725)
              ·
                refine ⟨17724029162754625011568397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47264077767345666697515725 17724029162754625011568397)
                ·
                  refine ⟨6646510936032984379338149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17724029162754625011568397 6646510936032984379338149)
                  ·
                    refine ⟨1246220800506184571125903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6646510936032984379338149 1246220800506184571125903)
                    ·
                      rfl

theorem cell23_7281019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 3, 4].length) (baseStart_7281019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281019 prefixEnd_7281019 := by exact prefixLift 7281019
  have htrace : WordTrace (prefixWord ++ tailWord_7281019) baseStart_7281019 baseEnd_7281019 := by
    simpa [prefixWord, tailWord_7281019, baseEnd_7281019] using wordTrace_append hprefix tailTrace_7281019
  have hstable : (prefixWord ++ tailWord_7281019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281019).length < 2 ^ (prefixWord ++ tailWord_7281019).sum := by decide
  have hdescent : baseEnd_7281019 < baseStart_7281019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281086 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2]
def baseStart_7281086 : Nat := 118140960795 + 7281086 * 2 ^ 59
def prefixEnd_7281086 : Nat := 4983230072969 + 3 ^ 40 * 7281086 * 2
def baseEnd_7281086 : Nat := 3738696804722404951239901

theorem tailTrace_7281086 : CollatzResearch.WordTrace tailWord_7281086 prefixEnd_7281086 3738696804722404951239901 := by
  unfold tailWord_7281086
  simp only [CollatzResearch.WordTrace]
  refine ⟨33195377912484550916622889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177042015533250938221988741 33195377912484550916622889)
  ·
    refine ⟨24896533434363413187467167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33195377912484550916622889 24896533434363413187467167)
    ·
      refine ⟨37344800151545119781200751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24896533434363413187467167 37344800151545119781200751)
      ·
        refine ⟨56017200227317679671801127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37344800151545119781200751 56017200227317679671801127)
        ·
          refine ⟨84025800340976519507701691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56017200227317679671801127 84025800340976519507701691)
          ·
            refine ⟨126038700511464779261552537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84025800340976519507701691 126038700511464779261552537)
            ·
              refine ⟨94529025383598584446164403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126038700511464779261552537 94529025383598584446164403)
              ·
                refine ⟨141793538075397876669246605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94529025383598584446164403 141793538075397876669246605)
                ·
                  refine ⟨53172576778274203750967477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141793538075397876669246605 53172576778274203750967477)
                  ·
                    refine ⟨4984929072963206601653201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53172576778274203750967477 4984929072963206601653201)
                    ·
                      refine ⟨3738696804722404951239901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4984929072963206601653201 3738696804722404951239901)
                      ·
                        rfl

theorem cell23_7281086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_7281086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281086 prefixEnd_7281086 := by exact prefixLift 7281086
  have htrace : WordTrace (prefixWord ++ tailWord_7281086) baseStart_7281086 baseEnd_7281086 := by
    simpa [prefixWord, tailWord_7281086, baseEnd_7281086] using wordTrace_append hprefix tailTrace_7281086
  have hstable : (prefixWord ++ tailWord_7281086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281086).length < 2 ^ (prefixWord ++ tailWord_7281086).sum := by decide
  have hdescent : baseEnd_7281086 < baseStart_7281086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281096 : List Nat := [2, 1, 3, 1, 3, 2, 3, 2, 1, 5]
def baseStart_7281096 : Nat := 118140960795 + 7281096 * 2 ^ 59
def prefixEnd_7281096 : Nat := 4983230072969 + 3 ^ 40 * 7281096 * 2
def baseEnd_7281096 : Nat := 1246233979842983304038285

theorem tailTrace_7281096 : CollatzResearch.WordTrace tailWord_7281096 prefixEnd_7281096 1246233979842983304038285 := by
  unfold tailWord_7281096
  simp only [CollatzResearch.WordTrace]
  refine ⟨132781694014920089520423571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177042258686560119360564761 132781694014920089520423571)
  ·
    refine ⟨199172541022380134280635357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132781694014920089520423571 199172541022380134280635357)
    ·
      refine ⟨74689702883392550355238259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199172541022380134280635357 74689702883392550355238259)
      ·
        refine ⟨112034554325088825532857389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74689702883392550355238259 112034554325088825532857389)
        ·
          refine ⟨42012957871908309574821521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112034554325088825532857389 42012957871908309574821521)
          ·
            refine ⟨31509718403931232181116141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42012957871908309574821521 31509718403931232181116141)
            ·
              refine ⟨11816144401474212067918553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31509718403931232181116141 11816144401474212067918553)
              ·
                refine ⟨8862108301105659050938915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11816144401474212067918553 8862108301105659050938915)
                ·
                  refine ⟨13293162451658488576408373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8862108301105659050938915 13293162451658488576408373)
                  ·
                    refine ⟨1246233979842983304038285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13293162451658488576408373 1246233979842983304038285)
                    ·
                      rfl

theorem cell23_7281096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_7281096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281096 prefixEnd_7281096 := by exact prefixLift 7281096
  have htrace : WordTrace (prefixWord ++ tailWord_7281096) baseStart_7281096 baseEnd_7281096 := by
    simpa [prefixWord, tailWord_7281096, baseEnd_7281096] using wordTrace_append hprefix tailTrace_7281096
  have hstable : (prefixWord ++ tailWord_7281096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281096).length < 2 ^ (prefixWord ++ tailWord_7281096).sum := by decide
  have hdescent : baseEnd_7281096 < baseStart_7281096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281109 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 3, 6]
def baseStart_7281109 : Nat := 118140960795 + 7281109 * 2 ^ 59
def prefixEnd_7281109 : Nat := 4983230072969 + 3 ^ 40 * 7281109 * 2
def baseEnd_7281109 : Nat := 1246236204925819453750765

theorem tailTrace_7281109 : CollatzResearch.WordTrace tailWord_7281109 prefixEnd_7281109 1246236204925819453750765 := by
  unfold tailWord_7281109
  simp only [CollatzResearch.WordTrace]
  refine ⟨265563862178793082261070381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177042574785862054840713587 265563862178793082261070381)
  ·
    refine ⟨99586448317047405847901393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265563862178793082261070381 99586448317047405847901393)
    ·
      refine ⟨74689836237785554385926045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99586448317047405847901393 74689836237785554385926045)
      ·
        refine ⟨28008688589169582894722267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74689836237785554385926045 28008688589169582894722267)
        ·
          refine ⟨42013032883754374342083401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28008688589169582894722267 42013032883754374342083401)
          ·
            refine ⟨31509774662815780756562551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42013032883754374342083401 31509774662815780756562551)
            ·
              refine ⟨47264661994223671134843827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31509774662815780756562551 47264661994223671134843827)
              ·
                refine ⟨70896992991335506702265741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47264661994223671134843827 70896992991335506702265741)
                ·
                  refine ⟨26586372371750815013349653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70896992991335506702265741 26586372371750815013349653)
                  ·
                    refine ⟨1246236204925819453750765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26586372371750815013349653 1246236204925819453750765)
                    ·
                      rfl

theorem cell23_7281109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_7281109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281109 prefixEnd_7281109 := by exact prefixLift 7281109
  have htrace : WordTrace (prefixWord ++ tailWord_7281109) baseStart_7281109 baseEnd_7281109 := by
    simpa [prefixWord, tailWord_7281109, baseEnd_7281109] using wordTrace_append hprefix tailTrace_7281109
  have hstable : (prefixWord ++ tailWord_7281109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281109).length < 2 ^ (prefixWord ++ tailWord_7281109).sum := by decide
  have hdescent : baseEnd_7281109 < baseStart_7281109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281154 : List Nat := [3, 4, 1, 2, 3, 1, 1, 1, 2, 3, 2]
def baseStart_7281154 : Nat := 118140960795 + 7281154 * 2 ^ 59
def prefixEnd_7281154 : Nat := 4983230072969 + 3 ^ 40 * 7281154 * 2
def baseEnd_7281154 : Nat := 3738731721406910685189589

theorem tailTrace_7281154 : CollatzResearch.WordTrace tailWord_7281154 prefixEnd_7281154 3738731721406910685189589 := by
  unfold tailWord_7281154
  simp only [CollatzResearch.WordTrace]
  refine ⟨66391375865907513736614629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177043668975753369964305677 66391375865907513736614629)
  ·
    refine ⟨12448382974857658825615243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66391375865907513736614629 12448382974857658825615243)
    ·
      refine ⟨18672574462286488238422865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12448382974857658825615243 18672574462286488238422865)
      ·
        refine ⟨14004430846714866178817149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18672574462286488238422865 14004430846714866178817149)
        ·
          refine ⟨5251661567518074817056431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14004430846714866178817149 5251661567518074817056431)
          ·
            refine ⟨7877492351277112225584647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5251661567518074817056431 7877492351277112225584647)
            ·
              refine ⟨11816238526915668338376971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7877492351277112225584647 11816238526915668338376971)
              ·
                refine ⟨17724357790373502507565457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11816238526915668338376971 17724357790373502507565457)
                ·
                  refine ⟨13293268342780126880674093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17724357790373502507565457 13293268342780126880674093)
                  ·
                    refine ⟨4984975628542547580252785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13293268342780126880674093 4984975628542547580252785)
                    ·
                      refine ⟨3738731721406910685189589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4984975628542547580252785 3738731721406910685189589)
                      ·
                        rfl

theorem cell23_7281154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_7281154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281154 prefixEnd_7281154 := by exact prefixLift 7281154
  have htrace : WordTrace (prefixWord ++ tailWord_7281154) baseStart_7281154 baseEnd_7281154 := by
    simpa [prefixWord, tailWord_7281154, baseEnd_7281154] using wordTrace_append hprefix tailTrace_7281154
  have hstable : (prefixWord ++ tailWord_7281154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281154).length < 2 ^ (prefixWord ++ tailWord_7281154).sum := by decide
  have hdescent : baseEnd_7281154 < baseStart_7281154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281189 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 1, 5, 4]
def baseStart_7281189 : Nat := 118140960795 + 7281189 * 2 ^ 59
def prefixEnd_7281189 : Nat := 4983230072969 + 3 ^ 40 * 7281189 * 2
def baseEnd_7281189 : Nat := 3738749693229818048251927

theorem tailTrace_7281189 : CollatzResearch.WordTrace tailWord_7281189 prefixEnd_7281189 3738749693229818048251927 := by
  unfold tailWord_7281189
  simp only [CollatzResearch.WordTrace]
  refine ⟨265566780018503255923982621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177044520012335503949321747 265566780018503255923982621)
  ·
    refine ⟨99587542506938720971493483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265566780018503255923982621 99587542506938720971493483)
    ·
      refine ⟨149381313760408081457240225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99587542506938720971493483 149381313760408081457240225)
      ·
        refine ⟨112035985320306061092930169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149381313760408081457240225 112035985320306061092930169)
        ·
          refine ⟨84026988990229545819697627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112035985320306061092930169 84026988990229545819697627)
          ·
            refine ⟨126040483485344318729546441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84026988990229545819697627 126040483485344318729546441)
            ·
              refine ⟨94530362614008239047159831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126040483485344318729546441 94530362614008239047159831)
              ·
                refine ⟨141795543921012358570739747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94530362614008239047159831 141795543921012358570739747)
                ·
                  refine ⟨212693315881518537856109621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141795543921012358570739747 212693315881518537856109621)
                  ·
                    refine ⟨19939998363892362924010277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 212693315881518537856109621 19939998363892362924010277)
                    ·
                      refine ⟨3738749693229818048251927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19939998363892362924010277 3738749693229818048251927)
                      ·
                        rfl

theorem cell23_7281189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_7281189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281189 prefixEnd_7281189 := by exact prefixLift 7281189
  have htrace : WordTrace (prefixWord ++ tailWord_7281189) baseStart_7281189 baseEnd_7281189 := by
    simpa [prefixWord, tailWord_7281189, baseEnd_7281189] using wordTrace_append hprefix tailTrace_7281189
  have hstable : (prefixWord ++ tailWord_7281189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281189).length < 2 ^ (prefixWord ++ tailWord_7281189).sum := by decide
  have hdescent : baseEnd_7281189 < baseStart_7281189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281210 : List Nat := [3, 1, 1, 1, 3, 4, 2, 2, 1, 3, 2]
def baseStart_7281210 : Nat := 118140960795 + 7281210 * 2 ^ 59
def prefixEnd_7281210 : Nat := 4983230072969 + 3 ^ 40 * 7281210 * 2
def baseEnd_7281210 : Nat := 3738760476323562466089331

theorem tailTrace_7281210 : CollatzResearch.WordTrace tailWord_7281210 prefixEnd_7281210 3738760476323562466089331 := by
  unfold tailWord_7281210
  simp only [CollatzResearch.WordTrace]
  refine ⟨66391886487856794127624271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177045030634284784340331389 66391886487856794127624271)
  ·
    refine ⟨99587829731785191191436407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66391886487856794127624271 99587829731785191191436407)
    ·
      refine ⟨149381744597677786787154611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99587829731785191191436407 149381744597677786787154611)
      ·
        refine ⟨224072616896516680180731917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149381744597677786787154611 224072616896516680180731917)
        ·
          refine ⟨84027231336193755067774469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224072616896516680180731917 84027231336193755067774469)
          ·
            refine ⟨15755105875536329075207713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84027231336193755067774469 15755105875536329075207713)
            ·
              refine ⟨11816329406652246806405785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15755105875536329075207713 11816329406652246806405785)
              ·
                refine ⟨8862247054989185104804339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11816329406652246806405785 8862247054989185104804339)
                ·
                  refine ⟨13293370582483777657206509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8862247054989185104804339 13293370582483777657206509)
                  ·
                    refine ⟨4985013968431416621452441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13293370582483777657206509 4985013968431416621452441)
                    ·
                      refine ⟨3738760476323562466089331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4985013968431416621452441 3738760476323562466089331)
                      ·
                        rfl

theorem cell23_7281210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 1, 3, 2].length) (baseStart_7281210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281210 prefixEnd_7281210 := by exact prefixLift 7281210
  have htrace : WordTrace (prefixWord ++ tailWord_7281210) baseStart_7281210 baseEnd_7281210 := by
    simpa [prefixWord, tailWord_7281210, baseEnd_7281210] using wordTrace_append hprefix tailTrace_7281210
  have hstable : (prefixWord ++ tailWord_7281210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281210).length < 2 ^ (prefixWord ++ tailWord_7281210).sum := by decide
  have hdescent : baseEnd_7281210 < baseStart_7281210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281219 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 4]
def baseStart_7281219 : Nat := 118140960795 + 7281219 * 2 ^ 59
def prefixEnd_7281219 : Nat := 4983230072969 + 3 ^ 40 * 7281219 * 2
def baseEnd_7281219 : Nat := 3738765097649452930876789

theorem tailTrace_7281219 : CollatzResearch.WordTrace tailWord_7281219 prefixEnd_7281219 3738765097649452930876789 := by
  unfold tailWord_7281219
  simp only [CollatzResearch.WordTrace]
  refine ⟨265567874208394571047574711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177045249472263047365049807 265567874208394571047574711)
  ·
    refine ⟨398351811312591856571362067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265567874208394571047574711 398351811312591856571362067)
    ·
      refine ⟨597527716968887784857043101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398351811312591856571362067 597527716968887784857043101)
      ·
        refine ⟨224072893863332919321391163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 597527716968887784857043101 224072893863332919321391163)
        ·
          refine ⟨336109340794999378982086745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224072893863332919321391163 336109340794999378982086745)
          ·
            refine ⟨252082005596249534236565059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336109340794999378982086745 252082005596249534236565059)
            ·
              refine ⟨378123008394374301354847589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252082005596249534236565059 378123008394374301354847589)
              ·
                refine ⟨70898064073945181504033923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 378123008394374301354847589 70898064073945181504033923)
                ·
                  refine ⟨106347096110917772256050885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70898064073945181504033923 106347096110917772256050885)
                  ·
                    refine ⟨19940080520797082298009541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106347096110917772256050885 19940080520797082298009541)
                    ·
                      refine ⟨3738765097649452930876789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19940080520797082298009541 3738765097649452930876789)
                      ·
                        rfl

theorem cell23_7281219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_7281219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281219 prefixEnd_7281219 := by exact prefixLift 7281219
  have htrace : WordTrace (prefixWord ++ tailWord_7281219) baseStart_7281219 baseEnd_7281219 := by
    simpa [prefixWord, tailWord_7281219, baseEnd_7281219] using wordTrace_append hprefix tailTrace_7281219
  have hstable : (prefixWord ++ tailWord_7281219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281219).length < 2 ^ (prefixWord ++ tailWord_7281219).sum := by decide
  have hdescent : baseEnd_7281219 < baseStart_7281219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281226 : List Nat := [3, 1, 2, 1, 1, 5, 1, 1, 2, 1, 5]
def baseStart_7281226 : Nat := 118140960795 + 7281226 * 2 ^ 59
def prefixEnd_7281226 : Nat := 4983230072969 + 3 ^ 40 * 7281226 * 2
def baseEnd_7281226 : Nat := 3738768692014034403489257

theorem tailTrace_7281226 : CollatzResearch.WordTrace tailWord_7281226 prefixEnd_7281226 3738768692014034403489257 := by
  unfold tailWord_7281226
  simp only [CollatzResearch.WordTrace]
  refine ⟨66392032379842302810769883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177045419679579474162053021 66392032379842302810769883)
  ·
    refine ⟨99588048569763454216154825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66392032379842302810769883 99588048569763454216154825)
    ·
      refine ⟨74691036427322590662116119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99588048569763454216154825 74691036427322590662116119)
      ·
        refine ⟨112036554640983885993174179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74691036427322590662116119 112036554640983885993174179)
        ·
          refine ⟨168054831961475828989761269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112036554640983885993174179 168054831961475828989761269)
          ·
            refine ⟨15755140496388358967790119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 168054831961475828989761269 15755140496388358967790119)
            ·
              refine ⟨23632710744582538451685179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15755140496388358967790119 23632710744582538451685179)
              ·
                refine ⟨35449066116873807677527769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23632710744582538451685179 35449066116873807677527769)
                ·
                  refine ⟨26586799587655355758145827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35449066116873807677527769 26586799587655355758145827)
                  ·
                    refine ⟨39880199381483033637218741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26586799587655355758145827 39880199381483033637218741)
                    ·
                      refine ⟨3738768692014034403489257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39880199381483033637218741 3738768692014034403489257)
                      ·
                        rfl

theorem cell23_7281226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_7281226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281226 prefixEnd_7281226 := by exact prefixLift 7281226
  have htrace : WordTrace (prefixWord ++ tailWord_7281226) baseStart_7281226 baseEnd_7281226 := by
    simpa [prefixWord, tailWord_7281226, baseEnd_7281226] using wordTrace_append hprefix tailTrace_7281226
  have hstable : (prefixWord ++ tailWord_7281226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281226).length < 2 ^ (prefixWord ++ tailWord_7281226).sum := by decide
  have hdescent : baseEnd_7281226 < baseStart_7281226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281239 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 7]
def baseStart_7281239 : Nat := 118140960795 + 7281239 * 2 ^ 59
def prefixEnd_7281239 : Nat := 4983230072969 + 3 ^ 40 * 7281239 * 2
def baseEnd_7281239 : Nat := 3738775367262542852626697

theorem tailTrace_7281239 : CollatzResearch.WordTrace tailWord_7281239 prefixEnd_7281239 3738775367262542852626697 := by
  unfold tailWord_7281239
  simp only [CollatzResearch.WordTrace]
  refine ⟨265568603668322114463302771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177045735778881409642201847 265568603668322114463302771)
  ·
    refine ⟨398352905502483171694954157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265568603668322114463302771 398352905502483171694954157)
    ·
      refine ⟨149382339563431189385607809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 398352905502483171694954157 149382339563431189385607809)
      ·
        refine ⟨112036754672573392039205857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149382339563431189385607809 112036754672573392039205857)
        ·
          refine ⟨84027566004430044029404393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112036754672573392039205857 84027566004430044029404393)
          ·
            refine ⟨63020674503322533022053295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84027566004430044029404393 63020674503322533022053295)
            ·
              refine ⟨94531011754983799533079943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63020674503322533022053295 94531011754983799533079943)
              ·
                refine ⟨141796517632475699299619915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94531011754983799533079943 141796517632475699299619915)
                ·
                  refine ⟨212694776448713548949429873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141796517632475699299619915 212694776448713548949429873)
                  ·
                    refine ⟨159521082336535161712072405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 212694776448713548949429873 159521082336535161712072405)
                    ·
                      refine ⟨3738775367262542852626697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 159521082336535161712072405 3738775367262542852626697)
                      ·
                        rfl

theorem cell23_7281239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_7281239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281239 prefixEnd_7281239 := by exact prefixLift 7281239
  have htrace : WordTrace (prefixWord ++ tailWord_7281239) baseStart_7281239 baseEnd_7281239 := by
    simpa [prefixWord, tailWord_7281239, baseEnd_7281239] using wordTrace_append hprefix tailTrace_7281239
  have hstable : (prefixWord ++ tailWord_7281239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281239).length < 2 ^ (prefixWord ++ tailWord_7281239).sum := by decide
  have hdescent : baseEnd_7281239 < baseStart_7281239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281259 : List Nat := [1, 1, 1, 1, 2, 2, 1, 6, 1, 7]
def baseStart_7281259 : Nat := 118140960795 + 7281259 * 2 ^ 59
def prefixEnd_7281259 : Nat := 4983230072969 + 3 ^ 40 * 7281259 * 2
def baseEnd_7281259 : Nat := 1246261878958544258125535

theorem tailTrace_7281259 : CollatzResearch.WordTrace tailWord_7281259 prefixEnd_7281259 1246261878958544258125535 := by
  unfold tailWord_7281259
  simp only [CollatzResearch.WordTrace]
  refine ⟨265569333128249657879030831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177046222085499771919353887 265569333128249657879030831)
  ·
    refine ⟨398353999692374486818546247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265569333128249657879030831 398353999692374486818546247)
    ·
      refine ⟨597530999538561730227819371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398353999692374486818546247 597530999538561730227819371)
      ·
        refine ⟨896296499307842595341729057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597530999538561730227819371 896296499307842595341729057)
        ·
          refine ⟨672222374480881946506296793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 896296499307842595341729057 672222374480881946506296793)
          ·
            refine ⟨504166780860661459879722595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 672222374480881946506296793 504166780860661459879722595)
            ·
              refine ⟨756250171290992189819583893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504166780860661459879722595 756250171290992189819583893)
              ·
                refine ⟨35449226779265258897792995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 756250171290992189819583893 35449226779265258897792995)
                ·
                  refine ⟨53173840168897888346689493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35449226779265258897792995 53173840168897888346689493)
                  ·
                    refine ⟨1246261878958544258125535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53173840168897888346689493 1246261878958544258125535)
                    ·
                      rfl

theorem cell23_7281259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 7].length) (baseStart_7281259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281259 prefixEnd_7281259 := by exact prefixLift 7281259
  have htrace : WordTrace (prefixWord ++ tailWord_7281259) baseStart_7281259 baseEnd_7281259 := by
    simpa [prefixWord, tailWord_7281259, baseEnd_7281259] using wordTrace_append hprefix tailTrace_7281259
  have hstable : (prefixWord ++ tailWord_7281259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281259).length < 2 ^ (prefixWord ++ tailWord_7281259).sum := by decide
  have hdescent : baseEnd_7281259 < baseStart_7281259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281276 : List Nat := [2, 2, 2, 1, 1, 2, 3, 3, 2, 5]
def baseStart_7281276 : Nat := 118140960795 + 7281276 * 2 ^ 59
def prefixEnd_7281276 : Nat := 4983230072969 + 3 ^ 40 * 7281276 * 2
def baseEnd_7281276 : Nat := 1246264788682253069288009

theorem tailTrace_7281276 : CollatzResearch.WordTrace tailWord_7281276 prefixEnd_7281276 1246264788682253069288009 := by
  unfold tailWord_7281276
  simp only [CollatzResearch.WordTrace]
  refine ⟨132784976584594034891199841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177046635446125379854933121 132784976584594034891199841)
  ·
    refine ⟨99588732438445526168399881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132784976584594034891199841 99588732438445526168399881)
    ·
      refine ⟨74691549328834144626299911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99588732438445526168399881 74691549328834144626299911)
      ·
        refine ⟨112037323993251216939449867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74691549328834144626299911 112037323993251216939449867)
        ·
          refine ⟨168055985989876825409174801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112037323993251216939449867 168055985989876825409174801)
          ·
            refine ⟨126041989492407619056881101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168055985989876825409174801 126041989492407619056881101)
            ·
              refine ⟨47265746059652857146330413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126041989492407619056881101 47265746059652857146330413)
              ·
                refine ⟨17724654772369821429873905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47265746059652857146330413 17724654772369821429873905)
                ·
                  refine ⟨13293491079277366072405429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17724654772369821429873905 13293491079277366072405429)
                  ·
                    refine ⟨1246264788682253069288009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13293491079277366072405429 1246264788682253069288009)
                    ·
                      rfl

theorem cell23_7281276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_7281276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281276 prefixEnd_7281276 := by exact prefixLift 7281276
  have htrace : WordTrace (prefixWord ++ tailWord_7281276) baseStart_7281276 baseEnd_7281276 := by
    simpa [prefixWord, tailWord_7281276, baseEnd_7281276] using wordTrace_append hprefix tailTrace_7281276
  have hstable : (prefixWord ++ tailWord_7281276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281276).length < 2 ^ (prefixWord ++ tailWord_7281276).sum := by decide
  have hdescent : baseEnd_7281276 < baseStart_7281276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281300 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 2, 5, 2]
def baseStart_7281300 : Nat := 118140960795 + 7281300 * 2 ^ 59
def prefixEnd_7281300 : Nat := 4983230072969 + 3 ^ 40 * 7281300 * 2
def baseEnd_7281300 : Nat := 3738806689582467113963917

theorem tailTrace_7281300 : CollatzResearch.WordTrace tailWord_7281300 prefixEnd_7281300 3738806689582467113963917 := by
  unfold tailWord_7281300
  simp only [CollatzResearch.WordTrace]
  refine ⟨132785414260550560940636677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177047219014067414587515569 132785414260550560940636677)
  ·
    refine ⟨24897265173853230176369377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132785414260550560940636677 24897265173853230176369377)
    ·
      refine ⟨18672948880389922632277033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24897265173853230176369377 18672948880389922632277033)
      ·
        refine ⟨14004711660292441974207775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18672948880389922632277033 14004711660292441974207775)
        ·
          refine ⟨21007067490438662961311663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14004711660292441974207775 21007067490438662961311663)
          ·
            refine ⟨31510601235657994441967495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21007067490438662961311663 31510601235657994441967495)
            ·
              refine ⟨47265901853486991662951243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31510601235657994441967495 47265901853486991662951243)
              ·
                refine ⟨70898852780230487494426865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47265901853486991662951243 70898852780230487494426865)
                ·
                  refine ⟨53174139585172865620820149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70898852780230487494426865 53174139585172865620820149)
                  ·
                    refine ⟨4985075586109956151951889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53174139585172865620820149 4985075586109956151951889)
                    ·
                      refine ⟨3738806689582467113963917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4985075586109956151951889 3738806689582467113963917)
                      ·
                        rfl

theorem cell23_7281300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_7281300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281300 prefixEnd_7281300 := by exact prefixLift 7281300
  have htrace : WordTrace (prefixWord ++ tailWord_7281300) baseStart_7281300 baseEnd_7281300 := by
    simpa [prefixWord, tailWord_7281300, baseEnd_7281300] using wordTrace_append hprefix tailTrace_7281300
  have hstable : (prefixWord ++ tailWord_7281300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281300).length < 2 ^ (prefixWord ++ tailWord_7281300).sum := by decide
  have hdescent : baseEnd_7281300 < baseStart_7281300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281380 : List Nat := [2, 3, 1, 1, 1, 4, 2, 2, 3, 1, 3]
def baseStart_7281380 : Nat := 118140960795 + 7281380 * 2 ^ 59
def prefixEnd_7281380 : Nat := 4983230072969 + 3 ^ 40 * 7281380 * 2
def baseEnd_7281380 : Nat := 3738847768034826800963549

theorem tailTrace_7281380 : CollatzResearch.WordTrace tailWord_7281380 prefixEnd_7281380 3738847768034826800963549 := by
  unfold tailWord_7281380
  simp only [CollatzResearch.WordTrace]
  refine ⟨132786873180405647772092797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177049164240540863696123729 132786873180405647772092797)
  ·
    refine ⟨49795077442652117914534799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132786873180405647772092797 49795077442652117914534799)
    ·
      refine ⟨74692616163978176871802199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49795077442652117914534799 74692616163978176871802199)
      ·
        refine ⟨112038924245967265307703299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74692616163978176871802199 112038924245967265307703299)
        ·
          refine ⟨168058386368950897961554949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112038924245967265307703299 168058386368950897961554949)
          ·
            refine ⟨31510947444178293367791553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168058386368950897961554949 31510947444178293367791553)
            ·
              refine ⟨23633210583133720025843665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31510947444178293367791553 23633210583133720025843665)
              ·
                refine ⟨17724907937350290019382749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23633210583133720025843665 17724907937350290019382749)
                ·
                  refine ⟨6646840476506358757268531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17724907937350290019382749 6646840476506358757268531)
                  ·
                    refine ⟨9970260714759538135902797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6646840476506358757268531 9970260714759538135902797)
                    ·
                      refine ⟨3738847768034826800963549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9970260714759538135902797 3738847768034826800963549)
                      ·
                        rfl

theorem cell23_7281380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_7281380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281380 prefixEnd_7281380 := by exact prefixLift 7281380
  have htrace : WordTrace (prefixWord ++ tailWord_7281380) baseStart_7281380 baseEnd_7281380 := by
    simpa [prefixWord, tailWord_7281380, baseEnd_7281380] using wordTrace_append hprefix tailTrace_7281380
  have hstable : (prefixWord ++ tailWord_7281380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281380).length < 2 ^ (prefixWord ++ tailWord_7281380).sum := by decide
  have hdescent : baseEnd_7281380 < baseStart_7281380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281390 : List Nat := [4, 1, 2, 1, 1, 3, 2, 1, 1, 5, 2]
def baseStart_7281390 : Nat := 118140960795 + 7281390 * 2 ^ 59
def prefixEnd_7281390 : Nat := 4983230072969 + 3 ^ 40 * 7281390 * 2
def baseEnd_7281390 : Nat := 3738852902841371761838503

theorem tailTrace_7281390 : CollatzResearch.WordTrace tailWord_7281390 prefixEnd_7281390 3738852902841371761838503 := by
  unfold tailWord_7281390
  simp only [CollatzResearch.WordTrace]
  refine ⟨33196763886346883406506203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177049407393850044834699749 33196763886346883406506203)
  ·
    refine ⟨49795145829520325109759305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33196763886346883406506203 49795145829520325109759305)
    ·
      refine ⟨37346359372140243832319479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49795145829520325109759305 37346359372140243832319479)
      ·
        refine ⟨56019539058210365748479219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37346359372140243832319479 56019539058210365748479219)
        ·
          refine ⟨84029308587315548622718829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56019539058210365748479219 84029308587315548622718829)
          ·
            refine ⟨31510990720243330733519561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84029308587315548622718829 31510990720243330733519561)
            ·
              refine ⟨23633243040182498050139671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31510990720243330733519561 23633243040182498050139671)
              ·
                refine ⟨35449864560273747075209507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23633243040182498050139671 35449864560273747075209507)
                ·
                  refine ⟨53174796840410620612814261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35449864560273747075209507 53174796840410620612814261)
                  ·
                    refine ⟨4985137203788495682451337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53174796840410620612814261 4985137203788495682451337)
                    ·
                      refine ⟨3738852902841371761838503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4985137203788495682451337 3738852902841371761838503)
                      ·
                        rfl

theorem cell23_7281390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_7281390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281390 prefixEnd_7281390 := by exact prefixLift 7281390
  have htrace : WordTrace (prefixWord ++ tailWord_7281390) baseStart_7281390 baseEnd_7281390 := by
    simpa [prefixWord, tailWord_7281390, baseEnd_7281390] using wordTrace_append hprefix tailTrace_7281390
  have hstable : (prefixWord ++ tailWord_7281390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281390).length < 2 ^ (prefixWord ++ tailWord_7281390).sum := by decide
  have hdescent : baseEnd_7281390 < baseStart_7281390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281423 : List Nat := [1, 1, 2, 1, 1, 1, 6, 2, 3, 2, 3]
def baseStart_7281423 : Nat := 118140960795 + 7281423 * 2 ^ 59
def prefixEnd_7281423 : Nat := 4983230072969 + 3 ^ 40 * 7281423 * 2
def baseEnd_7281423 : Nat := 3738869847702970132725851

theorem tailTrace_7281423 : CollatzResearch.WordTrace tailWord_7281423 prefixEnd_7281423 3738869847702970132725851 := by
  unfold tailWord_7281423
  simp only [CollatzResearch.WordTrace]
  refine ⟨265575314699655513888000923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177050209799770342592000615 265575314699655513888000923)
  ·
    refine ⟨398362972049483270832001385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265575314699655513888000923 398362972049483270832001385)
    ·
      refine ⟨298772229037112453124001039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398362972049483270832001385 298772229037112453124001039)
      ·
        refine ⟨448158343555668679686001559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298772229037112453124001039 448158343555668679686001559)
        ·
          refine ⟨672237515333503019529002339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448158343555668679686001559 672237515333503019529002339)
          ·
            refine ⟨1008356273000254529293503509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 672237515333503019529002339 1008356273000254529293503509)
            ·
              refine ⟨47266700296886931060632977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1008356273000254529293503509 47266700296886931060632977)
              ·
                refine ⟨35450025222665198295474733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47266700296886931060632977 35450025222665198295474733)
                ·
                  refine ⟨13293759458499449360803025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35450025222665198295474733 13293759458499449360803025)
                  ·
                    refine ⟨9970319593874587020602269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13293759458499449360803025 9970319593874587020602269)
                    ·
                      refine ⟨3738869847702970132725851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9970319593874587020602269 3738869847702970132725851)
                      ·
                        rfl

theorem cell23_7281423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 2, 3].length) (baseStart_7281423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281423 prefixEnd_7281423 := by exact prefixLift 7281423
  have htrace : WordTrace (prefixWord ++ tailWord_7281423) baseStart_7281423 baseEnd_7281423 := by
    simpa [prefixWord, tailWord_7281423, baseEnd_7281423] using wordTrace_append hprefix tailTrace_7281423
  have hstable : (prefixWord ++ tailWord_7281423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281423).length < 2 ^ (prefixWord ++ tailWord_7281423).sum := by decide
  have hdescent : baseEnd_7281423 < baseStart_7281423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281437 : List Nat := [1, 4, 2, 4, 1, 1, 1, 1, 3, 1, 4]
def baseStart_7281437 : Nat := 118140960795 + 7281437 * 2 ^ 59
def prefixEnd_7281437 : Nat := 4983230072969 + 3 ^ 40 * 7281437 * 2
def baseEnd_7281437 : Nat := 3738877036432133077950787

theorem tailTrace_7281437 : CollatzResearch.WordTrace tailWord_7281437 prefixEnd_7281437 3738877036432133077950787 := by
  unfold tailWord_7281437
  simp only [CollatzResearch.WordTrace]
  refine ⟨265575825321604794279010565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177050550214403196186007043 265575825321604794279010565)
  ·
    refine ⟨49795467247800898927314481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265575825321604794279010565 49795467247800898927314481)
    ·
      refine ⟨37346600435850674195485861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49795467247800898927314481 37346600435850674195485861)
      ·
        refine ⟨7002487581722001411653599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37346600435850674195485861 7002487581722001411653599)
        ·
          refine ⟨10503731372583002117480399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7002487581722001411653599 10503731372583002117480399)
          ·
            refine ⟨15755597058874503176220599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10503731372583002117480399 15755597058874503176220599)
            ·
              refine ⟨23633395588311754764330899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15755597058874503176220599 23633395588311754764330899)
              ·
                refine ⟨35450093382467632146496349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23633395588311754764330899 35450093382467632146496349)
                ·
                  refine ⟨13293785018425362054936131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35450093382467632146496349 13293785018425362054936131)
                  ·
                    refine ⟨19940677527638043082404197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13293785018425362054936131 19940677527638043082404197)
                    ·
                      refine ⟨3738877036432133077950787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19940677527638043082404197 3738877036432133077950787)
                      ·
                        rfl

theorem cell23_7281437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_7281437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281437 prefixEnd_7281437 := by exact prefixLift 7281437
  have htrace : WordTrace (prefixWord ++ tailWord_7281437) baseStart_7281437 baseEnd_7281437 := by
    simpa [prefixWord, tailWord_7281437, baseEnd_7281437] using wordTrace_append hprefix tailTrace_7281437
  have hstable : (prefixWord ++ tailWord_7281437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281437).length < 2 ^ (prefixWord ++ tailWord_7281437).sum := by decide
  have hdescent : baseEnd_7281437 < baseStart_7281437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281440 : List Nat := [2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 3]
def baseStart_7281440 : Nat := 118140960795 + 7281440 * 2 ^ 59
def prefixEnd_7281440 : Nat := 4983230072969 + 3 ^ 40 * 7281440 * 2
def baseEnd_7281440 : Nat := 3738878576874096566213273

theorem tailTrace_7281440 : CollatzResearch.WordTrace tailWord_7281440 prefixEnd_7281440 3738878576874096566213273 := by
  unfold tailWord_7281440
  simp only [CollatzResearch.WordTrace]
  refine ⟨132787967370296962895684887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177050623160395950527579849 132787967370296962895684887)
  ·
    refine ⟨199181951055445444343527331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132787967370296962895684887 199181951055445444343527331)
    ·
      refine ⟨298772926583168166515290997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199181951055445444343527331 298772926583168166515290997)
      ·
        refine ⟨28009961867172015610808531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 298772926583168166515290997 28009961867172015610808531)
        ·
          refine ⟨42014942800758023416212797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28009961867172015610808531 42014942800758023416212797)
          ·
            refine ⟨15755603550284258781079799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42014942800758023416212797 15755603550284258781079799)
            ·
              refine ⟨23633405325426388171619699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15755603550284258781079799 23633405325426388171619699)
              ·
                refine ⟨35450107988139582257429549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23633405325426388171619699 35450107988139582257429549)
                ·
                  refine ⟨13293790495552343346536081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35450107988139582257429549 13293790495552343346536081)
                  ·
                    refine ⟨9970342871664257509902061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13293790495552343346536081 9970342871664257509902061)
                    ·
                      refine ⟨3738878576874096566213273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9970342871664257509902061 3738878576874096566213273)
                      ·
                        rfl

theorem cell23_7281440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_7281440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281440 prefixEnd_7281440 := by exact prefixLift 7281440
  have htrace : WordTrace (prefixWord ++ tailWord_7281440) baseStart_7281440 baseEnd_7281440 := by
    simpa [prefixWord, tailWord_7281440, baseEnd_7281440] using wordTrace_append hprefix tailTrace_7281440
  have hstable : (prefixWord ++ tailWord_7281440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281440).length < 2 ^ (prefixWord ++ tailWord_7281440).sum := by decide
  have hdescent : baseEnd_7281440 < baseStart_7281440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281454 : List Nat := [4, 1, 3, 2, 1, 2, 3, 1, 1, 1, 4]
def baseStart_7281454 : Nat := 118140960795 + 7281454 * 2 ^ 59
def prefixEnd_7281454 : Nat := 4983230072969 + 3 ^ 40 * 7281454 * 2
def baseEnd_7281454 : Nat := 3738885765603259511438209

theorem tailTrace_7281454 : CollatzResearch.WordTrace tailWord_7281454 prefixEnd_7281454 3738885765603259511438209 := by
  unfold tailWord_7281454
  simp only [CollatzResearch.WordTrace]
  refine ⟨33197055670317900772797427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177050963575028804121586277 33197055670317900772797427)
  ·
    refine ⟨49795583505476851159196141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33197055670317900772797427 49795583505476851159196141)
    ·
      refine ⟨18673343814553819184698553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49795583505476851159196141 18673343814553819184698553)
      ·
        refine ⟨14005007860915364388523915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18673343814553819184698553 14005007860915364388523915)
        ·
          refine ⟨21007511791373046582785873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14005007860915364388523915 21007511791373046582785873)
          ·
            refine ⟨15755633843529784937089405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21007511791373046582785873 15755633843529784937089405)
            ·
              refine ⟨5908362691323669351408527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15755633843529784937089405 5908362691323669351408527)
              ·
                refine ⟨8862544036985504027112791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5908362691323669351408527 8862544036985504027112791)
                ·
                  refine ⟨13293816055478256040669187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8862544036985504027112791 13293816055478256040669187)
                  ·
                    refine ⟨19940724083217384061003781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13293816055478256040669187 19940724083217384061003781)
                    ·
                      refine ⟨3738885765603259511438209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19940724083217384061003781 3738885765603259511438209)
                      ·
                        rfl

theorem cell23_7281454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_7281454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281454 prefixEnd_7281454 := by exact prefixLift 7281454
  have htrace : WordTrace (prefixWord ++ tailWord_7281454) baseStart_7281454 baseEnd_7281454 := by
    simpa [prefixWord, tailWord_7281454, baseEnd_7281454] using wordTrace_append hprefix tailTrace_7281454
  have hstable : (prefixWord ++ tailWord_7281454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281454).length < 2 ^ (prefixWord ++ tailWord_7281454).sum := by decide
  have hdescent : baseEnd_7281454 < baseStart_7281454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281456 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 4, 7]
def baseStart_7281456 : Nat := 118140960795 + 7281456 * 2 ^ 59
def prefixEnd_7281456 : Nat := 4983230072969 + 3 ^ 40 * 7281456 * 2
def baseEnd_7281456 : Nat := 1246295597521522834537733

theorem tailTrace_7281456 : CollatzResearch.WordTrace tailWord_7281456 prefixEnd_7281456 1246295597521522834537733 := by
  unfold tailWord_7281456
  simp only [CollatzResearch.WordTrace]
  refine ⟨132788259154267980261976111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177051012205690640349301481 132788259154267980261976111)
  ·
    refine ⟨199182388731401970392964167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132788259154267980261976111 199182388731401970392964167)
    ·
      refine ⟨298773583097102955589446251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199182388731401970392964167 298773583097102955589446251)
      ·
        refine ⟨448160374645654433384169377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298773583097102955589446251 448160374645654433384169377)
        ·
          refine ⟨336120280984240825038127033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448160374645654433384169377 336120280984240825038127033)
          ·
            refine ⟨252090210738180618778595275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336120280984240825038127033 252090210738180618778595275)
            ·
              refine ⟨378135316107270928167892913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252090210738180618778595275 378135316107270928167892913)
              ·
                refine ⟨283601487080453196125919685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 378135316107270928167892913 283601487080453196125919685)
                ·
                  refine ⟨53175278827584974273609941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 283601487080453196125919685 53175278827584974273609941)
                  ·
                    refine ⟨1246295597521522834537733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53175278827584974273609941 1246295597521522834537733)
                    ·
                      rfl

theorem cell23_7281456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 4, 7].length) (baseStart_7281456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281456 prefixEnd_7281456 := by exact prefixLift 7281456
  have htrace : WordTrace (prefixWord ++ tailWord_7281456) baseStart_7281456 baseEnd_7281456 := by
    simpa [prefixWord, tailWord_7281456, baseEnd_7281456] using wordTrace_append hprefix tailTrace_7281456
  have hstable : (prefixWord ++ tailWord_7281456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281456).length < 2 ^ (prefixWord ++ tailWord_7281456).sum := by decide
  have hdescent : baseEnd_7281456 < baseStart_7281456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281457 : List Nat := [1, 2, 2, 3, 2, 1, 5, 1, 1, 2, 3]
def baseStart_7281457 : Nat := 118140960795 + 7281457 * 2 ^ 59
def prefixEnd_7281457 : Nat := 4983230072969 + 3 ^ 40 * 7281457 * 2
def baseEnd_7281457 : Nat := 3738887306045222999700695

theorem tailTrace_7281457 : CollatzResearch.WordTrace tailWord_7281457 prefixEnd_7281457 3738887306045222999700695 := by
  unfold tailWord_7281457
  simp only [CollatzResearch.WordTrace]
  refine ⟨265576554781532337694738625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177051036521021558463159083 265576554781532337694738625)
  ·
    refine ⟨199182416086149253271053969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265576554781532337694738625 199182416086149253271053969)
    ·
      refine ⟨149386812064611939953290477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199182416086149253271053969 149386812064611939953290477)
      ·
        refine ⟨56020054524229477482483929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149386812064611939953290477 56020054524229477482483929)
        ·
          refine ⟨42015040893172108111862947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56020054524229477482483929 42015040893172108111862947)
          ·
            refine ⟨63022561339758162167794421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42015040893172108111862947 63022561339758162167794421)
            ·
              refine ⟨5908365125602327703230727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63022561339758162167794421 5908365125602327703230727)
              ·
                refine ⟨8862547688403491554846091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5908365125602327703230727 8862547688403491554846091)
                ·
                  refine ⟨13293821532605237332269137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8862547688403491554846091 13293821532605237332269137)
                  ·
                    refine ⟨9970366149453927999201853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13293821532605237332269137 9970366149453927999201853)
                    ·
                      refine ⟨3738887306045222999700695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9970366149453927999201853 3738887306045222999700695)
                      ·
                        rfl

theorem cell23_7281457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_7281457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281457 prefixEnd_7281457 := by exact prefixLift 7281457
  have htrace : WordTrace (prefixWord ++ tailWord_7281457) baseStart_7281457 baseEnd_7281457 := by
    simpa [prefixWord, tailWord_7281457, baseEnd_7281457] using wordTrace_append hprefix tailTrace_7281457
  have hstable : (prefixWord ++ tailWord_7281457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281457).length < 2 ^ (prefixWord ++ tailWord_7281457).sum := by decide
  have hdescent : baseEnd_7281457 < baseStart_7281457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281460 : List Nat := [2, 5, 1, 1, 4, 10]
def baseStart_7281460 : Nat := 118140960795 + 7281460 * 2 ^ 59
def prefixEnd_7281460 : Nat := 4983230072969 + 3 ^ 40 * 7281460 * 2
def baseEnd_7281460 : Nat := 15386373853856734518367

theorem tailTrace_7281460 : CollatzResearch.WordTrace tailWord_7281460 prefixEnd_7281460 15386373853856734518367 := by
  unfold tailWord_7281460
  simp only [CollatzResearch.WordTrace]
  refine ⟨132788332100260734603548917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177051109467014312804731889 132788332100260734603548917)
  ·
    refine ⟨12448906134399443869082711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132788332100260734603548917 12448906134399443869082711)
    ·
      refine ⟨18673359201599165803624067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12448906134399443869082711 18673359201599165803624067)
      ·
        refine ⟨28010038802398748705436101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18673359201599165803624067 28010038802398748705436101)
        ·
          refine ⟨5251882275449765382269269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28010038802398748705436101 5251882275449765382269269)
          ·
            refine ⟨15386373853856734518367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5251882275449765382269269 15386373853856734518367)
            ·
              rfl

theorem cell23_7281460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 10].length) (baseStart_7281460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281460 prefixEnd_7281460 := by exact prefixLift 7281460
  have htrace : WordTrace (prefixWord ++ tailWord_7281460) baseStart_7281460 baseEnd_7281460 := by
    simpa [prefixWord, tailWord_7281460, baseEnd_7281460] using wordTrace_append hprefix tailTrace_7281460
  have hstable : (prefixWord ++ tailWord_7281460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281460).length < 2 ^ (prefixWord ++ tailWord_7281460).sum := by decide
  have hdescent : baseEnd_7281460 < baseStart_7281460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281471 : List Nat := [1, 1, 2, 2, 5, 1, 4, 2, 1, 2, 2]
def baseStart_7281471 : Nat := 118140960795 + 7281471 * 2 ^ 59
def prefixEnd_7281471 : Nat := 4983230072969 + 3 ^ 40 * 7281471 * 2
def baseEnd_7281471 : Nat := 3738894494774385944925631

theorem tailTrace_7281471 : CollatzResearch.WordTrace tailWord_7281471 prefixEnd_7281471 3738894494774385944925631 := by
  unfold tailWord_7281471
  simp only [CollatzResearch.WordTrace]
  refine ⟨265577065403481618085748267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177051376935654412057165511 265577065403481618085748267)
  ·
    refine ⟨398365598105222427128622401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265577065403481618085748267 398365598105222427128622401)
    ·
      refine ⟨298774198578916820346466801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398365598105222427128622401 298774198578916820346466801)
      ·
        refine ⟨224080648934187615259850101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298774198578916820346466801 224080648934187615259850101)
        ·
          refine ⟨21007560837580088930610947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 224080648934187615259850101 21007560837580088930610947)
          ·
            refine ⟨31511341256370133395916421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21007560837580088930610947 31511341256370133395916421)
            ·
              refine ⟨5908376485569400011734329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31511341256370133395916421 5908376485569400011734329)
              ·
                refine ⟨4431282364177050008800747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5908376485569400011734329 4431282364177050008800747)
                ·
                  refine ⟨6646923546265575013201121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4431282364177050008800747 6646923546265575013201121)
                  ·
                    refine ⟨4985192659699181259900841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6646923546265575013201121 4985192659699181259900841)
                    ·
                      refine ⟨3738894494774385944925631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4985192659699181259900841 3738894494774385944925631)
                      ·
                        rfl

theorem cell23_7281471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 2, 1, 2, 2].length) (baseStart_7281471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281471 prefixEnd_7281471 := by exact prefixLift 7281471
  have htrace : WordTrace (prefixWord ++ tailWord_7281471) baseStart_7281471 baseEnd_7281471 := by
    simpa [prefixWord, tailWord_7281471, baseEnd_7281471] using wordTrace_append hprefix tailTrace_7281471
  have hstable : (prefixWord ++ tailWord_7281471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281471).length < 2 ^ (prefixWord ++ tailWord_7281471).sum := by decide
  have hdescent : baseEnd_7281471 < baseStart_7281471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281480 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 5, 3, 2]
def baseStart_7281480 : Nat := 118140960795 + 7281480 * 2 ^ 59
def prefixEnd_7281480 : Nat := 4983230072969 + 3 ^ 40 * 7281480 * 2
def baseEnd_7281480 : Nat := 3738899116100276409713089

theorem tailTrace_7281480 : CollatzResearch.WordTrace tailWord_7281480 prefixEnd_7281480 3738899116100276409713089 := by
  unfold tailWord_7281480
  simp only [CollatzResearch.WordTrace]
  refine ⟨132788696830224506311412947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177051595773632675081883929 132788696830224506311412947)
  ·
    refine ⟨199183045245336759467119421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132788696830224506311412947 199183045245336759467119421)
    ·
      refine ⟨74693641967001284800169783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199183045245336759467119421 74693641967001284800169783)
      ·
        refine ⟨112040462950501927200254675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74693641967001284800169783 112040462950501927200254675)
        ·
          refine ⟨168060694425752890800382013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112040462950501927200254675 168060694425752890800382013)
          ·
            refine ⟨63022760409657334050143255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168060694425752890800382013 63022760409657334050143255)
            ·
              refine ⟨94534140614486001075214883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63022760409657334050143255 94534140614486001075214883)
              ·
                refine ⟨141801210921729001612822325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94534140614486001075214883 141801210921729001612822325)
                ·
                  refine ⟨13293863523912093901202093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141801210921729001612822325 13293863523912093901202093)
                  ·
                    refine ⟨4985198821467035212950785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13293863523912093901202093 4985198821467035212950785)
                    ·
                      refine ⟨3738899116100276409713089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4985198821467035212950785 3738899116100276409713089)
                      ·
                        rfl

theorem cell23_7281480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 5, 3, 2].length) (baseStart_7281480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281480 prefixEnd_7281480 := by exact prefixLift 7281480
  have htrace : WordTrace (prefixWord ++ tailWord_7281480) baseStart_7281480 baseEnd_7281480 := by
    simpa [prefixWord, tailWord_7281480, baseEnd_7281480] using wordTrace_append hprefix tailTrace_7281480
  have hstable : (prefixWord ++ tailWord_7281480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281480).length < 2 ^ (prefixWord ++ tailWord_7281480).sum := by decide
  have hdescent : baseEnd_7281480 < baseStart_7281480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281493 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 2, 3, 4]
def baseStart_7281493 : Nat := 118140960795 + 7281493 * 2 ^ 59
def prefixEnd_7281493 : Nat := 4983230072969 + 3 ^ 40 * 7281493 * 2
def baseEnd_7281493 : Nat := 3738905791348784858850529

theorem tailTrace_7281493 : CollatzResearch.WordTrace tailWord_7281493 prefixEnd_7281493 3738905791348784858850529 := by
  unfold tailWord_7281493
  simp only [CollatzResearch.WordTrace]
  refine ⟨265577867809401915843049133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177051911872934610562032755 265577867809401915843049133)
  ·
    refine ⟨99591700428525718441143425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265577867809401915843049133 99591700428525718441143425)
    ·
      refine ⟨74693775321394288830857569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99591700428525718441143425 74693775321394288830857569)
      ·
        refine ⟨56020331491045716623143177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74693775321394288830857569 56020331491045716623143177)
        ·
          refine ⟨42015248618284287467357383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56020331491045716623143177 42015248618284287467357383)
          ·
            refine ⟨63022872927426431201036075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42015248618284287467357383 63022872927426431201036075)
            ·
              refine ⟨94534309391139646801554113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63022872927426431201036075 94534309391139646801554113)
              ·
                refine ⟨70900732043354735101165585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94534309391139646801554113 70900732043354735101165585)
                ·
                  refine ⟨53175549032516051325874189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70900732043354735101165585 53175549032516051325874189)
                  ·
                    refine ⟨19940830887193519247202821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53175549032516051325874189 19940830887193519247202821)
                    ·
                      refine ⟨3738905791348784858850529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19940830887193519247202821 3738905791348784858850529)
                      ·
                        rfl

theorem cell23_7281493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_7281493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281493 prefixEnd_7281493 := by exact prefixLift 7281493
  have htrace : WordTrace (prefixWord ++ tailWord_7281493) baseStart_7281493 baseEnd_7281493 := by
    simpa [prefixWord, tailWord_7281493, baseEnd_7281493] using wordTrace_append hprefix tailTrace_7281493
  have hstable : (prefixWord ++ tailWord_7281493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281493).length < 2 ^ (prefixWord ++ tailWord_7281493).sum := by decide
  have hdescent : baseEnd_7281493 < baseStart_7281493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281523 : List Nat := [1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 4]
def baseStart_7281523 : Nat := 118140960795 + 7281523 * 2 ^ 59
def prefixEnd_7281523 : Nat := 4983230072969 + 3 ^ 40 * 7281523 * 2
def baseEnd_7281523 : Nat := 3738921195768419741475391

theorem tailTrace_7281523 : CollatzResearch.WordTrace tailWord_7281523 prefixEnd_7281523 3738921195768419741475391 := by
  unfold tailWord_7281523
  simp only [CollatzResearch.WordTrace]
  refine ⟨265578961999293230966641223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177052641332862153977760815 265578961999293230966641223)
  ·
    refine ⟨398368442998939846449961835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265578961999293230966641223 398368442998939846449961835)
    ·
      refine ⟨597552664498409769674942753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398368442998939846449961835 597552664498409769674942753)
      ·
        refine ⟨448164498373807327256207065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 597552664498409769674942753 448164498373807327256207065)
        ·
          refine ⟨336123373780355495442155299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448164498373807327256207065 336123373780355495442155299)
          ·
            refine ⟨504185060670533243163232949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336123373780355495442155299 504185060670533243163232949)
            ·
              refine ⟨47267349437862491546553089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 504185060670533243163232949 47267349437862491546553089)
              ·
                refine ⟨35450512078396868659914817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47267349437862491546553089 35450512078396868659914817)
                ·
                  refine ⟨26587884058797651494936113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35450512078396868659914817 26587884058797651494936113)
                  ·
                    refine ⟨19940913044098238621202085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26587884058797651494936113 19940913044098238621202085)
                    ·
                      refine ⟨3738921195768419741475391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19940913044098238621202085 3738921195768419741475391)
                      ·
                        rfl

theorem cell23_7281523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 4].length) (baseStart_7281523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281523 prefixEnd_7281523 := by exact prefixLift 7281523
  have htrace : WordTrace (prefixWord ++ tailWord_7281523) baseStart_7281523 baseEnd_7281523 := by
    simpa [prefixWord, tailWord_7281523, baseEnd_7281523] using wordTrace_append hprefix tailTrace_7281523
  have hstable : (prefixWord ++ tailWord_7281523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281523).length < 2 ^ (prefixWord ++ tailWord_7281523).sum := by decide
  have hdescent : baseEnd_7281523 < baseStart_7281523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281533 : List Nat := [1, 4, 1, 1, 2, 1, 3, 3, 7]
def baseStart_7281533 : Nat := 118140960795 + 7281533 * 2 ^ 59
def prefixEnd_7281533 : Nat := 4983230072969 + 3 ^ 40 * 7281533 * 2
def baseEnd_7281533 : Nat := 415436258952773855816705

theorem tailTrace_7281533 : CollatzResearch.WordTrace tailWord_7281533 prefixEnd_7281533 415436258952773855816705 := by
  unfold tailWord_7281533
  simp only [CollatzResearch.WordTrace]
  refine ⟨265579326729257002674505253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177052884486171335116336835 265579326729257002674505253)
  ·
    refine ⟨49796123761735688001469735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265579326729257002674505253 49796123761735688001469735)
    ·
      refine ⟨74694185642603532002204603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49796123761735688001469735 74694185642603532002204603)
      ·
        refine ⟨112041278463905298003306905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74694185642603532002204603 112041278463905298003306905)
        ·
          refine ⟨84030958847928973502480179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112041278463905298003306905 84030958847928973502480179)
          ·
            refine ⟨126046438271893460253720269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84030958847928973502480179 126046438271893460253720269)
            ·
              refine ⟨47267414351960047595145101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126046438271893460253720269 47267414351960047595145101)
              ·
                refine ⟨17725280381985017848179413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47267414351960047595145101 17725280381985017848179413)
                ·
                  refine ⟨415436258952773855816705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17725280381985017848179413 415436258952773855816705)
                  ·
                    rfl

theorem cell23_7281533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 7].length) (baseStart_7281533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281533 prefixEnd_7281533 := by exact prefixLift 7281533
  have htrace : WordTrace (prefixWord ++ tailWord_7281533) baseStart_7281533 baseEnd_7281533 := by
    simpa [prefixWord, tailWord_7281533, baseEnd_7281533] using wordTrace_append hprefix tailTrace_7281533
  have hstable : (prefixWord ++ tailWord_7281533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281533).length < 2 ^ (prefixWord ++ tailWord_7281533).sum := by decide
  have hdescent : baseEnd_7281533 < baseStart_7281533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281538 : List Nat := [3, 4, 2, 2, 2, 1, 1, 1, 1, 3, 3]
def baseStart_7281538 : Nat := 118140960795 + 7281538 * 2 ^ 59
def prefixEnd_7281538 : Nat := 4983230072969 + 3 ^ 40 * 7281538 * 2
def baseEnd_7281538 : Nat := 3738928897978237182787823

theorem tailTrace_7281538 : CollatzResearch.WordTrace tailWord_7281538 prefixEnd_7281538 3738928897978237182787823 := by
  unfold tailWord_7281538
  simp only [CollatzResearch.WordTrace]
  refine ⟨66394877273559722132109317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177053006062825925685624845 66394877273559722132109317)
  ·
    refine ⟨12449039488792447899770497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66394877273559722132109317 12449039488792447899770497)
    ·
      refine ⟨9336779616594335924827873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12449039488792447899770497 9336779616594335924827873)
      ·
        refine ⟨7002584712445751943620905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9336779616594335924827873 7002584712445751943620905)
        ·
          refine ⟨5251938534334313957715679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7002584712445751943620905 5251938534334313957715679)
          ·
            refine ⟨7877907801501470936573519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5251938534334313957715679 7877907801501470936573519)
            ·
              refine ⟨11816861702252206404860279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7877907801501470936573519 11816861702252206404860279)
              ·
                refine ⟨17725292553378309607290419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11816861702252206404860279 17725292553378309607290419)
                ·
                  refine ⟨26587938830067464410935629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17725292553378309607290419 26587938830067464410935629)
                  ·
                    refine ⟨9970477061275299154100861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26587938830067464410935629 9970477061275299154100861)
                    ·
                      refine ⟨3738928897978237182787823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9970477061275299154100861 3738928897978237182787823)
                      ·
                        rfl

theorem cell23_7281538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_7281538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281538 prefixEnd_7281538 := by exact prefixLift 7281538
  have htrace : WordTrace (prefixWord ++ tailWord_7281538) baseStart_7281538 baseEnd_7281538 := by
    simpa [prefixWord, tailWord_7281538, baseEnd_7281538] using wordTrace_append hprefix tailTrace_7281538
  have hstable : (prefixWord ++ tailWord_7281538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281538).length < 2 ^ (prefixWord ++ tailWord_7281538).sum := by decide
  have hdescent : baseEnd_7281538 < baseStart_7281538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281544 : List Nat := [2, 1, 3, 3, 2, 3, 1, 1, 1, 4, 2]
def baseStart_7281544 : Nat := 118140960795 + 7281544 * 2 ^ 59
def prefixEnd_7281544 : Nat := 4983230072969 + 3 ^ 40 * 7281544 * 2
def baseEnd_7281544 : Nat := 3738931978862164159312795

theorem tailTrace_7281544 : CollatzResearch.WordTrace tailWord_7281544 prefixEnd_7281544 3738931978862164159312795 := by
  unfold tailWord_7281544
  simp only [CollatzResearch.WordTrace]
  refine ⟨132789863966108575776577843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177053151954811434368770457 132789863966108575776577843)
  ·
    refine ⟨199184795949162863664866765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132789863966108575776577843 199184795949162863664866765)
    ·
      refine ⟨74694298480936073874325037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199184795949162863664866765 74694298480936073874325037)
      ·
        refine ⟨28010361930351027702871889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74694298480936073874325037 28010361930351027702871889)
        ·
          refine ⟨21007771447763270777153917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28010361930351027702871889 21007771447763270777153917)
          ·
            refine ⟨7877914292911226541432719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21007771447763270777153917 7877914292911226541432719)
            ·
              refine ⟨11816871439366839812149079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7877914292911226541432719 11816871439366839812149079)
              ·
                refine ⟨17725307159050259718223619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11816871439366839812149079 17725307159050259718223619)
                ·
                  refine ⟨26587960738575389577335429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17725307159050259718223619 26587960738575389577335429)
                  ·
                    refine ⟨4985242638482885545750393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26587960738575389577335429 4985242638482885545750393)
                    ·
                      refine ⟨3738931978862164159312795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4985242638482885545750393 3738931978862164159312795)
                      ·
                        rfl

theorem cell23_7281544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_7281544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281544 prefixEnd_7281544 := by exact prefixLift 7281544
  have htrace : WordTrace (prefixWord ++ tailWord_7281544) baseStart_7281544 baseEnd_7281544 := by
    simpa [prefixWord, tailWord_7281544, baseEnd_7281544] using wordTrace_append hprefix tailTrace_7281544
  have hstable : (prefixWord ++ tailWord_7281544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281544).length < 2 ^ (prefixWord ++ tailWord_7281544).sum := by decide
  have hdescent : baseEnd_7281544 < baseStart_7281544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281567 : List Nat := [1, 1, 2, 5, 2, 1, 3, 3, 5]
def baseStart_7281567 : Nat := 118140960795 + 7281567 * 2 ^ 59
def prefixEnd_7281567 : Nat := 4983230072969 + 3 ^ 40 * 7281567 * 2
def baseEnd_7281567 : Nat := 415438198768579729925021

theorem tailTrace_7281567 : CollatzResearch.WordTrace tailWord_7281567 prefixEnd_7281567 415438198768579729925021 := by
  unfold tailWord_7281567
  simp only [CollatzResearch.WordTrace]
  refine ⟨265580566811133826481242955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177053711207422550987495303 265580566811133826481242955)
  ·
    refine ⟨398370850216700739721864433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265580566811133826481242955 398370850216700739721864433)
    ·
      refine ⟨298778137662525554791398325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398370850216700739721864433 298778137662525554791398325)
      ·
        refine ⟨28010450405861770761693593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 298778137662525554791398325 28010450405861770761693593)
        ·
          refine ⟨21007837804396328071270195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28010450405861770761693593 21007837804396328071270195)
          ·
            refine ⟨31511756706594492106905293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21007837804396328071270195 31511756706594492106905293)
            ·
              refine ⟨11816908764972934540089485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31511756706594492106905293 11816908764972934540089485)
              ·
                refine ⟨4431340786864850452533557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11816908764972934540089485 4431340786864850452533557)
                ·
                  refine ⟨415438198768579729925021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4431340786864850452533557 415438198768579729925021)
                  ·
                    rfl

theorem cell23_7281567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 3, 5].length) (baseStart_7281567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281567 prefixEnd_7281567 := by exact prefixLift 7281567
  have htrace : WordTrace (prefixWord ++ tailWord_7281567) baseStart_7281567 baseEnd_7281567 := by
    simpa [prefixWord, tailWord_7281567, baseEnd_7281567] using wordTrace_append hprefix tailTrace_7281567
  have hstable : (prefixWord ++ tailWord_7281567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281567).length < 2 ^ (prefixWord ++ tailWord_7281567).sum := by decide
  have hdescent : baseEnd_7281567 < baseStart_7281567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281583 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 4]
def baseStart_7281583 : Nat := 118140960795 + 7281583 * 2 ^ 59
def prefixEnd_7281583 : Nat := 4983230072969 + 3 ^ 40 * 7281583 * 2
def baseEnd_7281583 : Nat := 3738952004607689506725115

theorem tailTrace_7281583 : CollatzResearch.WordTrace tailWord_7281583 prefixEnd_7281583 3738952004607689506725115 := by
  unfold tailWord_7281583
  simp only [CollatzResearch.WordTrace]
  refine ⟨265581150379075861213825403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177054100252717240809216935 265581150379075861213825403)
  ·
    refine ⟨398371725568613791820738105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265581150379075861213825403 398371725568613791820738105)
    ·
      refine ⟨298778794176460343865553579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398371725568613791820738105 298778794176460343865553579)
      ·
        refine ⟨448168191264690515798330369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298778794176460343865553579 448168191264690515798330369)
        ·
          refine ⟨336126143448517886848747777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448168191264690515798330369 336126143448517886848747777)
          ·
            refine ⟨252094607586388415136560833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336126143448517886848747777 252094607586388415136560833)
            ·
              refine ⟨189070955689791311352420625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252094607586388415136560833 189070955689791311352420625)
              ·
                refine ⟨141803216767343483514315469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189070955689791311352420625 141803216767343483514315469)
                ·
                  refine ⟨53176206287753806317868301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141803216767343483514315469 53176206287753806317868301)
                  ·
                    refine ⟨19941077357907677369200613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53176206287753806317868301 19941077357907677369200613)
                    ·
                      refine ⟨3738952004607689506725115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19941077357907677369200613 3738952004607689506725115)
                      ·
                        rfl

theorem cell23_7281583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 4].length) (baseStart_7281583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281583 prefixEnd_7281583 := by exact prefixLift 7281583
  have htrace : WordTrace (prefixWord ++ tailWord_7281583) baseStart_7281583 baseEnd_7281583 := by
    simpa [prefixWord, tailWord_7281583, baseEnd_7281583] using wordTrace_append hprefix tailTrace_7281583
  have hstable : (prefixWord ++ tailWord_7281583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281583).length < 2 ^ (prefixWord ++ tailWord_7281583).sum := by decide
  have hdescent : baseEnd_7281583 < baseStart_7281583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281610 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 5, 4]
def baseStart_7281610 : Nat := 118140960795 + 7281610 * 2 ^ 59
def prefixEnd_7281610 : Nat := 4983230072969 + 3 ^ 40 * 7281610 * 2
def baseEnd_7281610 : Nat := 1246321956195120300362497

theorem tailTrace_7281610 : CollatzResearch.WordTrace tailWord_7281610 prefixEnd_7281610 1246321956195120300362497 := by
  unfold tailWord_7281610
  simp only [CollatzResearch.WordTrace]
  refine ⟨66395533787494511206264571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177054756766652029883372189 66395533787494511206264571)
  ·
    refine ⟨99593300681241766809396857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66395533787494511206264571 99593300681241766809396857)
    ·
      refine ⟨74694975510931325107047643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99593300681241766809396857 74694975510931325107047643)
      ·
        refine ⟨112042463266396987660571465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74694975510931325107047643 112042463266396987660571465)
        ·
          refine ⟨84031847449797740745428599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112042463266396987660571465 84031847449797740745428599)
          ·
            refine ⟨126047771174696611118142899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84031847449797740745428599 126047771174696611118142899)
            ·
              refine ⟨189071656762044916677214349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126047771174696611118142899 189071656762044916677214349)
              ·
                refine ⟨70901871285766843753955381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189071656762044916677214349 70901871285766843753955381)
                ·
                  refine ⟨6647050433040641601933317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70901871285766843753955381 6647050433040641601933317)
                  ·
                    refine ⟨1246321956195120300362497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6647050433040641601933317 1246321956195120300362497)
                    ·
                      rfl

theorem cell23_7281610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_7281610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281610 prefixEnd_7281610 := by exact prefixLift 7281610
  have htrace : WordTrace (prefixWord ++ tailWord_7281610) baseStart_7281610 baseEnd_7281610 := by
    simpa [prefixWord, tailWord_7281610, baseEnd_7281610] using wordTrace_append hprefix tailTrace_7281610
  have hstable : (prefixWord ++ tailWord_7281610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281610).length < 2 ^ (prefixWord ++ tailWord_7281610).sum := by decide
  have hdescent : baseEnd_7281610 < baseStart_7281610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281623 : List Nat := [1, 1, 3, 2, 1, 1, 2, 4, 8]
def baseStart_7281623 : Nat := 118140960795 + 7281623 * 2 ^ 59
def prefixEnd_7281623 : Nat := 4983230072969 + 3 ^ 40 * 7281623 * 2
def baseEnd_7281623 : Nat := 415441393759318816691659

theorem tailTrace_7281623 : CollatzResearch.WordTrace tailWord_7281623 prefixEnd_7281623 415441393759318816691659 := by
  unfold tailWord_7281623
  simp only [CollatzResearch.WordTrace]
  refine ⟨265582609298930948045281523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177055072865953965363521015 265582609298930948045281523)
  ·
    refine ⟨398373913948396422067922285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265582609298930948045281523 398373913948396422067922285)
    ·
      refine ⟨149390217730648658275470857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 398373913948396422067922285 149390217730648658275470857)
      ·
        refine ⟨112042663297986493706603143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149390217730648658275470857 112042663297986493706603143)
        ·
          refine ⟨168063994946979740559904715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112042663297986493706603143 168063994946979740559904715)
          ·
            refine ⟨252095992420469610839857073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168063994946979740559904715 252095992420469610839857073)
            ·
              refine ⟨189071994315352208129892805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252095992420469610839857073 189071994315352208129892805)
              ·
                refine ⟨35450998934128539024354901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189071994315352208129892805 35450998934128539024354901)
                ·
                  refine ⟨415441393759318816691659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35450998934128539024354901 415441393759318816691659)
                  ·
                    rfl

theorem cell23_7281623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 8].length) (baseStart_7281623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281623 prefixEnd_7281623 := by exact prefixLift 7281623
  have htrace : WordTrace (prefixWord ++ tailWord_7281623) baseStart_7281623 baseEnd_7281623 := by
    simpa [prefixWord, tailWord_7281623, baseEnd_7281623] using wordTrace_append hprefix tailTrace_7281623
  have hstable : (prefixWord ++ tailWord_7281623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281623).length < 2 ^ (prefixWord ++ tailWord_7281623).sum := by decide
  have hdescent : baseEnd_7281623 < baseStart_7281623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281634 : List Nat := [3, 3, 3, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_7281634 : Nat := 118140960795 + 7281634 * 2 ^ 59
def prefixEnd_7281634 : Nat := 4983230072969 + 3 ^ 40 * 7281634 * 2
def baseEnd_7281634 : Nat := 3738978192121068807187381

theorem tailTrace_7281634 : CollatzResearch.WordTrace tailWord_7281634 prefixEnd_7281634 3738978192121068807187381 := by
  unfold tailWord_7281634
  simp only [CollatzResearch.WordTrace]
  refine ⟨66395752625472774230982989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177055340334594064615954637 66395752625472774230982989)
  ·
    refine ⟨24898407234552290336618621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66395752625472774230982989 24898407234552290336618621)
    ·
      refine ⟨9336902712957108876231983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24898407234552290336618621 9336902712957108876231983)
      ·
        refine ⟨14005354069435663314347975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9336902712957108876231983 14005354069435663314347975)
        ·
          refine ⟨21008031104153494971521963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14005354069435663314347975 21008031104153494971521963)
          ·
            refine ⟨31512046656230242457282945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21008031104153494971521963 31512046656230242457282945)
            ·
              refine ⟨23634034992172681842962209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31512046656230242457282945 23634034992172681842962209)
              ·
                refine ⟨17725526244129511382221657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23634034992172681842962209 17725526244129511382221657)
                ·
                  refine ⟨13294144683097133536666243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17725526244129511382221657 13294144683097133536666243)
                  ·
                    refine ⟨19941217024645700304999365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13294144683097133536666243 19941217024645700304999365)
                    ·
                      refine ⟨3738978192121068807187381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19941217024645700304999365 3738978192121068807187381)
                      ·
                        rfl

theorem cell23_7281634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_7281634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281634 prefixEnd_7281634 := by exact prefixLift 7281634
  have htrace : WordTrace (prefixWord ++ tailWord_7281634) baseStart_7281634 baseEnd_7281634 := by
    simpa [prefixWord, tailWord_7281634, baseEnd_7281634] using wordTrace_append hprefix tailTrace_7281634
  have hstable : (prefixWord ++ tailWord_7281634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281634).length < 2 ^ (prefixWord ++ tailWord_7281634).sum := by decide
  have hdescent : baseEnd_7281634 < baseStart_7281634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281640 : List Nat := [2, 1, 4, 1, 1, 1, 3, 4, 6]
def baseStart_7281640 : Nat := 118140960795 + 7281640 * 2 ^ 59
def prefixEnd_7281640 : Nat := 4983230072969 + 3 ^ 40 * 7281640 * 2
def baseEnd_7281640 : Nat := 415442363667221753745817

theorem tailTrace_7281640 : CollatzResearch.WordTrace tailWord_7281640 prefixEnd_7281640 415442363667221753745817 := by
  unfold tailWord_7281640
  simp only [CollatzResearch.WordTrace]
  refine ⟨132791614669934679974325187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177055486226579573299100249 132791614669934679974325187)
  ·
    refine ⟨199187422004902019961487781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132791614669934679974325187 199187422004902019961487781)
    ·
      refine ⟨37347641625919128742778959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199187422004902019961487781 37347641625919128742778959)
      ·
        refine ⟨56021462438878693114168439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37347641625919128742778959 56021462438878693114168439)
        ·
          refine ⟨84032193658318039671252659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56021462438878693114168439 84032193658318039671252659)
          ·
            refine ⟨126048290487477059506878989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84032193658318039671252659 126048290487477059506878989)
            ·
              refine ⟨47268108932803897315079621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126048290487477059506878989 47268108932803897315079621)
              ·
                refine ⟨8862770424900730746577429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47268108932803897315079621 8862770424900730746577429)
                ·
                  refine ⟨415442363667221753745817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8862770424900730746577429 415442363667221753745817)
                  ·
                    rfl

theorem cell23_7281640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 6].length) (baseStart_7281640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281640 prefixEnd_7281640 := by exact prefixLift 7281640
  have htrace : WordTrace (prefixWord ++ tailWord_7281640) baseStart_7281640 baseEnd_7281640 := by
    simpa [prefixWord, tailWord_7281640, baseEnd_7281640] using wordTrace_append hprefix tailTrace_7281640
  have hstable : (prefixWord ++ tailWord_7281640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281640).length < 2 ^ (prefixWord ++ tailWord_7281640).sum := by decide
  have hdescent : baseEnd_7281640 < baseStart_7281640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281724 : List Nat := [2, 2, 2, 2, 2, 3, 2, 2, 1, 1, 4]
def baseStart_7281724 : Nat := 118140960795 + 7281724 * 2 ^ 59
def prefixEnd_7281724 : Nat := 4983230072969 + 3 ^ 40 * 7281724 * 2
def baseEnd_7281724 : Nat := 3739024405379973455061967

theorem tailTrace_7281724 : CollatzResearch.WordTrace tailWord_7281724 prefixEnd_7281724 3739024405379973455061967 := by
  unfold tailWord_7281724
  simp only [CollatzResearch.WordTrace]
  refine ⟨132793146535782521147354113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177057528714376694863138817 132793146535782521147354113)
  ·
    refine ⟨99594859901836890860515585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132793146535782521147354113 99594859901836890860515585)
    ·
      refine ⟨74696144926377668145386689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99594859901836890860515585 74696144926377668145386689)
      ·
        refine ⟨56022108694783251109040017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74696144926377668145386689 56022108694783251109040017)
        ·
          refine ⟨42016581521087438331780013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56022108694783251109040017 42016581521087438331780013)
          ·
            refine ⟨15756218070407789374417505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42016581521087438331780013 15756218070407789374417505)
            ·
              refine ⟨11817163552805842030813129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15756218070407789374417505 11817163552805842030813129)
              ·
                refine ⟨8862872664604381523109847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11817163552805842030813129 8862872664604381523109847)
                ·
                  refine ⟨13294308996906572284664771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8862872664604381523109847 13294308996906572284664771)
                  ·
                    refine ⟨19941463495359858426997157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13294308996906572284664771 19941463495359858426997157)
                    ·
                      refine ⟨3739024405379973455061967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19941463495359858426997157 3739024405379973455061967)
                      ·
                        rfl

theorem cell23_7281724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_7281724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281724 prefixEnd_7281724 := by exact prefixLift 7281724
  have htrace : WordTrace (prefixWord ++ tailWord_7281724) baseStart_7281724 baseEnd_7281724 := by
    simpa [prefixWord, tailWord_7281724, baseEnd_7281724] using wordTrace_append hprefix tailTrace_7281724
  have hstable : (prefixWord ++ tailWord_7281724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281724).length < 2 ^ (prefixWord ++ tailWord_7281724).sum := by decide
  have hdescent : baseEnd_7281724 < baseStart_7281724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281760 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 2, 7]
def baseStart_7281760 : Nat := 118140960795 + 7281760 * 2 ^ 59
def prefixEnd_7281760 : Nat := 4983230072969 + 3 ^ 40 * 7281760 * 2
def baseEnd_7281760 : Nat := 1246347630227845104737267

theorem tailTrace_7281760 : CollatzResearch.WordTrace tailWord_7281760 prefixEnd_7281760 1246347630227845104737267 := by
  unfold tailWord_7281760
  simp only [CollatzResearch.WordTrace]
  refine ⟨132793803049717310221509367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177058404066289746962012489 132793803049717310221509367)
  ·
    refine ⟨199190704574575965332264051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132793803049717310221509367 199190704574575965332264051)
    ·
      refine ⟨298786056861863947998396077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199190704574575965332264051 298786056861863947998396077)
      ·
        refine ⟨112044771323198980499398529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298786056861863947998396077 112044771323198980499398529)
        ·
          refine ⟨84033578492399235374548897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112044771323198980499398529 84033578492399235374548897)
          ·
            refine ⟨63025183869299426530911673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84033578492399235374548897 63025183869299426530911673)
            ·
              refine ⟨47268887901974569898183755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63025183869299426530911673 47268887901974569898183755)
              ·
                refine ⟨70903331852961854847275633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47268887901974569898183755 70903331852961854847275633)
                ·
                  refine ⟨53177498889721391135456725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70903331852961854847275633 53177498889721391135456725)
                  ·
                    refine ⟨1246347630227845104737267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53177498889721391135456725 1246347630227845104737267)
                    ·
                      rfl

theorem cell23_7281760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 2, 7].length) (baseStart_7281760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281760 prefixEnd_7281760 := by exact prefixLift 7281760
  have htrace : WordTrace (prefixWord ++ tailWord_7281760) baseStart_7281760 baseEnd_7281760 := by
    simpa [prefixWord, tailWord_7281760, baseEnd_7281760] using wordTrace_append hprefix tailTrace_7281760
  have hstable : (prefixWord ++ tailWord_7281760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281760).length < 2 ^ (prefixWord ++ tailWord_7281760).sum := by decide
  have hdescent : baseEnd_7281760 < baseStart_7281760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281831 : List Nat := [1, 1, 6, 2, 1, 1, 1, 3, 1, 4, 2]
def baseStart_7281831 : Nat := 118140960795 + 7281831 * 2 ^ 59
def prefixEnd_7281831 : Nat := 4983230072969 + 3 ^ 40 * 7281831 * 2
def baseEnd_7281831 : Nat := 3739079347810004536423975

theorem tailTrace_7281831 : CollatzResearch.WordTrace tailWord_7281831 prefixEnd_7281831 3739079347810004536423975 := by
  unfold tailWord_7281831
  simp only [CollatzResearch.WordTrace]
  refine ⟨265590195682177399568853347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177060130454784933045902231 265590195682177399568853347)
  ·
    refine ⟨398385293523266099353280021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265590195682177399568853347 398385293523266099353280021)
    ·
      refine ⟨18674310633903098407185001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 398385293523266099353280021 18674310633903098407185001)
      ·
        refine ⟨14005732975427323805388751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18674310633903098407185001 14005732975427323805388751)
        ·
          refine ⟨21008599463140985708083127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14005732975427323805388751 21008599463140985708083127)
          ·
            refine ⟨31512899194711478562124691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21008599463140985708083127 31512899194711478562124691)
            ·
              refine ⟨47269348792067217843187037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31512899194711478562124691 47269348792067217843187037)
              ·
                refine ⟨17726005797025206691195139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47269348792067217843187037 17726005797025206691195139)
                ·
                  refine ⟨26589008695537810036792709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17726005797025206691195139 26589008695537810036792709)
                  ·
                    refine ⟨4985439130413339381898633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26589008695537810036792709 4985439130413339381898633)
                    ·
                      refine ⟨3739079347810004536423975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4985439130413339381898633 3739079347810004536423975)
                      ·
                        rfl

theorem cell23_7281831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_7281831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281831 prefixEnd_7281831 := by exact prefixLift 7281831
  have htrace : WordTrace (prefixWord ++ tailWord_7281831) baseStart_7281831 baseEnd_7281831 := by
    simpa [prefixWord, tailWord_7281831, baseEnd_7281831] using wordTrace_append hprefix tailTrace_7281831
  have hstable : (prefixWord ++ tailWord_7281831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281831).length < 2 ^ (prefixWord ++ tailWord_7281831).sum := by decide
  have hdescent : baseEnd_7281831 < baseStart_7281831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281840 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 8]
def baseStart_7281840 : Nat := 118140960795 + 7281840 * 2 ^ 59
def prefixEnd_7281840 : Nat := 4983230072969 + 3 ^ 40 * 7281840 * 2
def baseEnd_7281840 : Nat := 3739083969135895001211433

theorem tailTrace_7281840 : CollatzResearch.WordTrace tailWord_7281840 prefixEnd_7281840 3739083969135895001211433 := by
  unfold tailWord_7281840
  simp only [CollatzResearch.WordTrace]
  refine ⟨132795261969572397052965487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177060349292763196070620649 132795261969572397052965487)
  ·
    refine ⟨199192892954358595579448231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132795261969572397052965487 199192892954358595579448231)
    ·
      refine ⟨298789339431537893369172347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199192892954358595579448231 298789339431537893369172347)
      ·
        refine ⟨448184009147306840053758521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298789339431537893369172347 448184009147306840053758521)
        ·
          refine ⟨336138006860480130040318891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448184009147306840053758521 336138006860480130040318891)
          ·
            refine ⟨504207010290720195060478337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336138006860480130040318891 504207010290720195060478337)
            ·
              refine ⟨378155257718040146295358753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 504207010290720195060478337 378155257718040146295358753)
              ·
                refine ⟨283616443288530109721519065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 378155257718040146295358753 283616443288530109721519065)
                ·
                  refine ⟨212712332466397582291139299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283616443288530109721519065 212712332466397582291139299)
                  ·
                    refine ⟨319068498699596373436708949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 212712332466397582291139299 319068498699596373436708949)
                    ·
                      refine ⟨3739083969135895001211433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 319068498699596373436708949 3739083969135895001211433)
                      ·
                        rfl

theorem cell23_7281840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 8].length) (baseStart_7281840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281840 prefixEnd_7281840 := by exact prefixLift 7281840
  have htrace : WordTrace (prefixWord ++ tailWord_7281840) baseStart_7281840 baseEnd_7281840 := by
    simpa [prefixWord, tailWord_7281840, baseEnd_7281840] using wordTrace_append hprefix tailTrace_7281840
  have hstable : (prefixWord ++ tailWord_7281840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281840).length < 2 ^ (prefixWord ++ tailWord_7281840).sum := by decide
  have hdescent : baseEnd_7281840 < baseStart_7281840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281847 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 1, 5, 3]
def baseStart_7281847 : Nat := 118140960795 + 7281847 * 2 ^ 59
def prefixEnd_7281847 : Nat := 4983230072969 + 3 ^ 40 * 7281847 * 2
def baseEnd_7281847 : Nat := 3739087563500476473823901

theorem tailTrace_7281847 : CollatzResearch.WordTrace tailWord_7281847 prefixEnd_7281847 3739087563500476473823901 := by
  unfold tailWord_7281847
  simp only [CollatzResearch.WordTrace]
  refine ⟨265590779250119434301435795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177060519500079622867623863 265590779250119434301435795)
  ·
    refine ⟨398386168875179151452153693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265590779250119434301435795 398386168875179151452153693)
    ·
      refine ⟨149394813328192181794557635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 398386168875179151452153693 149394813328192181794557635)
      ·
        refine ⟨224092219992288272691836453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149394813328192181794557635 224092219992288272691836453)
        ·
          refine ⟨42017291248554051129719335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224092219992288272691836453 42017291248554051129719335)
          ·
            refine ⟨63025936872831076694579003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42017291248554051129719335 63025936872831076694579003)
            ·
              refine ⟨94538905309246615041868505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63025936872831076694579003 94538905309246615041868505)
              ·
                refine ⟨70904178981934961281401379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94538905309246615041868505 70904178981934961281401379)
                ·
                  refine ⟨106356268472902441922102069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70904178981934961281401379 106356268472902441922102069)
                  ·
                    refine ⟨9970900169334603930197069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106356268472902441922102069 9970900169334603930197069)
                    ·
                      refine ⟨3739087563500476473823901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9970900169334603930197069 3739087563500476473823901)
                      ·
                        rfl

theorem cell23_7281847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 5, 3].length) (baseStart_7281847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281847 prefixEnd_7281847 := by exact prefixLift 7281847
  have htrace : WordTrace (prefixWord ++ tailWord_7281847) baseStart_7281847 baseEnd_7281847 := by
    simpa [prefixWord, tailWord_7281847, baseEnd_7281847] using wordTrace_append hprefix tailTrace_7281847
  have hstable : (prefixWord ++ tailWord_7281847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281847).length < 2 ^ (prefixWord ++ tailWord_7281847).sum := by decide
  have hdescent : baseEnd_7281847 < baseStart_7281847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281887 : List Nat := [1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 4]
def baseStart_7281887 : Nat := 118140960795 + 7281887 * 2 ^ 59
def prefixEnd_7281887 : Nat := 4983230072969 + 3 ^ 40 * 7281887 * 2
def baseEnd_7281887 : Nat := 3739108102726656317323717

theorem tailTrace_7281887 : CollatzResearch.WordTrace tailWord_7281887 prefixEnd_7281887 3739108102726656317323717 := by
  unfold tailWord_7281887
  simp only [CollatzResearch.WordTrace]
  refine ⟨265592238169974521132891915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177061492113316347421927943 265592238169974521132891915)
  ·
    refine ⟨398388357254961781699337873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265592238169974521132891915 398388357254961781699337873)
    ·
      refine ⟨298791267941221336274503405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398388357254961781699337873 298791267941221336274503405)
      ·
        refine ⟨112046725477958001102938777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298791267941221336274503405 112046725477958001102938777)
        ·
          refine ⟨84035044108468500827204083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112046725477958001102938777 84035044108468500827204083)
          ·
            refine ⟨126052566162702751240806125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84035044108468500827204083 126052566162702751240806125)
            ·
              refine ⟨47269712311013531715302297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126052566162702751240806125 47269712311013531715302297)
              ·
                refine ⟨35452284233260148786476723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47269712311013531715302297 35452284233260148786476723)
                ·
                  refine ⟨53178426349890223179715085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35452284233260148786476723 53178426349890223179715085)
                  ·
                    refine ⟨19941909881208833692393157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53178426349890223179715085 19941909881208833692393157)
                    ·
                      refine ⟨3739108102726656317323717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19941909881208833692393157 3739108102726656317323717)
                      ·
                        rfl

theorem cell23_7281887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_7281887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281887 prefixEnd_7281887 := by exact prefixLift 7281887
  have htrace : WordTrace (prefixWord ++ tailWord_7281887) baseStart_7281887 baseEnd_7281887 := by
    simpa [prefixWord, tailWord_7281887, baseEnd_7281887] using wordTrace_append hprefix tailTrace_7281887
  have hstable : (prefixWord ++ tailWord_7281887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281887).length < 2 ^ (prefixWord ++ tailWord_7281887).sum := by decide
  have hdescent : baseEnd_7281887 < baseStart_7281887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281931 : List Nat := [1, 1, 1, 1, 5, 5, 1, 1, 3, 4]
def baseStart_7281931 : Nat := 118140960795 + 7281931 * 2 ^ 59
def prefixEnd_7281931 : Nat := 4983230072969 + 3 ^ 40 * 7281931 * 2
def baseEnd_7281931 : Nat := 1246376898625151381724505

theorem tailTrace_7281931 : CollatzResearch.WordTrace tailWord_7281931 prefixEnd_7281931 1246376898625151381724505 := by
  unfold tailWord_7281931
  simp only [CollatzResearch.WordTrace]
  refine ⟨265593842981815116647493647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177062561987876744431662431 265593842981815116647493647)
  ·
    refine ⟨398390764472722674971240471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265593842981815116647493647 398390764472722674971240471)
    ·
      refine ⟨597586146709084012456860707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398390764472722674971240471 597586146709084012456860707)
      ·
        refine ⟨896379220063626018685291061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597586146709084012456860707 896379220063626018685291061)
        ·
          refine ⟨84035551880964939251746037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 896379220063626018685291061 84035551880964939251746037)
          ·
            refine ⟨7878332988840463054851191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84035551880964939251746037 7878332988840463054851191)
            ·
              refine ⟨11817499483260694582276787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7878332988840463054851191 11817499483260694582276787)
              ·
                refine ⟨17726249224891041873415181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11817499483260694582276787 17726249224891041873415181)
                ·
                  refine ⟨6647343459334140702530693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17726249224891041873415181 6647343459334140702530693)
                  ·
                    refine ⟨1246376898625151381724505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6647343459334140702530693 1246376898625151381724505)
                    ·
                      rfl

theorem cell23_7281931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 3, 4].length) (baseStart_7281931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281931 prefixEnd_7281931 := by exact prefixLift 7281931
  have htrace : WordTrace (prefixWord ++ tailWord_7281931) baseStart_7281931 baseEnd_7281931 := by
    simpa [prefixWord, tailWord_7281931, baseEnd_7281931] using wordTrace_append hprefix tailTrace_7281931
  have hstable : (prefixWord ++ tailWord_7281931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281931).length < 2 ^ (prefixWord ++ tailWord_7281931).sum := by decide
  have hdescent : baseEnd_7281931 < baseStart_7281931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281944 : List Nat := [2, 1, 2, 3, 1, 4, 1, 3, 6]
def baseStart_7281944 : Nat := 118140960795 + 7281944 * 2 ^ 59
def prefixEnd_7281944 : Nat := 4983230072969 + 3 ^ 40 * 7281944 * 2
def baseEnd_7281944 : Nat := 415459707902662510478995

theorem tailTrace_7281944 : CollatzResearch.WordTrace tailWord_7281944 prefixEnd_7281944 415459707902662510478995 := by
  unfold tailWord_7281944
  simp only [CollatzResearch.WordTrace]
  refine ⟨132797158565384009933858443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177062878087178679911811257 132797158565384009933858443)
  ·
    refine ⟨199195737848076014900787665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132797158565384009933858443 199195737848076014900787665)
    ·
      refine ⟨149396803386057011175590749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199195737848076014900787665 149396803386057011175590749)
      ·
        refine ⟨56023801269771379190846531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149396803386057011175590749 56023801269771379190846531)
        ·
          refine ⟨84035701904657068786269797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56023801269771379190846531 84035701904657068786269797)
          ·
            refine ⟨15756694107123200397425587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84035701904657068786269797 15756694107123200397425587)
            ·
              refine ⟨23635041160684800596138381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15756694107123200397425587 23635041160684800596138381)
              ·
                refine ⟨8863140435256800223551893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23635041160684800596138381 8863140435256800223551893)
                ·
                  refine ⟨415459707902662510478995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8863140435256800223551893 415459707902662510478995)
                  ·
                    rfl

theorem cell23_7281944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 6].length) (baseStart_7281944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281944 prefixEnd_7281944 := by exact prefixLift 7281944
  have htrace : WordTrace (prefixWord ++ tailWord_7281944) baseStart_7281944 baseEnd_7281944 := by
    simpa [prefixWord, tailWord_7281944, baseEnd_7281944] using wordTrace_append hprefix tailTrace_7281944
  have hstable : (prefixWord ++ tailWord_7281944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281944).length < 2 ^ (prefixWord ++ tailWord_7281944).sum := by decide
  have hdescent : baseEnd_7281944 < baseStart_7281944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7281987 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 5, 6]
def baseStart_7281987 : Nat := 118140960795 + 7281987 * 2 ^ 59
def prefixEnd_7281987 : Nat := 4983230072969 + 3 ^ 40 * 7281987 * 2
def baseEnd_7281987 : Nat := 1246386483597368642024419

theorem tailTrace_7281987 : CollatzResearch.WordTrace tailWord_7281987 prefixEnd_7281987 1246386483597368642024419 := by
  unfold tailWord_7281987
  simp only [CollatzResearch.WordTrace]
  refine ⟨265595885469612238211532215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177063923646408158807688143 265595885469612238211532215)
  ·
    refine ⟨398393828204418357317298323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265595885469612238211532215 398393828204418357317298323)
    ·
      refine ⟨597590742306627535975947485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398393828204418357317298323 597590742306627535975947485)
      ·
        refine ⟨224096528364985325990980307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 597590742306627535975947485 224096528364985325990980307)
        ·
          refine ⟨336144792547477988986470461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224096528364985325990980307 336144792547477988986470461)
          ·
            refine ⟨126054297205304245869926423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 336144792547477988986470461 126054297205304245869926423)
            ·
              refine ⟨189081445807956368804889635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126054297205304245869926423 189081445807956368804889635)
              ·
                refine ⟨283622168711934553207334453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189081445807956368804889635 283622168711934553207334453)
                ·
                  refine ⟨26589578316743864363187605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 283622168711934553207334453 26589578316743864363187605)
                  ·
                    refine ⟨1246386483597368642024419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26589578316743864363187605 1246386483597368642024419)
                    ·
                      rfl

theorem cell23_7281987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 6].length) (baseStart_7281987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7281987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7281987 prefixEnd_7281987 := by exact prefixLift 7281987
  have htrace : WordTrace (prefixWord ++ tailWord_7281987) baseStart_7281987 baseEnd_7281987 := by
    simpa [prefixWord, tailWord_7281987, baseEnd_7281987] using wordTrace_append hprefix tailTrace_7281987
  have hstable : (prefixWord ++ tailWord_7281987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7281987).length < 2 ^ (prefixWord ++ tailWord_7281987).sum := by decide
  have hdescent : baseEnd_7281987 < baseStart_7281987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7281987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282017 : List Nat := [1, 2, 3, 1, 1, 1, 1, 13]
def baseStart_7282017 : Nat := 118140960795 + 7282017 * 2 ^ 59
def prefixEnd_7282017 : Nat := 4983230072969 + 3 ^ 40 * 7282017 * 2
def baseEnd_7282017 : Nat := 138487957600434844766597

theorem tailTrace_7282017 : CollatzResearch.WordTrace tailWord_7282017 prefixEnd_7282017 138487957600434844766597 := by
  unfold tailWord_7282017
  simp only [CollatzResearch.WordTrace]
  refine ⟨265596979659503553335124305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177064653106335702223416203 265596979659503553335124305)
  ·
    refine ⟨199197734744627665001343229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265596979659503553335124305 199197734744627665001343229)
    ·
      refine ⟨74699150529235374375503711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199197734744627665001343229 74699150529235374375503711)
      ·
        refine ⟨112048725793853061563255567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74699150529235374375503711 112048725793853061563255567)
        ·
          refine ⟨168073088690779592344883351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112048725793853061563255567 168073088690779592344883351)
          ·
            refine ⟨252109633036169388517325027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168073088690779592344883351 252109633036169388517325027)
            ·
              refine ⟨378164449554254082775987541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252109633036169388517325027 378164449554254082775987541)
              ·
                refine ⟨138487957600434844766597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 378164449554254082775987541 138487957600434844766597)
                ·
                  rfl

theorem cell23_7282017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 13].length) (baseStart_7282017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282017 prefixEnd_7282017 := by exact prefixLift 7282017
  have htrace : WordTrace (prefixWord ++ tailWord_7282017) baseStart_7282017 baseEnd_7282017 := by
    simpa [prefixWord, tailWord_7282017, baseEnd_7282017] using wordTrace_append hprefix tailTrace_7282017
  have hstable : (prefixWord ++ tailWord_7282017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282017).length < 2 ^ (prefixWord ++ tailWord_7282017).sum := by decide
  have hdescent : baseEnd_7282017 < baseStart_7282017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282028 : List Nat := [2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 4]
def baseStart_7282028 : Nat := 118140960795 + 7282028 * 2 ^ 59
def prefixEnd_7282028 : Nat := 4983230072969 + 3 ^ 40 * 7282028 * 2
def baseEnd_7282028 : Nat := 3739180503498940265660569

theorem tailTrace_7282028 : CollatzResearch.WordTrace tailWord_7282028 prefixEnd_7282028 3739180503498940265660569 := by
  unfold tailWord_7282028
  simp only [CollatzResearch.WordTrace]
  refine ⟨132798690431231851106887369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177064920574975801475849825 132798690431231851106887369)
  ·
    refine ⟨99599017823423888330165527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132798690431231851106887369 99599017823423888330165527)
    ·
      refine ⟨149398526735135832495248291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99599017823423888330165527 149398526735135832495248291)
      ·
        refine ⟨224097790102703748742872437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149398526735135832495248291 224097790102703748742872437)
        ·
          refine ⟨21009167822128476444644291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 224097790102703748742872437 21009167822128476444644291)
          ·
            refine ⟨31513751733192714666966437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21009167822128476444644291 31513751733192714666966437)
            ·
              refine ⟨5908828449973634000056207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31513751733192714666966437 5908828449973634000056207)
              ·
                refine ⟨8863242674960451000084311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5908828449973634000056207 8863242674960451000084311)
                ·
                  refine ⟨13294864012440676500126467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8863242674960451000084311 13294864012440676500126467)
                  ·
                    refine ⟨19942296018661014750189701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13294864012440676500126467 19942296018661014750189701)
                    ·
                      refine ⟨3739180503498940265660569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19942296018661014750189701 3739180503498940265660569)
                      ·
                        rfl

theorem cell23_7282028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 4].length) (baseStart_7282028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282028 prefixEnd_7282028 := by exact prefixLift 7282028
  have htrace : WordTrace (prefixWord ++ tailWord_7282028) baseStart_7282028 baseEnd_7282028 := by
    simpa [prefixWord, tailWord_7282028, baseEnd_7282028] using wordTrace_append hprefix tailTrace_7282028
  have hstable : (prefixWord ++ tailWord_7282028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282028).length < 2 ^ (prefixWord ++ tailWord_7282028).sum := by decide
  have hdescent : baseEnd_7282028 < baseStart_7282028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282031 : List Nat := [1, 1, 2, 1, 3, 1, 5, 3, 1, 2, 3]
def baseStart_7282031 : Nat := 118140960795 + 7282031 * 2 ^ 59
def prefixEnd_7282031 : Nat := 4983230072969 + 3 ^ 40 * 7282031 * 2
def baseEnd_7282031 : Nat := 3739182043940903753923055

theorem tailTrace_7282031 : CollatzResearch.WordTrace tailWord_7282031 prefixEnd_7282031 3739182043940903753923055 := by
  unfold tailWord_7282031
  simp only [CollatzResearch.WordTrace]
  refine ⟨265597490281452833726133947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177064993520968555817422631 265597490281452833726133947)
  ·
    refine ⟨398396235422179250589200921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265597490281452833726133947 398396235422179250589200921)
    ·
      refine ⟨298797176566634437941900691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398396235422179250589200921 298797176566634437941900691)
      ·
        refine ⟨448195764849951656912851037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298797176566634437941900691 448195764849951656912851037)
        ·
          refine ⟨168073411818731871342319139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 448195764849951656912851037 168073411818731871342319139)
          ·
            refine ⟨252110117728097807013478709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168073411818731871342319139 252110117728097807013478709)
            ·
              refine ⟨23635323537009169407513629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 252110117728097807013478709 23635323537009169407513629)
              ·
                refine ⟨8863246326378438527817611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23635323537009169407513629 8863246326378438527817611)
                ·
                  refine ⟨13294869489567657791726417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8863246326378438527817611 13294869489567657791726417)
                  ·
                    refine ⟨9971152117175743343794813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13294869489567657791726417 9971152117175743343794813)
                    ·
                      refine ⟨3739182043940903753923055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9971152117175743343794813 3739182043940903753923055)
                      ·
                        rfl

theorem cell23_7282031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 2, 3].length) (baseStart_7282031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282031 prefixEnd_7282031 := by exact prefixLift 7282031
  have htrace : WordTrace (prefixWord ++ tailWord_7282031) baseStart_7282031 baseEnd_7282031 := by
    simpa [prefixWord, tailWord_7282031, baseEnd_7282031] using wordTrace_append hprefix tailTrace_7282031
  have hstable : (prefixWord ++ tailWord_7282031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282031).length < 2 ^ (prefixWord ++ tailWord_7282031).sum := by decide
  have hdescent : baseEnd_7282031 < baseStart_7282031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282045 : List Nat := [1, 4, 1, 1, 2, 2, 1, 6, 1, 2, 2]
def baseStart_7282045 : Nat := 118140960795 + 7282045 * 2 ^ 59
def prefixEnd_7282045 : Nat := 4983230072969 + 3 ^ 40 * 7282045 * 2
def baseEnd_7282045 : Nat := 3739189232670066699147991

theorem tailTrace_7282045 : CollatzResearch.WordTrace tailWord_7282045 prefixEnd_7282045 3739189232670066699147991 := by
  unfold tailWord_7282045
  simp only [CollatzResearch.WordTrace]
  refine ⟨265598000903402114117143589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177065333935601409411429059 265598000903402114117143589)
  ·
    refine ⟨49799625169387896396964423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265598000903402114117143589 49799625169387896396964423)
    ·
      refine ⟨74699437754081844595446635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49799625169387896396964423 74699437754081844595446635)
      ·
        refine ⟨112049156631122766893169953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74699437754081844595446635 112049156631122766893169953)
        ·
          refine ⟨84036867473342075169877465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112049156631122766893169953 84036867473342075169877465)
          ·
            refine ⟨63027650605006556377408099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84036867473342075169877465 63027650605006556377408099)
            ·
              refine ⟨94541475907509834566112149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63027650605006556377408099 94541475907509834566112149)
              ·
                refine ⟨4431631683164523495286507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94541475907509834566112149 4431631683164523495286507)
                ·
                  refine ⟨6647447524746785242929761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4431631683164523495286507 6647447524746785242929761)
                  ·
                    refine ⟨4985585643560088932197321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6647447524746785242929761 4985585643560088932197321)
                    ·
                      refine ⟨3739189232670066699147991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4985585643560088932197321 3739189232670066699147991)
                      ·
                        rfl

theorem cell23_7282045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 6, 1, 2, 2].length) (baseStart_7282045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282045 prefixEnd_7282045 := by exact prefixLift 7282045
  have htrace : WordTrace (prefixWord ++ tailWord_7282045) baseStart_7282045 baseEnd_7282045 := by
    simpa [prefixWord, tailWord_7282045, baseEnd_7282045] using wordTrace_append hprefix tailTrace_7282045
  have hstable : (prefixWord ++ tailWord_7282045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282045).length < 2 ^ (prefixWord ++ tailWord_7282045).sum := by decide
  have hdescent : baseEnd_7282045 < baseStart_7282045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282068 : List Nat := [2, 4, 2, 1, 2, 3, 2, 7]
def baseStart_7282068 : Nat := 118140960795 + 7282068 * 2 ^ 59
def prefixEnd_7282068 : Nat := 4983230072969 + 3 ^ 40 * 7282068 * 2
def baseEnd_7282068 : Nat := 138488927508337781820755

theorem tailTrace_7282068 : CollatzResearch.WordTrace tailWord_7282068 prefixEnd_7282068 138488927508337781820755 := by
  unfold tailWord_7282068
  simp only [CollatzResearch.WordTrace]
  refine ⟨132799419891159394522615429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177065893188212526030153905 132799419891159394522615429)
  ·
    refine ⟨24899891229592386472990393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132799419891159394522615429 24899891229592386472990393)
    ·
      refine ⟨18674918422194289854742795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24899891229592386472990393 18674918422194289854742795)
      ·
        refine ⟨28012377633291434782114193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18674918422194289854742795 28012377633291434782114193)
        ·
          refine ⟨21009283224968576086585645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28012377633291434782114193 21009283224968576086585645)
          ·
            refine ⟨7878481209363216032469617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21009283224968576086585645 7878481209363216032469617)
            ·
              refine ⟨5908860907022412024352213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7878481209363216032469617 5908860907022412024352213)
              ·
                refine ⟨138488927508337781820755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5908860907022412024352213 138488927508337781820755)
                ·
                  rfl

theorem cell23_7282068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 7].length) (baseStart_7282068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282068 prefixEnd_7282068 := by exact prefixLift 7282068
  have htrace : WordTrace (prefixWord ++ tailWord_7282068) baseStart_7282068 baseEnd_7282068 := by
    simpa [prefixWord, tailWord_7282068, baseEnd_7282068] using wordTrace_append hprefix tailTrace_7282068
  have hstable : (prefixWord ++ tailWord_7282068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282068).length < 2 ^ (prefixWord ++ tailWord_7282068).sum := by decide
  have hdescent : baseEnd_7282068 < baseStart_7282068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282074 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 1, 4, 5]
def baseStart_7282074 : Nat := 118140960795 + 7282074 * 2 ^ 59
def prefixEnd_7282074 : Nat := 4983230072969 + 3 ^ 40 * 7282074 * 2
def baseEnd_7282074 : Nat := 3739204123609047085685357

theorem tailTrace_7282074 : CollatzResearch.WordTrace tailWord_7282074 prefixEnd_7282074 3739204123609047085685357 := by
  unfold tailWord_7282074
  simp only [CollatzResearch.WordTrace]
  refine ⟨66399764655074263017487319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177066039080198034713299517 66399764655074263017487319)
  ·
    refine ⟨99599646982611394526230979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66399764655074263017487319 99599646982611394526230979)
    ·
      refine ⟨149399470473917091789346469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99599646982611394526230979 149399470473917091789346469)
      ·
        refine ⟨28012400713859454710502463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149399470473917091789346469 28012400713859454710502463)
        ·
          refine ⟨42018601070789182065753695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28012400713859454710502463 42018601070789182065753695)
          ·
            refine ⟨63027901606183773098630543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42018601070789182065753695 63027901606183773098630543)
            ·
              refine ⟨94541852409275659647945815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63027901606183773098630543 94541852409275659647945815)
              ·
                refine ⟨141812778613913489471918723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94541852409275659647945815 141812778613913489471918723)
                ·
                  refine ⟨212719167920870234207878085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141812778613913489471918723 212719167920870234207878085)
                  ·
                    refine ⟨39884843985163168913977141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 212719167920870234207878085 39884843985163168913977141)
                    ·
                      refine ⟨3739204123609047085685357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39884843985163168913977141 3739204123609047085685357)
                      ·
                        rfl

theorem cell23_7282074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_7282074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282074 prefixEnd_7282074 := by exact prefixLift 7282074
  have htrace : WordTrace (prefixWord ++ tailWord_7282074) baseStart_7282074 baseEnd_7282074 := by
    simpa [prefixWord, tailWord_7282074, baseEnd_7282074] using wordTrace_append hprefix tailTrace_7282074
  have hstable : (prefixWord ++ tailWord_7282074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282074).length < 2 ^ (prefixWord ++ tailWord_7282074).sum := by decide
  have hdescent : baseEnd_7282074 < baseStart_7282074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282084 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 1, 5, 4]
def baseStart_7282084 : Nat := 118140960795 + 7282084 * 2 ^ 59
def prefixEnd_7282084 : Nat := 4983230072969 + 3 ^ 40 * 7282084 * 2
def baseEnd_7282084 : Nat := 3739209258415592046560311

theorem tailTrace_7282084 : CollatzResearch.WordTrace tailWord_7282084 prefixEnd_7282084 3739209258415592046560311 := by
  unfold tailWord_7282084
  simp only [CollatzResearch.WordTrace]
  refine ⟨132799711675130411888906653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177066282233507215851875537 132799711675130411888906653)
  ·
    refine ⟨49799891878173904458339995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132799711675130411888906653 49799891878173904458339995)
    ·
      refine ⟨74699837817260856687509993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49799891878173904458339995 74699837817260856687509993)
      ·
        refine ⟨56024878362945642515632495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74699837817260856687509993 56024878362945642515632495)
        ·
          refine ⟨84037317544418463773448743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56024878362945642515632495 84037317544418463773448743)
          ·
            refine ⟨126055976316627695660173115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84037317544418463773448743 126055976316627695660173115)
            ·
              refine ⟨189083964474941543490259673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126055976316627695660173115 189083964474941543490259673)
              ·
                refine ⟨141812973356206157617694755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189083964474941543490259673 141812973356206157617694755)
                ·
                  refine ⟨212719460034309236426542133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141812973356206157617694755 212719460034309236426542133)
                  ·
                    refine ⟨19942449378216490914988325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 212719460034309236426542133 19942449378216490914988325)
                    ·
                      refine ⟨3739209258415592046560311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19942449378216490914988325 3739209258415592046560311)
                      ·
                        rfl

theorem cell23_7282084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_7282084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282084 prefixEnd_7282084 := by exact prefixLift 7282084
  have htrace : WordTrace (prefixWord ++ tailWord_7282084) baseStart_7282084 baseEnd_7282084 := by
    simpa [prefixWord, tailWord_7282084, baseEnd_7282084] using wordTrace_append hprefix tailTrace_7282084
  have hstable : (prefixWord ++ tailWord_7282084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282084).length < 2 ^ (prefixWord ++ tailWord_7282084).sum := by decide
  have hdescent : baseEnd_7282084 < baseStart_7282084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282158 : List Nat := [4, 1, 2, 1, 2, 1, 3, 4, 5]
def baseStart_7282158 : Nat := 118140960795 + 7282158 * 2 ^ 59
def prefixEnd_7282158 : Nat := 4983230072969 + 3 ^ 40 * 7282158 * 2
def baseEnd_7282158 : Nat := 415471917331558306337219

theorem tailTrace_7282158 : CollatzResearch.WordTrace tailWord_7282158 prefixEnd_7282158 415471917331558306337219 := by
  unfold tailWord_7282158
  simp only [CollatzResearch.WordTrace]
  refine ⟨33200265293999091802000891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177068081567995156277338085 33200265293999091802000891)
  ·
    refine ⟨49800397940998637703001337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33200265293999091802000891 49800397940998637703001337)
    ·
      refine ⟨37350298455748978277251003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49800397940998637703001337 37350298455748978277251003)
      ·
        refine ⟨56025447683623467415876505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37350298455748978277251003 56025447683623467415876505)
        ·
          refine ⟨42019085762717600561907379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56025447683623467415876505 42019085762717600561907379)
          ·
            refine ⟨63028628644076400842861069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42019085762717600561907379 63028628644076400842861069)
            ·
              refine ⟨23635735741528650316072901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63028628644076400842861069 23635735741528650316072901)
              ·
                refine ⟨4431700451536621934263669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23635735741528650316072901 4431700451536621934263669)
                ·
                  refine ⟨415471917331558306337219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4431700451536621934263669 415471917331558306337219)
                  ·
                    rfl

theorem cell23_7282158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 4, 5].length) (baseStart_7282158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282158 prefixEnd_7282158 := by exact prefixLift 7282158
  have htrace : WordTrace (prefixWord ++ tailWord_7282158) baseStart_7282158 baseEnd_7282158 := by
    simpa [prefixWord, tailWord_7282158, baseEnd_7282158] using wordTrace_append hprefix tailTrace_7282158
  have hstable : (prefixWord ++ tailWord_7282158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282158).length < 2 ^ (prefixWord ++ tailWord_7282158).sum := by decide
  have hdescent : baseEnd_7282158 < baseStart_7282158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282252 : List Nat := [2, 2, 1, 3, 1, 5, 1, 3, 1, 4]
def baseStart_7282252 : Nat := 118140960795 + 7282252 * 2 ^ 59
def prefixEnd_7282252 : Nat := 4983230072969 + 3 ^ 40 * 7282252 * 2
def baseEnd_7282252 : Nat := 1246431841055182463086513

theorem tailTrace_7282252 : CollatzResearch.WordTrace tailWord_7282252 prefixEnd_7282252 1246431841055182463086513 := by
  unfold tailWord_7282252
  simp only [CollatzResearch.WordTrace]
  refine ⟨132802775406826094234964505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177070367209101458979952673 132802775406826094234964505)
  ·
    refine ⟨99602081555119570676223379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132802775406826094234964505 99602081555119570676223379)
    ·
      refine ⟨149403122332679356014335069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99602081555119570676223379 149403122332679356014335069)
      ·
        refine ⟨56026170874754758505375651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149403122332679356014335069 56026170874754758505375651)
        ·
          refine ⟨84039256312132137758063477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56026170874754758505375651 84039256312132137758063477)
          ·
            refine ⟨7878680279262387914818451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84039256312132137758063477 7878680279262387914818451)
            ·
              refine ⟨11818020418893581872227677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7878680279262387914818451 11818020418893581872227677)
              ·
                refine ⟨4431757657085093202085379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11818020418893581872227677 4431757657085093202085379)
                ·
                  refine ⟨6647636485627639803128069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4431757657085093202085379 6647636485627639803128069)
                  ·
                    refine ⟨1246431841055182463086513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6647636485627639803128069 1246431841055182463086513)
                    ·
                      rfl

theorem cell23_7282252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 3, 1, 4].length) (baseStart_7282252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282252 prefixEnd_7282252 := by exact prefixLift 7282252
  have htrace : WordTrace (prefixWord ++ tailWord_7282252) baseStart_7282252 baseEnd_7282252 := by
    simpa [prefixWord, tailWord_7282252, baseEnd_7282252] using wordTrace_append hprefix tailTrace_7282252
  have hstable : (prefixWord ++ tailWord_7282252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282252).length < 2 ^ (prefixWord ++ tailWord_7282252).sum := by decide
  have hdescent : baseEnd_7282252 < baseStart_7282252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282261 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 5, 5]
def baseStart_7282261 : Nat := 118140960795 + 7282261 * 2 ^ 59
def prefixEnd_7282261 : Nat := 4983230072969 + 3 ^ 40 * 7282261 * 2
def baseEnd_7282261 : Nat := 1246433381497145951348999

theorem tailTrace_7282261 : CollatzResearch.WordTrace tailWord_7282261 prefixEnd_7282261 1246433381497145951348999 := by
  unfold tailWord_7282261
  simp only [CollatzResearch.WordTrace]
  refine ⟨265605879070619583007006637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177070586047079722004671091 265605879070619583007006637)
  ·
    refine ⟨99602204651482343627627489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265605879070619583007006637 99602204651482343627627489)
    ·
      refine ⟨74701653488611757720720617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99602204651482343627627489 74701653488611757720720617)
      ·
        refine ⟨56026240116458818290540463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74701653488611757720720617 56026240116458818290540463)
        ·
          refine ⟨84039360174688227435810695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56026240116458818290540463 84039360174688227435810695)
          ·
            refine ⟨126059040262032341153716043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84039360174688227435810695 126059040262032341153716043)
            ·
              refine ⟨189088560393048511730574065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126059040262032341153716043 189088560393048511730574065)
              ·
                refine ⟨141816420294786383797930549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189088560393048511730574065 141816420294786383797930549)
                ·
                  refine ⟨13295289402636223481055989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141816420294786383797930549 13295289402636223481055989)
                  ·
                    refine ⟨1246433381497145951348999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13295289402636223481055989 1246433381497145951348999)
                    ·
                      rfl

theorem cell23_7282261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_7282261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282261 prefixEnd_7282261 := by exact prefixLift 7282261
  have htrace : WordTrace (prefixWord ++ tailWord_7282261) baseStart_7282261 baseEnd_7282261 := by
    simpa [prefixWord, tailWord_7282261, baseEnd_7282261] using wordTrace_append hprefix tailTrace_7282261
  have hstable : (prefixWord ++ tailWord_7282261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282261).length < 2 ^ (prefixWord ++ tailWord_7282261).sum := by decide
  have hdescent : baseEnd_7282261 < baseStart_7282261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282269 : List Nat := [1, 4, 4, 2, 1, 2, 1, 1, 3, 4]
def baseStart_7282269 : Nat := 118140960795 + 7282269 * 2 ^ 59
def prefixEnd_7282269 : Nat := 4983230072969 + 3 ^ 40 * 7282269 * 2
def baseEnd_7282269 : Nat := 1246434750778891274248987

theorem tailTrace_7282269 : CollatzResearch.WordTrace tailWord_7282269 prefixEnd_7282269 1246434750778891274248987 := by
  unfold tailWord_7282269
  simp only [CollatzResearch.WordTrace]
  refine ⟨265606170854590600373297861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177070780569727066915531907 265606170854590600373297861)
  ·
    refine ⟨49801157035235737569993349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265606170854590600373297861 49801157035235737569993349)
    ·
      refine ⟨9337716944106700794373753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49801157035235737569993349 9337716944106700794373753)
      ·
        refine ⟨7003287708080025595780315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9337716944106700794373753 7003287708080025595780315)
        ·
          refine ⟨10504931562120038393670473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7003287708080025595780315 10504931562120038393670473)
          ·
            refine ⟨7878698671590028795252855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10504931562120038393670473 7878698671590028795252855)
            ·
              refine ⟨11818048007385043192879283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7878698671590028795252855 11818048007385043192879283)
              ·
                refine ⟨17727072011077564789318925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11818048007385043192879283 17727072011077564789318925)
                ·
                  refine ⟨6647652004154086795994597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17727072011077564789318925 6647652004154086795994597)
                  ·
                    refine ⟨1246434750778891274248987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6647652004154086795994597 1246434750778891274248987)
                    ·
                      rfl

theorem cell23_7282269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_7282269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282269 prefixEnd_7282269 := by exact prefixLift 7282269
  have htrace : WordTrace (prefixWord ++ tailWord_7282269) baseStart_7282269 baseEnd_7282269 := by
    simpa [prefixWord, tailWord_7282269, baseEnd_7282269] using wordTrace_append hprefix tailTrace_7282269
  have hstable : (prefixWord ++ tailWord_7282269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282269).length < 2 ^ (prefixWord ++ tailWord_7282269).sum := by decide
  have hdescent : baseEnd_7282269 < baseStart_7282269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282275 : List Nat := [1, 1, 1, 5, 1, 3, 3, 1, 3, 1, 3]
def baseStart_7282275 : Nat := 118140960795 + 7282275 * 2 ^ 59
def prefixEnd_7282275 : Nat := 4983230072969 + 3 ^ 40 * 7282275 * 2
def baseEnd_7282275 : Nat := 3739307333220600799271933

theorem tailTrace_7282275 : CollatzResearch.WordTrace tailWord_7282275 prefixEnd_7282275 3739307333220600799271933 := by
  unfold tailWord_7282275
  simp only [CollatzResearch.WordTrace]
  refine ⟨265606389692568863398016279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177070926461712575598677519 265606389692568863398016279)
  ·
    refine ⟨398409584538853295097024419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265606389692568863398016279 398409584538853295097024419)
    ·
      refine ⟨597614376808279942645536629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398409584538853295097024419 597614376808279942645536629)
      ·
        refine ⟨56026347825776244623019059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 597614376808279942645536629 56026347825776244623019059)
        ·
          refine ⟨84039521738664366934528589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56026347825776244623019059 84039521738664366934528589)
          ·
            refine ⟨31514820651999137600448221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84039521738664366934528589 31514820651999137600448221)
            ·
              refine ⟨11818057744499676600168083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31514820651999137600448221 11818057744499676600168083)
              ·
                refine ⟨17727086616749514900252125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11818057744499676600168083 17727086616749514900252125)
                ·
                  refine ⟨6647657481281068087594547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17727086616749514900252125 6647657481281068087594547)
                  ·
                    refine ⟨9971486221921602131391821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6647657481281068087594547 9971486221921602131391821)
                    ·
                      refine ⟨3739307333220600799271933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9971486221921602131391821 3739307333220600799271933)
                      ·
                        rfl

theorem cell23_7282275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_7282275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282275 prefixEnd_7282275 := by exact prefixLift 7282275
  have htrace : WordTrace (prefixWord ++ tailWord_7282275) baseStart_7282275 baseEnd_7282275 := by
    simpa [prefixWord, tailWord_7282275, baseEnd_7282275] using wordTrace_append hprefix tailTrace_7282275
  have hstable : (prefixWord ++ tailWord_7282275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282275).length < 2 ^ (prefixWord ++ tailWord_7282275).sum := by decide
  have hdescent : baseEnd_7282275 < baseStart_7282275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282298 : List Nat := [3, 1, 1, 1, 1, 1, 1, 8, 1, 1, 4]
def baseStart_7282298 : Nat := 118140960795 + 7282298 * 2 ^ 59
def prefixEnd_7282298 : Nat := 4983230072969 + 3 ^ 40 * 7282298 * 2
def baseEnd_7282298 : Nat := 3739319143275654209284327

theorem tailTrace_7282298 : CollatzResearch.WordTrace tailWord_7282298 prefixEnd_7282298 3739319143275654209284327 := by
  unfold tailWord_7282298
  simp only [CollatzResearch.WordTrace]
  refine ⟨66401807142871384581525887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177071485714323692217402365 66401807142871384581525887)
  ·
    refine ⟨99602710714307076872288831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66401807142871384581525887 99602710714307076872288831)
    ·
      refine ⟨149404066071460615308433247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99602710714307076872288831 149404066071460615308433247)
      ·
        refine ⟨224106099107190922962649871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149404066071460615308433247 224106099107190922962649871)
        ·
          refine ⟨336159148660786384443974807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224106099107190922962649871 336159148660786384443974807)
          ·
            refine ⟨504238722991179576665962211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336159148660786384443974807 504238722991179576665962211)
            ·
              refine ⟨756358084486769364998943317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504238722991179576665962211 756358084486769364998943317)
              ·
                refine ⟨8863571302579328496081367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 756358084486769364998943317 8863571302579328496081367)
                ·
                  refine ⟨13295356953868992744122051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8863571302579328496081367 13295356953868992744122051)
                  ·
                    refine ⟨19943035430803489116183077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13295356953868992744122051 19943035430803489116183077)
                    ·
                      refine ⟨3739319143275654209284327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19943035430803489116183077 3739319143275654209284327)
                      ·
                        rfl

theorem cell23_7282298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 1, 1, 4].length) (baseStart_7282298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282298 prefixEnd_7282298 := by exact prefixLift 7282298
  have htrace : WordTrace (prefixWord ++ tailWord_7282298) baseStart_7282298 baseEnd_7282298 := by
    simpa [prefixWord, tailWord_7282298, baseEnd_7282298] using wordTrace_append hprefix tailTrace_7282298
  have hstable : (prefixWord ++ tailWord_7282298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282298).length < 2 ^ (prefixWord ++ tailWord_7282298).sum := by decide
  have hdescent : baseEnd_7282298 < baseStart_7282298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282315 : List Nat := [1, 1, 1, 1, 4, 1, 7, 1, 1, 1, 4]
def baseStart_7282315 : Nat := 118140960795 + 7282315 * 2 ^ 59
def prefixEnd_7282315 : Nat := 4983230072969 + 3 ^ 40 * 7282315 * 2
def baseEnd_7282315 : Nat := 3739327872446780642771749

theorem tailTrace_7282315 : CollatzResearch.WordTrace tailWord_7282315 prefixEnd_7282315 3739327872446780642771749 := by
  unfold tailWord_7282315
  simp only [CollatzResearch.WordTrace]
  refine ⟨265607848612423950229472399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177071899074949300152981599 265607848612423950229472399)
  ·
    refine ⟨398411772918635925344208599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265607848612423950229472399 398411772918635925344208599)
    ·
      refine ⟨597617659377953888016312899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398411772918635925344208599 597617659377953888016312899)
      ·
        refine ⟨896426489066930832024469349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597617659377953888016312899 896426489066930832024469349)
        ·
          refine ⟨168079966700049531004588003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 896426489066930832024469349 168079966700049531004588003)
          ·
            refine ⟨252119950050074296506882005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168079966700049531004588003 252119950050074296506882005)
            ·
              refine ⟨5909061329298616324380047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 252119950050074296506882005 5909061329298616324380047)
              ·
                refine ⟨8863591993947924486570071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5909061329298616324380047 8863591993947924486570071)
                ·
                  refine ⟨13295387990921886729855107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8863591993947924486570071 13295387990921886729855107)
                  ·
                    refine ⟨19943081986382830094782661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13295387990921886729855107 19943081986382830094782661)
                    ·
                      refine ⟨3739327872446780642771749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19943081986382830094782661 3739327872446780642771749)
                      ·
                        rfl

theorem cell23_7282315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 1, 1, 4].length) (baseStart_7282315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282315 prefixEnd_7282315 := by exact prefixLift 7282315
  have htrace : WordTrace (prefixWord ++ tailWord_7282315) baseStart_7282315 baseEnd_7282315 := by
    simpa [prefixWord, tailWord_7282315, baseEnd_7282315] using wordTrace_append hprefix tailTrace_7282315
  have hstable : (prefixWord ++ tailWord_7282315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282315).length < 2 ^ (prefixWord ++ tailWord_7282315).sum := by decide
  have hdescent : baseEnd_7282315 < baseStart_7282315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282341 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 2, 2, 6]
def baseStart_7282341 : Nat := 118140960795 + 7282341 * 2 ^ 59
def prefixEnd_7282341 : Nat := 4983230072969 + 3 ^ 40 * 7282341 * 2
def baseEnd_7282341 : Nat := 3739341222943797541046629

theorem tailTrace_7282341 : CollatzResearch.WordTrace tailWord_7282341 prefixEnd_7282341 3739341222943797541046629 := by
  unfold tailWord_7282341
  simp only [CollatzResearch.WordTrace]
  refine ⟨265608796910329756669918877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177072531273553171113279251 265608796910329756669918877)
  ·
    refine ⟨99603298841373658751219579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265608796910329756669918877 99603298841373658751219579)
    ·
      refine ⟨149404948262060488126829369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99603298841373658751219579 149404948262060488126829369)
      ·
        refine ⟨112053711196545366095122027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149404948262060488126829369 112053711196545366095122027)
        ·
          refine ⟨168080566794818049142683041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112053711196545366095122027 168080566794818049142683041)
          ·
            refine ⟨126060425096113536857012281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168080566794818049142683041 126060425096113536857012281)
            ·
              refine ⟨94545318822085152642759211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126060425096113536857012281 94545318822085152642759211)
              ·
                refine ⟨141817978233127728964138817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94545318822085152642759211 141817978233127728964138817)
                ·
                  refine ⟨106363483674845796723104113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141817978233127728964138817 106363483674845796723104113)
                  ·
                    refine ⟨79772612756134347542328085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106363483674845796723104113 79772612756134347542328085)
                    ·
                      refine ⟨3739341222943797541046629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79772612756134347542328085 3739341222943797541046629)
                      ·
                        rfl

theorem cell23_7282341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_7282341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282341 prefixEnd_7282341 := by exact prefixLift 7282341
  have htrace : WordTrace (prefixWord ++ tailWord_7282341) baseStart_7282341 baseEnd_7282341 := by
    simpa [prefixWord, tailWord_7282341, baseEnd_7282341] using wordTrace_append hprefix tailTrace_7282341
  have hstable : (prefixWord ++ tailWord_7282341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282341).length < 2 ^ (prefixWord ++ tailWord_7282341).sum := by decide
  have hdescent : baseEnd_7282341 < baseStart_7282341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282351 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 2, 7]
def baseStart_7282351 : Nat := 118140960795 + 7282351 * 2 ^ 59
def prefixEnd_7282351 : Nat := 4983230072969 + 3 ^ 40 * 7282351 * 2
def baseEnd_7282351 : Nat := 1246448785916780833973861

theorem tailTrace_7282351 : CollatzResearch.WordTrace tailWord_7282351 prefixEnd_7282351 1246448785916780833973861 := by
  unfold tailWord_7282351
  simp only [CollatzResearch.WordTrace]
  refine ⟨265609161640293528377782907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177072774426862352251855271 265609161640293528377782907)
  ·
    refine ⟨398413742460440292566674361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265609161640293528377782907 398413742460440292566674361)
    ·
      refine ⟨298810306845330219425005771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398413742460440292566674361 298810306845330219425005771)
      ·
        refine ⟨448215460267995329137508657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298810306845330219425005771 448215460267995329137508657)
        ·
          refine ⟨336161595200996496853131493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448215460267995329137508657 336161595200996496853131493)
          ·
            refine ⟨63030299100186843159962155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 336161595200996496853131493 63030299100186843159962155)
            ·
              refine ⟨94545448650280264739943233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63030299100186843159962155 94545448650280264739943233)
              ·
                refine ⟨70909086487710198554957425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94545448650280264739943233 70909086487710198554957425)
                ·
                  refine ⟨53181814865782648916218069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70909086487710198554957425 53181814865782648916218069)
                  ·
                    refine ⟨1246448785916780833973861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53181814865782648916218069 1246448785916780833973861)
                    ·
                      rfl

theorem cell23_7282351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 7].length) (baseStart_7282351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282351 prefixEnd_7282351 := by exact prefixLift 7282351
  have htrace : WordTrace (prefixWord ++ tailWord_7282351) baseStart_7282351 baseEnd_7282351 := by
    simpa [prefixWord, tailWord_7282351, baseEnd_7282351] using wordTrace_append hprefix tailTrace_7282351
  have hstable : (prefixWord ++ tailWord_7282351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282351).length < 2 ^ (prefixWord ++ tailWord_7282351).sum := by decide
  have hdescent : baseEnd_7282351 < baseStart_7282351 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282365 : List Nat := [1, 4, 1, 2, 1, 2, 2, 2, 4, 1, 3]
def baseStart_7282365 : Nat := 118140960795 + 7282365 * 2 ^ 59
def prefixEnd_7282365 : Nat := 4983230072969 + 3 ^ 40 * 7282365 * 2
def baseEnd_7282365 : Nat := 3739353546479505447146519

theorem tailTrace_7282365 : CollatzResearch.WordTrace tailWord_7282365 prefixEnd_7282365 3739353546479505447146519 := by
  unfold tailWord_7282365
  simp only [CollatzResearch.WordTrace]
  refine ⟨265609672262242808768792549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177073114841495205845861699 265609672262242808768792549)
  ·
    refine ⟨49801813549170526644148603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265609672262242808768792549 49801813549170526644148603)
    ·
      refine ⟨74702720323755789966222905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49801813549170526644148603 74702720323755789966222905)
      ·
        refine ⟨56027040242816842474667179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74702720323755789966222905 56027040242816842474667179)
        ·
          refine ⟨84040560364225263712000769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56027040242816842474667179 84040560364225263712000769)
          ·
            refine ⟨63030420273168947784000577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84040560364225263712000769 63030420273168947784000577)
            ·
              refine ⟨47272815204876710838000433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63030420273168947784000577 47272815204876710838000433)
              ·
                refine ⟨35454611403657533128500325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47272815204876710838000433 35454611403657533128500325)
                ·
                  refine ⟨6647739638185787461593811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35454611403657533128500325 6647739638185787461593811)
                  ·
                    refine ⟨9971609457278681192390717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6647739638185787461593811 9971609457278681192390717)
                    ·
                      refine ⟨3739353546479505447146519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9971609457278681192390717 3739353546479505447146519)
                      ·
                        rfl

theorem cell23_7282365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_7282365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282365 prefixEnd_7282365 := by exact prefixLift 7282365
  have htrace : WordTrace (prefixWord ++ tailWord_7282365) baseStart_7282365 baseEnd_7282365 := by
    simpa [prefixWord, tailWord_7282365, baseEnd_7282365] using wordTrace_append hprefix tailTrace_7282365
  have hstable : (prefixWord ++ tailWord_7282365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282365).length < 2 ^ (prefixWord ++ tailWord_7282365).sum := by decide
  have hdescent : baseEnd_7282365 < baseStart_7282365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282366 : List Nat := [4, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2]
def baseStart_7282366 : Nat := 118140960795 + 7282366 * 2 ^ 59
def prefixEnd_7282366 : Nat := 4983230072969 + 3 ^ 40 * 7282366 * 2
def baseEnd_7282366 : Nat := 3739354059960159943234015

theorem tailTrace_7282366 : CollatzResearch.WordTrace tailWord_7282366 prefixEnd_7282366 3739354059960159943234015 := by
  unfold tailWord_7282366
  simp only [CollatzResearch.WordTrace]
  refine ⟨33201213591904898242447369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177073139156826123959719301 33201213591904898242447369)
  ·
    refine ⟨24900910193928673681835527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33201213591904898242447369 24900910193928673681835527)
    ·
      refine ⟨37351365290893010522753291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24900910193928673681835527 37351365290893010522753291)
      ·
        refine ⟨56027047936339515784129937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37351365290893010522753291 56027047936339515784129937)
        ·
          refine ⟨42020285952254636838097453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56027047936339515784129937 42020285952254636838097453)
          ·
            refine ⟨15757607232095488814286545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42020285952254636838097453 15757607232095488814286545)
            ·
              refine ⟨11818205424071616610714909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15757607232095488814286545 11818205424071616610714909)
              ·
                refine ⟨4431827034026856229018091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11818205424071616610714909 4431827034026856229018091)
                ·
                  refine ⟨6647740551040284343527137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4431827034026856229018091 6647740551040284343527137)
                  ·
                    refine ⟨4985805413280213257645353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6647740551040284343527137 4985805413280213257645353)
                    ·
                      refine ⟨3739354059960159943234015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4985805413280213257645353 3739354059960159943234015)
                      ·
                        rfl

theorem cell23_7282366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_7282366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282366 prefixEnd_7282366 := by exact prefixLift 7282366
  have htrace : WordTrace (prefixWord ++ tailWord_7282366) baseStart_7282366 baseEnd_7282366 := by
    simpa [prefixWord, tailWord_7282366, baseEnd_7282366] using wordTrace_append hprefix tailTrace_7282366
  have hstable : (prefixWord ++ tailWord_7282366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282366).length < 2 ^ (prefixWord ++ tailWord_7282366).sum := by decide
  have hdescent : baseEnd_7282366 < baseStart_7282366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282505 : List Nat := [1, 2, 1, 1, 2, 4, 2, 3, 3, 4]
def baseStart_7282505 : Nat := 118140960795 + 7282505 * 2 ^ 59
def prefixEnd_7282505 : Nat := 4983230072969 + 3 ^ 40 * 7282505 * 2
def baseEnd_7282505 : Nat := 1246475144590378299798625

theorem tailTrace_7282505 : CollatzResearch.WordTrace tailWord_7282505 prefixEnd_7282505 1246475144590378299798625 := by
  unfold tailWord_7282505
  simp only [CollatzResearch.WordTrace]
  refine ⟨265614778481735612678888969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177076518987823741785925979 265614778481735612678888969)
  ·
    refine ⟨199211083861301709509166727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265614778481735612678888969 199211083861301709509166727)
    ·
      refine ⟨298816625791952564263750091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199211083861301709509166727 298816625791952564263750091)
      ·
        refine ⟨448224938687928846395625137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298816625791952564263750091 448224938687928846395625137)
        ·
          refine ⟨336168704015946634796718853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448224938687928846395625137 336168704015946634796718853)
          ·
            refine ⟨63031632002989994024384785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 336168704015946634796718853 63031632002989994024384785)
            ·
              refine ⟨47273724002242495518288589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63031632002989994024384785 47273724002242495518288589)
              ·
                refine ⟨17727646500840935819358221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47273724002242495518288589 17727646500840935819358221)
                ·
                  refine ⟨6647867437815350932259333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17727646500840935819358221 6647867437815350932259333)
                  ·
                    refine ⟨1246475144590378299798625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6647867437815350932259333 1246475144590378299798625)
                    ·
                      rfl

theorem cell23_7282505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 3, 4].length) (baseStart_7282505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282505 prefixEnd_7282505 := by exact prefixLift 7282505
  have htrace : WordTrace (prefixWord ++ tailWord_7282505) baseStart_7282505 baseEnd_7282505 := by
    simpa [prefixWord, tailWord_7282505, baseEnd_7282505] using wordTrace_append hprefix tailTrace_7282505
  have hstable : (prefixWord ++ tailWord_7282505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282505).length < 2 ^ (prefixWord ++ tailWord_7282505).sum := by decide
  have hdescent : baseEnd_7282505 < baseStart_7282505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282532 : List Nat := [2, 3, 1, 1, 5, 1, 1, 1, 1, 4, 3]
def baseStart_7282532 : Nat := 118140960795 + 7282532 * 2 ^ 59
def prefixEnd_7282532 : Nat := 4983230072969 + 3 ^ 40 * 7282532 * 2
def baseEnd_7282532 : Nat := 3739439297748806293758251

theorem tailTrace_7282532 : CollatzResearch.WordTrace tailWord_7282532 prefixEnd_7282532 3739439297748806293758251 := by
  unfold tailWord_7282532
  simp only [CollatzResearch.WordTrace]
  refine ⟨132807881626318898145060925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177077175501758530860081233 132807881626318898145060925)
  ·
    refine ⟨49802955609869586804397847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132807881626318898145060925 49802955609869586804397847)
    ·
      refine ⟨74704433414804380206596771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49802955609869586804397847 74704433414804380206596771)
      ·
        refine ⟨112056650122206570309895157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74704433414804380206596771 112056650122206570309895157)
        ·
          refine ⟨10505310948956865966552671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112056650122206570309895157 10505310948956865966552671)
          ·
            refine ⟨15757966423435298949829007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10505310948956865966552671 15757966423435298949829007)
            ·
              refine ⟨23636949635152948424743511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15757966423435298949829007 23636949635152948424743511)
              ·
                refine ⟨35455424452729422637115267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23636949635152948424743511 35455424452729422637115267)
                ·
                  refine ⟨53183136679094133955672901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35455424452729422637115267 53183136679094133955672901)
                  ·
                    refine ⟨9971838127330150116688669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53183136679094133955672901 9971838127330150116688669)
                    ·
                      refine ⟨3739439297748806293758251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9971838127330150116688669 3739439297748806293758251)
                      ·
                        rfl

theorem cell23_7282532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_7282532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282532 prefixEnd_7282532 := by exact prefixLift 7282532
  have htrace : WordTrace (prefixWord ++ tailWord_7282532) baseStart_7282532 baseEnd_7282532 := by
    simpa [prefixWord, tailWord_7282532, baseEnd_7282532] using wordTrace_append hprefix tailTrace_7282532
  have hstable : (prefixWord ++ tailWord_7282532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282532).length < 2 ^ (prefixWord ++ tailWord_7282532).sum := by decide
  have hdescent : baseEnd_7282532 < baseStart_7282532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282585 : List Nat := [1, 2, 1, 2, 1, 3, 2, 3, 3, 1, 4]
def baseStart_7282585 : Nat := 118140960795 + 7282585 * 2 ^ 59
def prefixEnd_7282585 : Nat := 4983230072969 + 3 ^ 40 * 7282585 * 2
def baseEnd_7282585 : Nat := 3739466512223494586395507

theorem tailTrace_7282585 : CollatzResearch.WordTrace tailWord_7282585 prefixEnd_7282585 3739466512223494586395507 := by
  unfold tailWord_7282585
  simp only [CollatzResearch.WordTrace]
  refine ⟨265617696321445786341801209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177078464214297190894534139 265617696321445786341801209)
  ·
    refine ⟨199213272241084339756350907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265617696321445786341801209 199213272241084339756350907)
    ·
      refine ⟨298819908361626509634526361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199213272241084339756350907 298819908361626509634526361)
      ·
        refine ⟨224114931271219882225894771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298819908361626509634526361 224114931271219882225894771)
        ·
          refine ⟨336172396906829823338842157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224114931271219882225894771 336172396906829823338842157)
          ·
            refine ⟨126064648840061183752065809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 336172396906829823338842157 126064648840061183752065809)
            ·
              refine ⟨94548486630045887814049357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126064648840061183752065809 94548486630045887814049357)
              ·
                refine ⟨35455682486267207930268509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94548486630045887814049357 35455682486267207930268509)
                ·
                  refine ⟨13295880932350202973850691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35455682486267207930268509 13295880932350202973850691)
                  ·
                    refine ⟨19943821398525304460776037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13295880932350202973850691 19943821398525304460776037)
                    ·
                      refine ⟨3739466512223494586395507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19943821398525304460776037 3739466512223494586395507)
                      ·
                        rfl

theorem cell23_7282585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_7282585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282585 prefixEnd_7282585 := by exact prefixLift 7282585
  have htrace : WordTrace (prefixWord ++ tailWord_7282585) baseStart_7282585 baseEnd_7282585 := by
    simpa [prefixWord, tailWord_7282585, baseEnd_7282585] using wordTrace_append hprefix tailTrace_7282585
  have hstable : (prefixWord ++ tailWord_7282585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282585).length < 2 ^ (prefixWord ++ tailWord_7282585).sum := by decide
  have hdescent : baseEnd_7282585 < baseStart_7282585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282590 : List Nat := [4, 3, 1, 3, 1, 2, 1, 3, 1, 4]
def baseStart_7282590 : Nat := 118140960795 + 7282590 * 2 ^ 59
def prefixEnd_7282590 : Nat := 4983230072969 + 3 ^ 40 * 7282590 * 2
def baseEnd_7282590 : Nat := 1246489693208922355610995

theorem tailTrace_7282590 : CollatzResearch.WordTrace tailWord_7282590 prefixEnd_7282590 1246489693208922355610995 := by
  unfold tailWord_7282590
  simp only [CollatzResearch.WordTrace]
  refine ⟨33202234835803459024466653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177078585790951781463822149 33202234835803459024466653)
  ·
    refine ⟨12450838063426297134174995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33202234835803459024466653 12450838063426297134174995)
    ·
      refine ⟨18676257095139445701262493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12450838063426297134174995 18676257095139445701262493)
      ·
        refine ⟨7003596410677292137973435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18676257095139445701262493 7003596410677292137973435)
        ·
          refine ⟨10505394616015938206960153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7003596410677292137973435 10505394616015938206960153)
          ·
            refine ⟨7879045962011953655220115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10505394616015938206960153 7879045962011953655220115)
            ·
              refine ⟨11818568943017930482830173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7879045962011953655220115 11818568943017930482830173)
              ·
                refine ⟨4431963353631723931061315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11818568943017930482830173 4431963353631723931061315)
                ·
                  refine ⟨6647945030447585896591973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4431963353631723931061315 6647945030447585896591973)
                  ·
                    refine ⟨1246489693208922355610995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6647945030447585896591973 1246489693208922355610995)
                    ·
                      rfl

theorem cell23_7282590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_7282590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282590 prefixEnd_7282590 := by exact prefixLift 7282590
  have htrace : WordTrace (prefixWord ++ tailWord_7282590) baseStart_7282590 baseEnd_7282590 := by
    simpa [prefixWord, tailWord_7282590, baseEnd_7282590] using wordTrace_append hprefix tailTrace_7282590
  have hstable : (prefixWord ++ tailWord_7282590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282590).length < 2 ^ (prefixWord ++ tailWord_7282590).sum := by decide
  have hdescent : baseEnd_7282590 < baseStart_7282590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282596 : List Nat := [2, 3, 1, 2, 1, 3, 3, 3, 1, 1, 3]
def baseStart_7282596 : Nat := 118140960795 + 7282596 * 2 ^ 59
def prefixEnd_7282596 : Nat := 4983230072969 + 3 ^ 40 * 7282596 * 2
def baseEnd_7282596 : Nat := 3739472160510694043357957

theorem tailTrace_7282596 : CollatzResearch.WordTrace tailWord_7282596 prefixEnd_7282596 3739472160510694043357957 := by
  unfold tailWord_7282596
  simp only [CollatzResearch.WordTrace]
  refine ⟨132809048762202967610225821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177078731682937290146967761 132809048762202967610225821)
  ·
    refine ⟨49803393285826112853834683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132809048762202967610225821 49803393285826112853834683)
    ·
      refine ⟨74705089928739169280752025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49803393285826112853834683 74705089928739169280752025)
      ·
        refine ⟨56028817446554376960564019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74705089928739169280752025 56028817446554376960564019)
        ·
          refine ⟨84043226169831565440846029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56028817446554376960564019 84043226169831565440846029)
          ·
            refine ⟨31516209813686837040317261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84043226169831565440846029 31516209813686837040317261)
            ·
              refine ⟨11818578680132563890118973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31516209813686837040317261 11818578680132563890118973)
              ·
                refine ⟨4431967005049711458794615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11818578680132563890118973 4431967005049711458794615)
                ·
                  refine ⟨6647950507574567188191923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4431967005049711458794615 6647950507574567188191923)
                  ·
                    refine ⟨9971925761361850782287885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6647950507574567188191923 9971925761361850782287885)
                    ·
                      refine ⟨3739472160510694043357957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9971925761361850782287885 3739472160510694043357957)
                      ·
                        rfl

theorem cell23_7282596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_7282596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282596 prefixEnd_7282596 := by exact prefixLift 7282596
  have htrace : WordTrace (prefixWord ++ tailWord_7282596) baseStart_7282596 baseEnd_7282596 := by
    simpa [prefixWord, tailWord_7282596, baseEnd_7282596] using wordTrace_append hprefix tailTrace_7282596
  have hstable : (prefixWord ++ tailWord_7282596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282596).length < 2 ^ (prefixWord ++ tailWord_7282596).sum := by decide
  have hdescent : baseEnd_7282596 < baseStart_7282596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282613 : List Nat := [1, 3, 3, 2, 1, 3, 3, 2, 1, 1, 3]
def baseStart_7282613 : Nat := 118140960795 + 7282613 * 2 ^ 59
def prefixEnd_7282613 : Nat := 4983230072969 + 3 ^ 40 * 7282613 * 2
def baseEnd_7282613 : Nat := 3739480889681820476845379

theorem tailTrace_7282613 : CollatzResearch.WordTrace tailWord_7282613 prefixEnd_7282613 3739480889681820476845379 := by
  unfold tailWord_7282613
  simp only [CollatzResearch.WordTrace]
  refine ⟨265618717565344347123820493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177079145043562898082546995 265618717565344347123820493)
  ·
    refine ⟨99607019087004130171432685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265618717565344347123820493 99607019087004130171432685)
    ·
      refine ⟨37352632157626548814287257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99607019087004130171432685 37352632157626548814287257)
      ·
        refine ⟨28014474118219911610715443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37352632157626548814287257 28014474118219911610715443)
        ·
          refine ⟨42021711177329867416073165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28014474118219911610715443 42021711177329867416073165)
          ·
            refine ⟨15758141691498700281027437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42021711177329867416073165 15758141691498700281027437)
            ·
              refine ⟨5909303134312012605385289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15758141691498700281027437 5909303134312012605385289)
              ·
                refine ⟨4431977350734009454038967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5909303134312012605385289 4431977350734009454038967)
                ·
                  refine ⟨6647966026101014181058451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4431977350734009454038967 6647966026101014181058451)
                  ·
                    refine ⟨9971949039151521271587677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6647966026101014181058451 9971949039151521271587677)
                    ·
                      refine ⟨3739480889681820476845379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9971949039151521271587677 3739480889681820476845379)
                      ·
                        rfl

theorem cell23_7282613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_7282613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282613 prefixEnd_7282613 := by exact prefixLift 7282613
  have htrace : WordTrace (prefixWord ++ tailWord_7282613) baseStart_7282613 baseEnd_7282613 := by
    simpa [prefixWord, tailWord_7282613, baseEnd_7282613] using wordTrace_append hprefix tailTrace_7282613
  have hstable : (prefixWord ++ tailWord_7282613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282613).length < 2 ^ (prefixWord ++ tailWord_7282613).sum := by decide
  have hdescent : baseEnd_7282613 < baseStart_7282613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282622 : List Nat := [4, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5]
def baseStart_7282622 : Nat := 118140960795 + 7282622 * 2 ^ 59
def prefixEnd_7282622 : Nat := 4983230072969 + 3 ^ 40 * 7282622 * 2
def baseEnd_7282622 : Nat := 3739485511007710941632837

theorem tailTrace_7282622 : CollatzResearch.WordTrace tailWord_7282622 prefixEnd_7282622 3739485511007710941632837 := by
  unfold tailWord_7282622
  simp only [CollatzResearch.WordTrace]
  refine ⟨33202380727788967707612265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177079363881541161107265413 33202380727788967707612265)
  ·
    refine ⟨24901785545841725780709199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33202380727788967707612265 24901785545841725780709199)
    ·
      refine ⟨37352678318762588671063799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24901785545841725780709199 37352678318762588671063799)
      ·
        refine ⟨56029017478143883006595699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37352678318762588671063799 56029017478143883006595699)
        ·
          refine ⟨84043526217215824509893549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56029017478143883006595699 84043526217215824509893549)
          ·
            refine ⟨31516322331455934191210081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84043526217215824509893549 31516322331455934191210081)
            ·
              refine ⟨23637241748591950643407561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31516322331455934191210081 23637241748591950643407561)
              ·
                refine ⟨17727931311443962982555671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23637241748591950643407561 17727931311443962982555671)
                ·
                  refine ⟨26591896967165944473833507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17727931311443962982555671 26591896967165944473833507)
                  ·
                    refine ⟨39887845450748916710750261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26591896967165944473833507 39887845450748916710750261)
                    ·
                      refine ⟨3739485511007710941632837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39887845450748916710750261 3739485511007710941632837)
                      ·
                        rfl

theorem cell23_7282622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_7282622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282622 prefixEnd_7282622 := by exact prefixLift 7282622
  have htrace : WordTrace (prefixWord ++ tailWord_7282622) baseStart_7282622 baseEnd_7282622 := by
    simpa [prefixWord, tailWord_7282622, baseEnd_7282622] using wordTrace_append hprefix tailTrace_7282622
  have hstable : (prefixWord ++ tailWord_7282622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282622).length < 2 ^ (prefixWord ++ tailWord_7282622).sum := by decide
  have hdescent : baseEnd_7282622 < baseStart_7282622 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282670 : List Nat := [4, 1, 2, 1, 3, 1, 4, 2, 1, 2, 2]
def baseStart_7282670 : Nat := 118140960795 + 7282670 * 2 ^ 59
def prefixEnd_7282670 : Nat := 4983230072969 + 3 ^ 40 * 7282670 * 2
def baseEnd_7282670 : Nat := 3739510158079126753832617

theorem tailTrace_7282670 : CollatzResearch.WordTrace tailWord_7282670 prefixEnd_7282670 3739510158079126753832617 := by
  unfold tailWord_7282670
  simp only [CollatzResearch.WordTrace]
  refine ⟨33202599565767230732330683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177080531017425230572430309 33202599565767230732330683)
  ·
    refine ⟨49803899348650846098496025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33202599565767230732330683 49803899348650846098496025)
    ·
      refine ⟨37352924511488134573872019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49803899348650846098496025 37352924511488134573872019)
      ·
        refine ⟨56029386767232201860808029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37352924511488134573872019 56029386767232201860808029)
        ·
          refine ⟨21011020037712075697803011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56029386767232201860808029 21011020037712075697803011)
          ·
            refine ⟨31516530056568113546704517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21011020037712075697803011 31516530056568113546704517)
            ·
              refine ⟨5909349385606521290007097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31516530056568113546704517 5909349385606521290007097)
              ·
                refine ⟨4432012039204890967505323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5909349385606521290007097 4432012039204890967505323)
                ·
                  refine ⟨6648018058807336451257985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4432012039204890967505323 6648018058807336451257985)
                  ·
                    refine ⟨4986013544105502338443489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6648018058807336451257985 4986013544105502338443489)
                    ·
                      refine ⟨3739510158079126753832617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4986013544105502338443489 3739510158079126753832617)
                      ·
                        rfl

theorem cell23_7282670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_7282670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282670 prefixEnd_7282670 := by exact prefixLift 7282670
  have htrace : WordTrace (prefixWord ++ tailWord_7282670) baseStart_7282670 baseEnd_7282670 := by
    simpa [prefixWord, tailWord_7282670, baseEnd_7282670] using wordTrace_append hprefix tailTrace_7282670
  have hstable : (prefixWord ++ tailWord_7282670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282670).length < 2 ^ (prefixWord ++ tailWord_7282670).sum := by decide
  have hdescent : baseEnd_7282670 < baseStart_7282670 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282685 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 1, 8]
def baseStart_7282685 : Nat := 118140960795 + 7282685 * 2 ^ 59
def prefixEnd_7282685 : Nat := 4983230072969 + 3 ^ 40 * 7282685 * 2
def baseEnd_7282685 : Nat := 1246505953429648065048349

theorem tailTrace_7282685 : CollatzResearch.WordTrace tailWord_7282685 prefixEnd_7282685 1246505953429648065048349 := by
  unfold tailWord_7282685
  simp only [CollatzResearch.WordTrace]
  refine ⟨265621343621083503420441509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177080895747389002280294339 265621343621083503420441509)
  ·
    refine ⟨49804001928953156891332783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265621343621083503420441509 49804001928953156891332783)
    ·
      refine ⟨74706002893429735336999175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49804001928953156891332783 74706002893429735336999175)
      ·
        refine ⟨112059004340144603005498763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74706002893429735336999175 112059004340144603005498763)
        ·
          refine ⟨168088506510216904508248145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112059004340144603005498763 168088506510216904508248145)
          ·
            refine ⟨126066379882662678381186109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168088506510216904508248145 126066379882662678381186109)
            ·
              refine ⟨47274892455998504392944791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126066379882662678381186109 47274892455998504392944791)
              ·
                refine ⟨70912338683997756589417187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47274892455998504392944791 70912338683997756589417187)
                ·
                  refine ⟨106368508025996634884125781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70912338683997756589417187 106368508025996634884125781)
                  ·
                    refine ⟨1246505953429648065048349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 106368508025996634884125781 1246505953429648065048349)
                    ·
                      rfl

theorem cell23_7282685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_7282685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282685 prefixEnd_7282685 := by exact prefixLift 7282685
  have htrace : WordTrace (prefixWord ++ tailWord_7282685) baseStart_7282685 baseEnd_7282685 := by
    simpa [prefixWord, tailWord_7282685, baseEnd_7282685] using wordTrace_append hprefix tailTrace_7282685
  have hstable : (prefixWord ++ tailWord_7282685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282685).length < 2 ^ (prefixWord ++ tailWord_7282685).sum := by decide
  have hdescent : baseEnd_7282685 < baseStart_7282685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282686 : List Nat := [4, 2, 2, 2, 1, 2, 2, 1, 1, 3, 3]
def baseStart_7282686 : Nat := 118140960795 + 7282686 * 2 ^ 59
def prefixEnd_7282686 : Nat := 4983230072969 + 3 ^ 40 * 7282686 * 2
def baseEnd_7282686 : Nat := 3739518373769598691232543

theorem tailTrace_7282686 : CollatzResearch.WordTrace tailWord_7282686 prefixEnd_7282686 3739518373769598691232543 := by
  unfold tailWord_7282686
  simp only [CollatzResearch.WordTrace]
  refine ⟨33202672511759985073903489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177080920062719920394151941 33202672511759985073903489)
  ·
    refine ⟨24902004383819988805427617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33202672511759985073903489 24902004383819988805427617)
    ·
      refine ⟨18676503287864991604070713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24902004383819988805427617 18676503287864991604070713)
      ·
        refine ⟨14007377465898743703053035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18676503287864991604070713 14007377465898743703053035)
        ·
          refine ⟨21011066198848115554579553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14007377465898743703053035 21011066198848115554579553)
          ·
            refine ⟨15758299649136086665934665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21011066198848115554579553 15758299649136086665934665)
            ·
              refine ⟨11818724736852064999450999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15758299649136086665934665 11818724736852064999450999)
              ·
                refine ⟨17728087105278097499176499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11818724736852064999450999 17728087105278097499176499)
                ·
                  refine ⟨26592130657917146248764749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17728087105278097499176499 26592130657917146248764749)
                  ·
                    refine ⟨9972048996718929843286781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26592130657917146248764749 9972048996718929843286781)
                    ·
                      refine ⟨3739518373769598691232543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9972048996718929843286781 3739518373769598691232543)
                      ·
                        rfl

theorem cell23_7282686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_7282686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282686 prefixEnd_7282686 := by exact prefixLift 7282686
  have htrace : WordTrace (prefixWord ++ tailWord_7282686) baseStart_7282686 baseEnd_7282686 := by
    simpa [prefixWord, tailWord_7282686, baseEnd_7282686] using wordTrace_append hprefix tailTrace_7282686
  have hstable : (prefixWord ++ tailWord_7282686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282686).length < 2 ^ (prefixWord ++ tailWord_7282686).sum := by decide
  have hdescent : baseEnd_7282686 < baseStart_7282686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282722 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 4, 2, 4]
def baseStart_7282722 : Nat := 118140960795 + 7282722 * 2 ^ 59
def prefixEnd_7282722 : Nat := 4983230072969 + 3 ^ 40 * 7282722 * 2
def baseEnd_7282722 : Nat := 3739536859073160550382377

theorem tailTrace_7282722 : CollatzResearch.WordTrace tailWord_7282722 prefixEnd_7282722 3739536859073160550382377 := by
  unfold tailWord_7282722
  simp only [CollatzResearch.WordTrace]
  refine ⟨66405673280487364684884605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177081795414632972493025613 66405673280487364684884605)
  ·
    refine ⟨24902127480182761756831727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66405673280487364684884605 24902127480182761756831727)
    ·
      refine ⟨37353191220274142635247591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24902127480182761756831727 37353191220274142635247591)
      ·
        refine ⟨56029786830411213952871387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37353191220274142635247591 56029786830411213952871387)
        ·
          refine ⟨84044680245616820929307081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56029786830411213952871387 84044680245616820929307081)
          ·
            refine ⟨63033510184212615696980311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84044680245616820929307081 63033510184212615696980311)
            ·
              refine ⟨94550265276318923545470467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63033510184212615696980311 94550265276318923545470467)
              ·
                refine ⟨141825397914478385318205701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94550265276318923545470467 141825397914478385318205701)
                ·
                  refine ⟨26592262108964697247163569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141825397914478385318205701 26592262108964697247163569)
                  ·
                    refine ⟨19944196581723522935372677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26592262108964697247163569 19944196581723522935372677)
                    ·
                      refine ⟨3739536859073160550382377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19944196581723522935372677 3739536859073160550382377)
                      ·
                        rfl

theorem cell23_7282722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_7282722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282722 prefixEnd_7282722 := by exact prefixLift 7282722
  have htrace : WordTrace (prefixWord ++ tailWord_7282722) baseStart_7282722 baseEnd_7282722 := by
    simpa [prefixWord, tailWord_7282722, baseEnd_7282722] using wordTrace_append hprefix tailTrace_7282722
  have hstable : (prefixWord ++ tailWord_7282722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282722).length < 2 ^ (prefixWord ++ tailWord_7282722).sum := by decide
  have hdescent : baseEnd_7282722 < baseStart_7282722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282755 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 7]
def baseStart_7282755 : Nat := 118140960795 + 7282755 * 2 ^ 59
def prefixEnd_7282755 : Nat := 4983230072969 + 3 ^ 40 * 7282755 * 2
def baseEnd_7282755 : Nat := 3739553803934758921269725

theorem tailTrace_7282755 : CollatzResearch.WordTrace tailWord_7282755 prefixEnd_7282755 3739553803934758921269725 := by
  unfold tailWord_7282755
  simp only [CollatzResearch.WordTrace]
  refine ⟨265623896730829905375489719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177082597820553270250326479 265623896730829905375489719)
  ·
    refine ⟨398435845096244858063234579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265623896730829905375489719 398435845096244858063234579)
    ·
      refine ⟨597653767644367287094851869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398435845096244858063234579 597653767644367287094851869)
      ·
        refine ⟨224120162866637732660569451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 597653767644367287094851869 224120162866637732660569451)
        ·
          refine ⟨336180244299956598990854177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224120162866637732660569451 336180244299956598990854177)
          ·
            refine ⟨252135183224967449243140633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336180244299956598990854177 252135183224967449243140633)
            ·
              refine ⟨189101387418725586932355475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252135183224967449243140633 189101387418725586932355475)
              ·
                refine ⟨283652081128088380398533213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189101387418725586932355475 283652081128088380398533213)
                ·
                  refine ⟨106369530423033142649449955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 283652081128088380398533213 106369530423033142649449955)
                  ·
                    refine ⟨159554295634549713974174933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106369530423033142649449955 159554295634549713974174933)
                    ·
                      refine ⟨3739553803934758921269725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 159554295634549713974174933 3739553803934758921269725)
                      ·
                        rfl

theorem cell23_7282755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_7282755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282755 prefixEnd_7282755 := by exact prefixLift 7282755
  have htrace : WordTrace (prefixWord ++ tailWord_7282755) baseStart_7282755 baseEnd_7282755 := by
    simpa [prefixWord, tailWord_7282755, baseEnd_7282755] using wordTrace_append hprefix tailTrace_7282755
  have hstable : (prefixWord ++ tailWord_7282755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282755).length < 2 ^ (prefixWord ++ tailWord_7282755).sum := by decide
  have hdescent : baseEnd_7282755 < baseStart_7282755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282762 : List Nat := [3, 1, 2, 1, 1, 2, 1, 5, 2, 5]
def baseStart_7282762 : Nat := 118140960795 + 7282762 * 2 ^ 59
def prefixEnd_7282762 : Nat := 4983230072969 + 3 ^ 40 * 7282762 * 2
def baseEnd_7282762 : Nat := 1246519132766446797960731

theorem tailTrace_7282762 : CollatzResearch.WordTrace tailWord_7282762 prefixEnd_7282762 1246519132766446797960731 := by
  unfold tailWord_7282762
  simp only [CollatzResearch.WordTrace]
  refine ⟨66406038010451136392748635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177082768027869697047329693 66406038010451136392748635)
  ·
    refine ⟨99609057015676704589122953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66406038010451136392748635 99609057015676704589122953)
    ·
      refine ⟨74706792761757528441842215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99609057015676704589122953 74706792761757528441842215)
      ·
        refine ⟨112060189142636292662763323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74706792761757528441842215 112060189142636292662763323)
        ·
          refine ⟨168090283713954438994144985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112060189142636292662763323 168090283713954438994144985)
          ·
            refine ⟨126067712785465829245608739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168090283713954438994144985 126067712785465829245608739)
            ·
              refine ⟨189101569178198743868413109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126067712785465829245608739 189101569178198743868413109)
              ·
                refine ⟨17728272110456132237663729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 189101569178198743868413109 17728272110456132237663729)
                ·
                  refine ⟨13296204082842099178247797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17728272110456132237663729 13296204082842099178247797)
                  ·
                    refine ⟨1246519132766446797960731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13296204082842099178247797 1246519132766446797960731)
                    ·
                      rfl

theorem cell23_7282762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_7282762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282762 prefixEnd_7282762 := by exact prefixLift 7282762
  have htrace : WordTrace (prefixWord ++ tailWord_7282762) baseStart_7282762 baseEnd_7282762 := by
    simpa [prefixWord, tailWord_7282762, baseEnd_7282762] using wordTrace_append hprefix tailTrace_7282762
  have hstable : (prefixWord ++ tailWord_7282762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282762).length < 2 ^ (prefixWord ++ tailWord_7282762).sum := by decide
  have hdescent : baseEnd_7282762 < baseStart_7282762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
