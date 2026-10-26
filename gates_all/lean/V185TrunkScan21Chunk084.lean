import V185TrunkScan21Chunk083

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1019745 : List Nat := [1, 2, 3, 1, 1, 1, 4, 8]
def baseStart_1019745 : Nat := 118140960795 + 1019745 * 2 ^ 59
def prefixEnd_1019745 : Nat := 4983230072969 + 3 ^ 40 * 1019745 * 2
def baseEnd_1019745 : Nat := 77573234076921181733005

theorem tailTrace_1019745 : CollatzResearch.WordTrace tailWord_1019745 prefixEnd_1019745 77573234076921181733005 := by
  unfold tailWord_1019745
  simp only [CollatzResearch.WordTrace]
  refine ⟨37193155690645498425636689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24795437127096998950424459 37193155690645498425636689)
  ·
    refine ⟨27894866767984123819227517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37193155690645498425636689 27894866767984123819227517)
    ·
      refine ⟨10460575037994046432210319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27894866767984123819227517 10460575037994046432210319)
      ·
        refine ⟨15690862556991069648315479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10460575037994046432210319 15690862556991069648315479)
        ·
          refine ⟨23536293835486604472473219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15690862556991069648315479 23536293835486604472473219)
          ·
            refine ⟨35304440753229906708709829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23536293835486604472473219 35304440753229906708709829)
            ·
              refine ⟨6619582641230607507883093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35304440753229906708709829 6619582641230607507883093)
              ·
                refine ⟨77573234076921181733005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6619582641230607507883093 77573234076921181733005)
                ·
                  rfl

theorem cell21_1019745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 8].length) (baseStart_1019745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1019745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1019745 prefixEnd_1019745 := by exact prefixLift 1019745
  have htrace : WordTrace (prefixWord ++ tailWord_1019745) baseStart_1019745 baseEnd_1019745 := by
    simpa [prefixWord, tailWord_1019745, baseEnd_1019745] using wordTrace_append hprefix tailTrace_1019745
  have hstable : (prefixWord ++ tailWord_1019745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019745).length < 2 ^ (prefixWord ++ tailWord_1019745).sum := by decide
  have hdescent : baseEnd_1019745 < baseStart_1019745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019793 : List Nat := [1, 2, 2, 1, 1, 1, 4, 6, 3]
def baseStart_1019793 : Nat := 118140960795 + 1019793 * 2 ^ 59
def prefixEnd_1019793 : Nat := 4983230072969 + 3 ^ 40 * 1019793 * 2
def baseEnd_1019793 : Nat := 232730656484726128398917

theorem tailTrace_1019793 : CollatzResearch.WordTrace tailWord_1019793 prefixEnd_1019793 232730656484726128398917 := by
  unfold tailWord_1019793
  simp only [CollatzResearch.WordTrace]
  refine ⟨37194906394471602623384033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24796604262981068415589355 37194906394471602623384033)
  ·
    refine ⟨27896179795853701967538025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37194906394471602623384033 27896179795853701967538025)
    ·
      refine ⟨20922134846890276475653519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27896179795853701967538025 20922134846890276475653519)
      ·
        refine ⟨31383202270335414713480279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20922134846890276475653519 31383202270335414713480279)
        ·
          refine ⟨47074803405503122070220419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31383202270335414713480279 47074803405503122070220419)
          ·
            refine ⟨70612205108254683105330629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47074803405503122070220419 70612205108254683105330629)
            ·
              refine ⟨13239788457797753082249493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70612205108254683105330629 13239788457797753082249493)
              ·
                refine ⟨620615083959269675730445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13239788457797753082249493 620615083959269675730445)
                ·
                  refine ⟨232730656484726128398917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 620615083959269675730445 232730656484726128398917)
                  ·
                    rfl

theorem cell21_1019793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 6, 3].length) (baseStart_1019793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1019793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1019793 prefixEnd_1019793 := by exact prefixLift 1019793
  have htrace : WordTrace (prefixWord ++ tailWord_1019793) baseStart_1019793 baseEnd_1019793 := by
    simpa [prefixWord, tailWord_1019793, baseEnd_1019793] using wordTrace_append hprefix tailTrace_1019793
  have hstable : (prefixWord ++ tailWord_1019793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019793).length < 2 ^ (prefixWord ++ tailWord_1019793).sum := by decide
  have hdescent : baseEnd_1019793 < baseStart_1019793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019886 : List Nat := [4, 1, 2, 1, 3, 1, 1, 5, 3]
def baseStart_1019886 : Nat := 118140960795 + 1019886 * 2 ^ 59
def prefixEnd_1019886 : Nat := 4983230072969 + 3 ^ 40 * 1019886 * 2
def baseEnd_1019886 : Nat := 232751880351778633348727

theorem tailTrace_1019886 : CollatzResearch.WordTrace tailWord_1019886 prefixEnd_1019886 232751880351778633348727 := by
  unfold tailWord_1019886
  simp only [CollatzResearch.WordTrace]
  refine ⟨4649787297891834938314939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24798865588756453004346341 4649787297891834938314939)
  ·
    refine ⟨6974680946837752407472409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4649787297891834938314939 6974680946837752407472409)
    ·
      refine ⟨5231010710128314305604307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6974680946837752407472409 5231010710128314305604307)
      ·
        refine ⟨7846516065192471458406461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5231010710128314305604307 7846516065192471458406461)
        ·
          refine ⟨2942443524447176796902423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7846516065192471458406461 2942443524447176796902423)
          ·
            refine ⟨4413665286670765195353635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2942443524447176796902423 4413665286670765195353635)
            ·
              refine ⟨6620497930006147793030453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4413665286670765195353635 6620497930006147793030453)
              ·
                refine ⟨620671680938076355596605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6620497930006147793030453 620671680938076355596605)
                ·
                  refine ⟨232751880351778633348727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 620671680938076355596605 232751880351778633348727)
                  ·
                    rfl

theorem cell21_1019886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_1019886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1019886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1019886 prefixEnd_1019886 := by exact prefixLift 1019886
  have htrace : WordTrace (prefixWord ++ tailWord_1019886) baseStart_1019886 baseEnd_1019886 := by
    simpa [prefixWord, tailWord_1019886, baseEnd_1019886] using wordTrace_append hprefix tailTrace_1019886
  have hstable : (prefixWord ++ tailWord_1019886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019886).length < 2 ^ (prefixWord ++ tailWord_1019886).sum := by decide
  have hdescent : baseEnd_1019886 < baseStart_1019886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019897 : List Nat := [1, 2, 1, 3, 1, 5, 8]
def baseStart_1019897 : Nat := 118140960795 + 1019897 * 2 ^ 59
def prefixEnd_1019897 : Nat := 4983230072969 + 3 ^ 40 * 1019897 * 2
def baseEnd_1019897 : Nat := 25861598966849450962819

theorem tailTrace_1019897 : CollatzResearch.WordTrace tailWord_1019897 prefixEnd_1019897 25861598966849450962819 := by
  unfold tailWord_1019897
  simp only [CollatzResearch.WordTrace]
  refine ⟨37198699586094828385169945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24799133057396552256779963 37198699586094828385169945)
  ·
    refine ⟨27899024689571121288877459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37198699586094828385169945 27899024689571121288877459)
    ·
      refine ⟨41848537034356681933316189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27899024689571121288877459 41848537034356681933316189)
      ·
        refine ⟨15693201387883755724993571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41848537034356681933316189 15693201387883755724993571)
        ·
          refine ⟨23539802081825633587490357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15693201387883755724993571 23539802081825633587490357)
          ·
            refine ⟨2206856445171153148827221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23539802081825633587490357 2206856445171153148827221)
            ·
              refine ⟨25861598966849450962819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2206856445171153148827221 25861598966849450962819)
              ·
                rfl

theorem cell21_1019897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 8].length) (baseStart_1019897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1019897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1019897 prefixEnd_1019897 := by exact prefixLift 1019897
  have htrace : WordTrace (prefixWord ++ tailWord_1019897) baseStart_1019897 baseEnd_1019897 := by
    simpa [prefixWord, tailWord_1019897, baseEnd_1019897] using wordTrace_append hprefix tailTrace_1019897
  have hstable : (prefixWord ++ tailWord_1019897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019897).length < 2 ^ (prefixWord ++ tailWord_1019897).sum := by decide
  have hdescent : baseEnd_1019897 < baseStart_1019897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019928 : List Nat := [2, 1, 2, 3, 2, 1, 1, 4, 5]
def baseStart_1019928 : Nat := 118140960795 + 1019928 * 2 ^ 59
def prefixEnd_1019928 : Nat := 4983230072969 + 3 ^ 40 * 1019928 * 2
def baseEnd_1019928 : Nat := 232761465323995893648641

theorem tailTrace_1019928 : CollatzResearch.WordTrace tailWord_1019928 prefixEnd_1019928 232761465323995893648641 := by
  unfold tailWord_1019928
  simp only [CollatzResearch.WordTrace]
  refine ⟨18599915124491260339774219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24799886832655013786365625 18599915124491260339774219)
  ·
    refine ⟨27899872686736890509661329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18599915124491260339774219 27899872686736890509661329)
    ·
      refine ⟨20924904515052667882245997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27899872686736890509661329 20924904515052667882245997)
      ·
        refine ⟨7846839193144750455842249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20924904515052667882245997 7846839193144750455842249)
        ·
          refine ⟨5885129394858562841881687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7846839193144750455842249 5885129394858562841881687)
          ·
            refine ⟨8827694092287844262822531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5885129394858562841881687 8827694092287844262822531)
            ·
              refine ⟨13241541138431766394233797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8827694092287844262822531 13241541138431766394233797)
              ·
                refine ⟨2482788963455956198918837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13241541138431766394233797 2482788963455956198918837)
                ·
                  refine ⟨232761465323995893648641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2482788963455956198918837 232761465323995893648641)
                  ·
                    rfl

theorem cell21_1019928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 5].length) (baseStart_1019928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1019928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1019928 prefixEnd_1019928 := by exact prefixLift 1019928
  have htrace : WordTrace (prefixWord ++ tailWord_1019928) baseStart_1019928 baseEnd_1019928 := by
    simpa [prefixWord, tailWord_1019928, baseEnd_1019928] using wordTrace_append hprefix tailTrace_1019928
  have hstable : (prefixWord ++ tailWord_1019928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019928).length < 2 ^ (prefixWord ++ tailWord_1019928).sum := by decide
  have hdescent : baseEnd_1019928 < baseStart_1019928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020035 : List Nat := [1, 1, 1, 3, 3, 3, 2, 3, 4]
def baseStart_1020035 : Nat := 118140960795 + 1020035 * 2 ^ 59
def prefixEnd_1020035 : Nat := 4983230072969 + 3 ^ 40 * 1020035 * 2
def baseEnd_1020035 : Nat := 232785884181787485365089

theorem tailTrace_1020035 : CollatzResearch.WordTrace tailWord_1020035 prefixEnd_1020035 232785884181787485365089 := by
  unfold tailWord_1020035
  simp only [CollatzResearch.WordTrace]
  refine ⟨37203732859594877953693559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24802488573063251969129039 37203732859594877953693559)
  ·
    refine ⟨55805599289392316930540339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37203732859594877953693559 55805599289392316930540339)
    ·
      refine ⟨83708398934088475395810509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55805599289392316930540339 83708398934088475395810509)
      ·
        refine ⟨31390649600283178273428941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83708398934088475395810509 31390649600283178273428941)
        ·
          refine ⟨11771493600106191852535853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31390649600283178273428941 11771493600106191852535853)
          ·
            refine ⟨4414310100039821944700945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11771493600106191852535853 4414310100039821944700945)
            ·
              refine ⟨3310732575029866458525709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4414310100039821944700945 3310732575029866458525709)
              ·
                refine ⟨1241524715636199921947141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3310732575029866458525709 1241524715636199921947141)
                ·
                  refine ⟨232785884181787485365089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1241524715636199921947141 232785884181787485365089)
                  ·
                    rfl

theorem cell21_1020035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 4].length) (baseStart_1020035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1020035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1020035 prefixEnd_1020035 := by exact prefixLift 1020035
  have htrace : WordTrace (prefixWord ++ tailWord_1020035) baseStart_1020035 baseEnd_1020035 := by
    simpa [prefixWord, tailWord_1020035, baseEnd_1020035] using wordTrace_append hprefix tailTrace_1020035
  have hstable : (prefixWord ++ tailWord_1020035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020035).length < 2 ^ (prefixWord ++ tailWord_1020035).sum := by decide
  have hdescent : baseEnd_1020035 < baseStart_1020035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020066 : List Nat := [3, 3, 1, 3, 1, 2, 8]
def baseStart_1020066 : Nat := 118140960795 + 1020066 * 2 ^ 59
def prefixEnd_1020066 : Nat := 4983230072969 + 3 ^ 40 * 1020066 * 2
def baseEnd_1020066 : Nat := 25865884311570924483151

theorem tailTrace_1020066 : CollatzResearch.WordTrace tailWord_1020066 prefixEnd_1020066 25865884311570924483151 := by
  unfold tailWord_1020066
  simp only [CollatzResearch.WordTrace]
  refine ⟨9301215880620642562018013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24803242348321713498714701 9301215880620642562018013)
  ·
    refine ⟨3487955955232740960756755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9301215880620642562018013 3487955955232740960756755)
    ·
      refine ⟨5231933932849111441135133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3487955955232740960756755 5231933932849111441135133)
      ·
        refine ⟨1961975224818416790425675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5231933932849111441135133 1961975224818416790425675)
        ·
          refine ⟨2942962837227625185638513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1961975224818416790425675 2942962837227625185638513)
          ·
            refine ⟨2207222127920718889228885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2942962837227625185638513 2207222127920718889228885)
            ·
              refine ⟨25865884311570924483151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2207222127920718889228885 25865884311570924483151)
              ·
                rfl

theorem cell21_1020066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 8].length) (baseStart_1020066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1020066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1020066 prefixEnd_1020066 := by exact prefixLift 1020066
  have htrace : WordTrace (prefixWord ++ tailWord_1020066) baseStart_1020066 baseEnd_1020066 := by
    simpa [prefixWord, tailWord_1020066, baseEnd_1020066] using wordTrace_append hprefix tailTrace_1020066
  have hstable : (prefixWord ++ tailWord_1020066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020066).length < 2 ^ (prefixWord ++ tailWord_1020066).sum := by decide
  have hdescent : baseEnd_1020066 < baseStart_1020066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020114 : List Nat := [3, 2, 2, 2, 1, 2, 3, 3, 3]
def baseStart_1020114 : Nat := 118140960795 + 1020114 * 2 ^ 59
def prefixEnd_1020114 : Nat := 4983230072969 + 3 ^ 40 * 1020114 * 2
def baseEnd_1020114 : Nat := 232803913058100903548261

theorem tailTrace_1020114 : CollatzResearch.WordTrace tailWord_1020114 prefixEnd_1020114 232803913058100903548261 := by
  unfold tailWord_1020114
  simp only [CollatzResearch.WordTrace]
  refine ⟨9301653556577168611454849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24804409484205782963879597 9301653556577168611454849)
  ·
    refine ⟨6976240167432876458591137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9301653556577168611454849 6976240167432876458591137)
    ·
      refine ⟨5232180125574657343943353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6976240167432876458591137 5232180125574657343943353)
      ·
        refine ⟨3924135094180993007957515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5232180125574657343943353 3924135094180993007957515)
        ·
          refine ⟨5886202641271489511936273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3924135094180993007957515 5886202641271489511936273)
          ·
            refine ⟨4414651980953617133952205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5886202641271489511936273 4414651980953617133952205)
            ·
              refine ⟨1655494492857606425232077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4414651980953617133952205 1655494492857606425232077)
              ·
                refine ⟨620810434821602409462029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1655494492857606425232077 620810434821602409462029)
                ·
                  refine ⟨232803913058100903548261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 620810434821602409462029 232803913058100903548261)
                  ·
                    rfl

theorem cell21_1020114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_1020114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1020114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1020114 prefixEnd_1020114 := by exact prefixLift 1020114
  have htrace : WordTrace (prefixWord ++ tailWord_1020114) baseStart_1020114 baseEnd_1020114 := by
    simpa [prefixWord, tailWord_1020114, baseEnd_1020114] using wordTrace_append hprefix tailTrace_1020114
  have hstable : (prefixWord ++ tailWord_1020114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020114).length < 2 ^ (prefixWord ++ tailWord_1020114).sum := by decide
  have hdescent : baseEnd_1020114 < baseStart_1020114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020131 : List Nat := [1, 1, 1, 8, 2, 1, 1, 1, 5]
def baseStart_1020131 : Nat := 118140960795 + 1020131 * 2 ^ 59
def prefixEnd_1020131 : Nat := 4983230072969 + 3 ^ 40 * 1020131 * 2
def baseEnd_1020131 : Nat := 232807792689712651764893

theorem tailTrace_1020131 : CollatzResearch.WordTrace tailWord_1020131 prefixEnd_1020131 232807792689712651764893 := by
  unfold tailWord_1020131
  simp only [CollatzResearch.WordTrace]
  refine ⟨37207234267247086349188247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24804822844831390899458831 37207234267247086349188247)
  ·
    refine ⟨55810851400870629523782371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37207234267247086349188247 55810851400870629523782371)
    ·
      refine ⟨83716277101305944285673557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55810851400870629523782371 83716277101305944285673557)
      ·
        refine ⟨981050122280929034597737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 83716277101305944285673557 981050122280929034597737)
        ·
          refine ⟨735787591710696775948303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 981050122280929034597737 735787591710696775948303)
          ·
            refine ⟨1103681387566045163922455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735787591710696775948303 1103681387566045163922455)
            ·
              refine ⟨1655522081349067745883683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1103681387566045163922455 1655522081349067745883683)
              ·
                refine ⟨2483283122023601618825525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1655522081349067745883683 2483283122023601618825525)
                ·
                  refine ⟨232807792689712651764893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2483283122023601618825525 232807792689712651764893)
                  ·
                    rfl

theorem cell21_1020131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 5].length) (baseStart_1020131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1020131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1020131 prefixEnd_1020131 := by exact prefixLift 1020131
  have htrace : WordTrace (prefixWord ++ tailWord_1020131) baseStart_1020131 baseEnd_1020131 := by
    simpa [prefixWord, tailWord_1020131, baseEnd_1020131] using wordTrace_append hprefix tailTrace_1020131
  have hstable : (prefixWord ++ tailWord_1020131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020131).length < 2 ^ (prefixWord ++ tailWord_1020131).sum := by decide
  have hdescent : baseEnd_1020131 < baseStart_1020131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020170 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 8]
def baseStart_1020170 : Nat := 118140960795 + 1020170 * 2 ^ 59
def prefixEnd_1020170 : Nat := 4983230072969 + 3 ^ 40 * 1020170 * 2
def baseEnd_1020170 : Nat := 232816693021057250614813

theorem tailTrace_1020170 : CollatzResearch.WordTrace tailWord_1020170 prefixEnd_1020170 232816693021057250614813 := by
  unfold tailWord_1020170
  simp only [CollatzResearch.WordTrace]
  refine ⟨9302164178526449002464491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24805771142737197339905309 9302164178526449002464491)
  ·
    refine ⟨13953246267789673503696737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9302164178526449002464491 13953246267789673503696737)
    ·
      refine ⟨10464934700842255127772553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13953246267789673503696737 10464934700842255127772553)
      ·
        refine ⟨7848701025631691345829415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10464934700842255127772553 7848701025631691345829415)
        ·
          refine ⟨11773051538447537018744123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7848701025631691345829415 11773051538447537018744123)
          ·
            refine ⟨17659577307671305528116185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11773051538447537018744123 17659577307671305528116185)
            ·
              refine ⟨13244682980753479146087139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17659577307671305528116185 13244682980753479146087139)
              ·
                refine ⟨19867024471130218719130709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13244682980753479146087139 19867024471130218719130709)
                ·
                  refine ⟨232816693021057250614813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19867024471130218719130709 232816693021057250614813)
                  ·
                    rfl

theorem cell21_1020170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_1020170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1020170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1020170 prefixEnd_1020170 := by exact prefixLift 1020170
  have htrace : WordTrace (prefixWord ++ tailWord_1020170) baseStart_1020170 baseEnd_1020170 := by
    simpa [prefixWord, tailWord_1020170, baseEnd_1020170] using wordTrace_append hprefix tailTrace_1020170
  have hstable : (prefixWord ++ tailWord_1020170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020170).length < 2 ^ (prefixWord ++ tailWord_1020170).sum := by decide
  have hdescent : baseEnd_1020170 < baseStart_1020170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020218 : List Nat := [3, 1, 1, 1, 4, 3, 3, 5]
def baseStart_1020218 : Nat := 118140960795 + 1020218 * 2 ^ 59
def prefixEnd_1020218 : Nat := 4983230072969 + 3 ^ 40 * 1020218 * 2
def baseEnd_1020218 : Nat := 77609215758339944604905

theorem tailTrace_1020218 : CollatzResearch.WordTrace tailWord_1020218 prefixEnd_1020218 77609215758339944604905 := by
  unfold tailWord_1020218
  simp only [CollatzResearch.WordTrace]
  refine ⟨9302601854482975051901327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24806938278621266805070205 9302601854482975051901327)
  ·
    refine ⟨13953902781724462577851991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9302601854482975051901327 13953902781724462577851991)
    ·
      refine ⟨20930854172586693866777987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13953902781724462577851991 20930854172586693866777987)
      ·
        refine ⟨31396281258880040800166981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20930854172586693866777987 31396281258880040800166981)
        ·
          refine ⟨5886802736040007650031309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31396281258880040800166981 5886802736040007650031309)
          ·
            refine ⟨2207551026015002868761741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5886802736040007650031309 2207551026015002868761741)
            ·
              refine ⟨827831634755626075785653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2207551026015002868761741 827831634755626075785653)
              ·
                refine ⟨77609215758339944604905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 827831634755626075785653 77609215758339944604905)
                ·
                  rfl

theorem cell21_1020218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 5].length) (baseStart_1020218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1020218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1020218 prefixEnd_1020218 := by exact prefixLift 1020218
  have htrace : WordTrace (prefixWord ++ tailWord_1020218) baseStart_1020218 baseEnd_1020218 := by
    simpa [prefixWord, tailWord_1020218, baseEnd_1020218] using wordTrace_append hprefix tailTrace_1020218
  have hstable : (prefixWord ++ tailWord_1020218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020218).length < 2 ^ (prefixWord ++ tailWord_1020218).sum := by decide
  have hdescent : baseEnd_1020218 < baseStart_1020218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020367 : List Nat := [1, 1, 2, 1, 1, 4, 1, 5, 5]
def baseStart_1020367 : Nat := 118140960795 + 1020367 * 2 ^ 59
def prefixEnd_1020367 : Nat := 4983230072969 + 3 ^ 40 * 1020367 * 2
def baseEnd_1020367 : Nat := 232861651105028685831077

theorem tailTrace_1020367 : CollatzResearch.WordTrace tailWord_1020367 prefixEnd_1020367 232861651105028685831077 := by
  unfold tailWord_1020367
  simp only [CollatzResearch.WordTrace]
  refine ⟨37215841894392098654779355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24810561262928065769852903 37215841894392098654779355)
  ·
    refine ⟨55823762841588147982169033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37215841894392098654779355 55823762841588147982169033)
    ·
      refine ⟨41867822131191110986626775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55823762841588147982169033 41867822131191110986626775)
      ·
        refine ⟨62801733196786666479940163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41867822131191110986626775 62801733196786666479940163)
        ·
          refine ⟨94202599795179999719910245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62801733196786666479940163 94202599795179999719910245)
          ·
            refine ⟨17662987461596249947483171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94202599795179999719910245 17662987461596249947483171)
            ·
              refine ⟨26494481192394374921224757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17662987461596249947483171 26494481192394374921224757)
              ·
                refine ⟨2483857611786972648864821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26494481192394374921224757 2483857611786972648864821)
                ·
                  refine ⟨232861651105028685831077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2483857611786972648864821 232861651105028685831077)
                  ·
                    rfl

theorem cell21_1020367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 5].length) (baseStart_1020367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1020367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1020367 prefixEnd_1020367 := by exact prefixLift 1020367
  have htrace : WordTrace (prefixWord ++ tailWord_1020367) baseStart_1020367 baseEnd_1020367 := by
    simpa [prefixWord, tailWord_1020367, baseEnd_1020367] using wordTrace_append hprefix tailTrace_1020367
  have hstable : (prefixWord ++ tailWord_1020367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020367).length < 2 ^ (prefixWord ++ tailWord_1020367).sum := by decide
  have hdescent : baseEnd_1020367 < baseStart_1020367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020401 : List Nat := [1, 2, 2, 2, 3, 1, 4, 3, 3]
def baseStart_1020401 : Nat := 118140960795 + 1020401 * 2 ^ 59
def prefixEnd_1020401 : Nat := 4983230072969 + 3 ^ 40 * 1020401 * 2
def baseEnd_1020401 : Nat := 232869410368252182264341

theorem tailTrace_1020401 : CollatzResearch.WordTrace tailWord_1020401 prefixEnd_1020401 232869410368252182264341 := by
  unfold tailWord_1020401
  simp only [CollatzResearch.WordTrace]
  refine ⟨37217081976268922461517057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24811387984179281641011371 37217081976268922461517057)
  ·
    refine ⟨27912811482201691846137793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37217081976268922461517057 27912811482201691846137793)
    ·
      refine ⟨20934608611651268884603345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27912811482201691846137793 20934608611651268884603345)
      ·
        refine ⟨15700956458738451663452509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20934608611651268884603345 15700956458738451663452509)
        ·
          refine ⟨5887858672026919373794691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15700956458738451663452509 5887858672026919373794691)
          ·
            refine ⟨8831788008040379060692037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5887858672026919373794691 8831788008040379060692037)
            ·
              refine ⟨1655960251507571073879757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8831788008040379060692037 1655960251507571073879757)
              ·
                refine ⟨620985094315339152704909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1655960251507571073879757 620985094315339152704909)
                ·
                  refine ⟨232869410368252182264341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 620985094315339152704909 232869410368252182264341)
                  ·
                    rfl

theorem cell21_1020401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 3, 3].length) (baseStart_1020401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1020401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1020401 prefixEnd_1020401 := by exact prefixLift 1020401
  have htrace : WordTrace (prefixWord ++ tailWord_1020401) baseStart_1020401 baseEnd_1020401 := by
    simpa [prefixWord, tailWord_1020401, baseEnd_1020401] using wordTrace_append hprefix tailTrace_1020401
  have hstable : (prefixWord ++ tailWord_1020401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020401).length < 2 ^ (prefixWord ++ tailWord_1020401).sum := by decide
  have hdescent : baseEnd_1020401 < baseStart_1020401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020418 : List Nat := [3, 4, 1, 2, 2, 1, 2, 1, 5]
def baseStart_1020418 : Nat := 118140960795 + 1020418 * 2 ^ 59
def prefixEnd_1020418 : Nat := 4983230072969 + 3 ^ 40 * 1020418 * 2
def baseEnd_1020418 : Nat := 232873289999863930480973

theorem tailTrace_1020418 : CollatzResearch.WordTrace tailWord_1020418 prefixEnd_1020418 232873289999863930480973 := by
  unfold tailWord_1020418
  simp only [CollatzResearch.WordTrace]
  refine ⟨9304425504301833591221477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24811801344804889576590605 9304425504301833591221477)
  ·
    refine ⟨1744579782056593798354027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9304425504301833591221477 1744579782056593798354027)
    ·
      refine ⟨2616869673084890697531041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1744579782056593798354027 2616869673084890697531041)
      ·
        refine ⟨1962652254813668023148281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2616869673084890697531041 1962652254813668023148281)
        ·
          refine ⟨1471989191110251017361211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1962652254813668023148281 1471989191110251017361211)
          ·
            refine ⟨2207983786665376526041817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1471989191110251017361211 2207983786665376526041817)
            ·
              refine ⟨1655987839999032394531363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2207983786665376526041817 1655987839999032394531363)
              ·
                refine ⟨2483981759998548591797045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1655987839999032394531363 2483981759998548591797045)
                ·
                  refine ⟨232873289999863930480973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2483981759998548591797045 232873289999863930480973)
                  ·
                    rfl

theorem cell21_1020418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_1020418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1020418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1020418 prefixEnd_1020418 := by exact prefixLift 1020418
  have htrace : WordTrace (prefixWord ++ tailWord_1020418) baseStart_1020418 baseEnd_1020418 := by
    simpa [prefixWord, tailWord_1020418, baseEnd_1020418] using wordTrace_append hprefix tailTrace_1020418
  have hstable : (prefixWord ++ tailWord_1020418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020418).length < 2 ^ (prefixWord ++ tailWord_1020418).sum := by decide
  have hdescent : baseEnd_1020418 < baseStart_1020418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020452 : List Nat := [2, 3, 1, 5, 2, 1, 1, 3, 3]
def baseStart_1020452 : Nat := 118140960795 + 1020452 * 2 ^ 59
def prefixEnd_1020452 : Nat := 4983230072969 + 3 ^ 40 * 1020452 * 2
def baseEnd_1020452 : Nat := 232881049263087426914237

theorem tailTrace_1020452 : CollatzResearch.WordTrace tailWord_1020452 prefixEnd_1020452 232881049263087426914237 := by
  unfold tailWord_1020452
  simp only [CollatzResearch.WordTrace]
  refine ⟨18609471049542079085811805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24812628066056105447749073 18609471049542079085811805)
  ·
    refine ⟨6978551643578279657179427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18609471049542079085811805 6978551643578279657179427)
    ·
      refine ⟨10467827465367419485769141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6978551643578279657179427 10467827465367419485769141)
      ·
        refine ⟨981358824878195576790857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10467827465367419485769141 981358824878195576790857)
        ·
          refine ⟨736019118658646682593143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 981358824878195576790857 736019118658646682593143)
          ·
            refine ⟨1104028677987970023889715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736019118658646682593143 1104028677987970023889715)
            ·
              refine ⟨1656043016981955035834573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1104028677987970023889715 1656043016981955035834573)
              ·
                refine ⟨621016131368233138437965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1656043016981955035834573 621016131368233138437965)
                ·
                  refine ⟨232881049263087426914237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 621016131368233138437965 232881049263087426914237)
                  ·
                    rfl

theorem cell21_1020452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_1020452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1020452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1020452 prefixEnd_1020452 := by exact prefixLift 1020452
  have htrace : WordTrace (prefixWord ++ tailWord_1020452) baseStart_1020452 baseEnd_1020452 := by
    simpa [prefixWord, tailWord_1020452, baseEnd_1020452] using wordTrace_append hprefix tailTrace_1020452
  have hstable : (prefixWord ++ tailWord_1020452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020452).length < 2 ^ (prefixWord ++ tailWord_1020452).sum := by decide
  have hdescent : baseEnd_1020452 < baseStart_1020452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020474 : List Nat := [3, 1, 1, 1, 3, 3, 2, 1, 6]
def baseStart_1020474 : Nat := 118140960795 + 1020474 * 2 ^ 59
def prefixEnd_1020474 : Nat := 4983230072969 + 3 ^ 40 * 1020474 * 2
def baseEnd_1020474 : Nat := 232886069962820277547525

theorem tailTrace_1020474 : CollatzResearch.WordTrace tailWord_1020474 prefixEnd_1020474 232886069962820277547525 := by
  unfold tailWord_1020474
  simp only [CollatzResearch.WordTrace]
  refine ⟨9304936126251113982231119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24813163003336303952616317 9304936126251113982231119)
  ·
    refine ⟨13957404189376670973346679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9304936126251113982231119 13957404189376670973346679)
    ·
      refine ⟨20936106284065006460020019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13957404189376670973346679 20936106284065006460020019)
      ·
        refine ⟨31404159426097509690030029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20936106284065006460020019 31404159426097509690030029)
        ·
          refine ⟨11776559784786566133761261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31404159426097509690030029 11776559784786566133761261)
          ·
            refine ⟨4416209919294962300160473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11776559784786566133761261 4416209919294962300160473)
            ·
              refine ⟨3312157439471221725120355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4416209919294962300160473 3312157439471221725120355)
              ·
                refine ⟨4968236159206832587680533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3312157439471221725120355 4968236159206832587680533)
                ·
                  refine ⟨232886069962820277547525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4968236159206832587680533 232886069962820277547525)
                  ·
                    rfl

theorem cell21_1020474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_1020474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1020474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1020474 prefixEnd_1020474 := by exact prefixLift 1020474
  have htrace : WordTrace (prefixWord ++ tailWord_1020474) baseStart_1020474 baseEnd_1020474 := by
    simpa [prefixWord, tailWord_1020474, baseEnd_1020474] using wordTrace_append hprefix tailTrace_1020474
  have hstable : (prefixWord ++ tailWord_1020474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020474).length < 2 ^ (prefixWord ++ tailWord_1020474).sum := by decide
  have hdescent : baseEnd_1020474 < baseStart_1020474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020477 : List Nat := [1, 4, 1, 3, 2, 3, 1, 1, 5]
def baseStart_1020477 : Nat := 118140960795 + 1020477 * 2 ^ 59
def prefixEnd_1020477 : Nat := 4983230072969 + 3 ^ 40 * 1020477 * 2
def baseEnd_1020477 : Nat := 232886754603692938997519

theorem tailTrace_1020477 : CollatzResearch.WordTrace tailWord_1020477 prefixEnd_1020477 232886754603692938997519 := by
  unfold tailWord_1020477
  simp only [CollatzResearch.WordTrace]
  refine ⟨37219853923993587441283685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24813235949329058294189123 37219853923993587441283685)
  ·
    refine ⟨6978722610748797645240691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37219853923993587441283685 6978722610748797645240691)
    ·
      refine ⟨10468083916123196467861037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6978722610748797645240691 10468083916123196467861037)
      ·
        refine ⟨3925531468546198675447889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10468083916123196467861037 3925531468546198675447889)
        ·
          refine ⟨2944148601409649006585917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3925531468546198675447889 2944148601409649006585917)
          ·
            refine ⟨1104055725528618377469719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2944148601409649006585917 1104055725528618377469719)
            ·
              refine ⟨1656083588292927566204579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1104055725528618377469719 1656083588292927566204579)
              ·
                refine ⟨2484125382439391349306869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1656083588292927566204579 2484125382439391349306869)
                ·
                  refine ⟨232886754603692938997519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2484125382439391349306869 232886754603692938997519)
                  ·
                    rfl

theorem cell21_1020477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_1020477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1020477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1020477 prefixEnd_1020477 := by exact prefixLift 1020477
  have htrace : WordTrace (prefixWord ++ tailWord_1020477) baseStart_1020477 baseEnd_1020477 := by
    simpa [prefixWord, tailWord_1020477, baseEnd_1020477] using wordTrace_append hprefix tailTrace_1020477
  have hstable : (prefixWord ++ tailWord_1020477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020477).length < 2 ^ (prefixWord ++ tailWord_1020477).sum := by decide
  have hdescent : baseEnd_1020477 < baseStart_1020477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020491 : List Nat := [1, 1, 1, 1, 3, 1, 8, 1, 4]
def baseStart_1020491 : Nat := 118140960795 + 1020491 * 2 ^ 59
def prefixEnd_1020491 : Nat := 4983230072969 + 3 ^ 40 * 1020491 * 2
def baseEnd_1020491 : Nat := 232889949594432025764157

theorem tailTrace_1020491 : CollatzResearch.WordTrace tailWord_1020491 prefixEnd_1020491 232889949594432025764157 := by
  unfold tailWord_1020491
  simp only [CollatzResearch.WordTrace]
  refine ⟨37220364545942867832293327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24813576363961911888195551 37220364545942867832293327)
  ·
    refine ⟨55830546818914301748439991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37220364545942867832293327 55830546818914301748439991)
    ·
      refine ⟨83745820228371452622659987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55830546818914301748439991 83745820228371452622659987)
      ·
        refine ⟨125618730342557178933989981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83745820228371452622659987 125618730342557178933989981)
        ·
          refine ⟨47107023878458942100246243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125618730342557178933989981 47107023878458942100246243)
          ·
            refine ⟨70660535817688413150369365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47107023878458942100246243 70660535817688413150369365)
            ·
              refine ⟨828053154113536091605891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 70660535817688413150369365 828053154113536091605891)
              ·
                refine ⟨1242079731170304137408837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 828053154113536091605891 1242079731170304137408837)
                ·
                  refine ⟨232889949594432025764157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1242079731170304137408837 232889949594432025764157)
                  ·
                    rfl

theorem cell21_1020491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 4].length) (baseStart_1020491 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1020491 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1020491 prefixEnd_1020491 := by exact prefixLift 1020491
  have htrace : WordTrace (prefixWord ++ tailWord_1020491) baseStart_1020491 baseEnd_1020491 := by
    simpa [prefixWord, tailWord_1020491, baseEnd_1020491] using wordTrace_append hprefix tailTrace_1020491
  have hstable : (prefixWord ++ tailWord_1020491).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020491).length < 2 ^ (prefixWord ++ tailWord_1020491).sum := by decide
  have hdescent : baseEnd_1020491 < baseStart_1020491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020536 : List Nat := [2, 1, 2, 1, 1, 1, 2, 8, 3]
def baseStart_1020536 : Nat := 118140960795 + 1020536 * 2 ^ 59
def prefixEnd_1020536 : Nat := 4983230072969 + 3 ^ 40 * 1020536 * 2
def baseEnd_1020536 : Nat := 232900219207521947514065

theorem tailTrace_1020536 : CollatzResearch.WordTrace tailWord_1020536 prefixEnd_1020536 232900219207521947514065 := by
  unfold tailWord_1020536
  simp only [CollatzResearch.WordTrace]
  refine ⟨18611002915389920258840731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24814670553853227011787641 18611002915389920258840731)
  ·
    refine ⟨27916504373084880388261097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18611002915389920258840731 27916504373084880388261097)
    ·
      refine ⟨20937378279813660291195823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27916504373084880388261097 20937378279813660291195823)
      ·
        refine ⟨31406067419720490436793735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20937378279813660291195823 31406067419720490436793735)
        ·
          refine ⟨47109101129580735655190603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31406067419720490436793735 47109101129580735655190603)
          ·
            refine ⟨70663651694371103482785905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47109101129580735655190603 70663651694371103482785905)
            ·
              refine ⟨52997738770778327612089429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70663651694371103482785905 52997738770778327612089429)
              ·
                refine ⟨621067251220058526704173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 52997738770778327612089429 621067251220058526704173)
                ·
                  refine ⟨232900219207521947514065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 621067251220058526704173 232900219207521947514065)
                  ·
                    rfl

theorem cell21_1020536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 8, 3].length) (baseStart_1020536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1020536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1020536 prefixEnd_1020536 := by exact prefixLift 1020536
  have htrace : WordTrace (prefixWord ++ tailWord_1020536) baseStart_1020536 baseEnd_1020536 := by
    simpa [prefixWord, tailWord_1020536, baseEnd_1020536] using wordTrace_append hprefix tailTrace_1020536
  have hstable : (prefixWord ++ tailWord_1020536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020536).length < 2 ^ (prefixWord ++ tailWord_1020536).sum := by decide
  have hdescent : baseEnd_1020536 < baseStart_1020536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020595 : List Nat := [1, 1, 1, 2, 3, 4, 1, 3, 5]
def baseStart_1020595 : Nat := 118140960795 + 1020595 * 2 ^ 59
def prefixEnd_1020595 : Nat := 4983230072969 + 3 ^ 40 * 1020595 * 2
def baseEnd_1020595 : Nat := 232913683811350956030611

theorem tailTrace_1020595 : CollatzResearch.WordTrace tailWord_1020595 prefixEnd_1020595 232913683811350956030611 := by
  unfold tailWord_1020595
  simp only [CollatzResearch.WordTrace]
  refine ⟨37224157737566093594079239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24816105158377395729386159 37224157737566093594079239)
  ·
    refine ⟨55836236606349140391118859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37224157737566093594079239 55836236606349140391118859)
    ·
      refine ⟨83754354909523710586678289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55836236606349140391118859 83754354909523710586678289)
      ·
        refine ⟨62815766182142782940008717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83754354909523710586678289 62815766182142782940008717)
        ·
          refine ⟨23555912318303543602503269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62815766182142782940008717 23555912318303543602503269)
          ·
            refine ⟨4416733559681914425469363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23555912318303543602503269 4416733559681914425469363)
            ·
              refine ⟨6625100339522871638204045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4416733559681914425469363 6625100339522871638204045)
              ·
                refine ⟨2484412627321076864326517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6625100339522871638204045 2484412627321076864326517)
                ·
                  refine ⟨232913683811350956030611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2484412627321076864326517 232913683811350956030611)
                  ·
                    rfl

theorem cell21_1020595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 5].length) (baseStart_1020595 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1020595 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1020595 prefixEnd_1020595 := by exact prefixLift 1020595
  have htrace : WordTrace (prefixWord ++ tailWord_1020595) baseStart_1020595 baseEnd_1020595 := by
    simpa [prefixWord, tailWord_1020595, baseEnd_1020595] using wordTrace_append hprefix tailTrace_1020595
  have hstable : (prefixWord ++ tailWord_1020595).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020595).length < 2 ^ (prefixWord ++ tailWord_1020595).sum := by decide
  have hdescent : baseEnd_1020595 < baseStart_1020595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020612 : List Nat := [2, 3, 3, 1, 1, 2, 2, 2, 5]
def baseStart_1020612 : Nat := 118140960795 + 1020612 * 2 ^ 59
def prefixEnd_1020612 : Nat := 4983230072969 + 3 ^ 40 * 1020612 * 2
def baseEnd_1020612 : Nat := 232917563442962704247243

theorem tailTrace_1020612 : CollatzResearch.WordTrace tailWord_1020612 prefixEnd_1020612 232917563442962704247243 := by
  unfold tailWord_1020612
  simp only [CollatzResearch.WordTrace]
  refine ⟨18612388889252252748724045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24816518519003003664965393 18612388889252252748724045)
  ·
    refine ⟨6979645833469594780771517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18612388889252252748724045 6979645833469594780771517)
    ·
      refine ⟨2617367187551098042789319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6979645833469594780771517 2617367187551098042789319)
      ·
        refine ⟨3926050781326647064183979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2617367187551098042789319 3926050781326647064183979)
        ·
          refine ⟨5889076171989970596275969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3926050781326647064183979 5889076171989970596275969)
          ·
            refine ⟨4416807128992477947206977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5889076171989970596275969 4416807128992477947206977)
            ·
              refine ⟨3312605346744358460405233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4416807128992477947206977 3312605346744358460405233)
              ·
                refine ⟨2484454010058268845303925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3312605346744358460405233 2484454010058268845303925)
                ·
                  refine ⟨232917563442962704247243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2484454010058268845303925 232917563442962704247243)
                  ·
                    rfl

theorem cell21_1020612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_1020612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1020612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1020612 prefixEnd_1020612 := by exact prefixLift 1020612
  have htrace : WordTrace (prefixWord ++ tailWord_1020612) baseStart_1020612 baseEnd_1020612 := by
    simpa [prefixWord, tailWord_1020612, baseEnd_1020612] using wordTrace_append hprefix tailTrace_1020612
  have hstable : (prefixWord ++ tailWord_1020612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020612).length < 2 ^ (prefixWord ++ tailWord_1020612).sum := by decide
  have hdescent : baseEnd_1020612 < baseStart_1020612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020764 : List Nat := [2, 2, 4, 2, 1, 1, 1, 3, 5]
def baseStart_1020764 : Nat := 118140960795 + 1020764 * 2 ^ 59
def prefixEnd_1020764 : Nat := 4983230072969 + 3 ^ 40 * 1020764 * 2
def baseEnd_1020764 : Nat := 232952251913844217713599

theorem tailTrace_1020764 : CollatzResearch.WordTrace tailWord_1020764 prefixEnd_1020764 232952251913844217713599 := by
  unfold tailWord_1020764
  simp only [CollatzResearch.WordTrace]
  refine ⟨18615160836976917728490673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24820214449302556971320897 18615160836976917728490673)
  ·
    refine ⟨13961370627732688296368005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18615160836976917728490673 13961370627732688296368005)
    ·
      refine ⟨2617756992699879055569001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13961370627732688296368005 2617756992699879055569001)
      ·
        refine ⟨1963317744524909291676751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2617756992699879055569001 1963317744524909291676751)
        ·
          refine ⟨2944976616787363937515127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1963317744524909291676751 2944976616787363937515127)
          ·
            refine ⟨4417464925181045906272691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2944976616787363937515127 4417464925181045906272691)
            ·
              refine ⟨6626197387771568859409037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4417464925181045906272691 6626197387771568859409037)
              ·
                refine ⟨2484824020414338322278389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6626197387771568859409037 2484824020414338322278389)
                ·
                  refine ⟨232952251913844217713599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2484824020414338322278389 232952251913844217713599)
                  ·
                    rfl

theorem cell21_1020764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_1020764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1020764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1020764 prefixEnd_1020764 := by exact prefixLift 1020764
  have htrace : WordTrace (prefixWord ++ tailWord_1020764) baseStart_1020764 baseEnd_1020764 := by
    simpa [prefixWord, tailWord_1020764, baseEnd_1020764] using wordTrace_append hprefix tailTrace_1020764
  have hstable : (prefixWord ++ tailWord_1020764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020764).length < 2 ^ (prefixWord ++ tailWord_1020764).sum := by decide
  have hdescent : baseEnd_1020764 < baseStart_1020764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020877 : List Nat := [1, 6, 3, 1, 2, 1, 1, 6]
def baseStart_1020877 : Nat := 118140960795 + 1020877 * 2 ^ 59
def prefixEnd_1020877 : Nat := 4983230072969 + 3 ^ 40 * 1020877 * 2
def baseEnd_1020877 : Nat := 77659346684460377443345

theorem tailTrace_1020877 : CollatzResearch.WordTrace tailWord_1020877 prefixEnd_1020877 77659346684460377443345 := by
  unfold tailWord_1020877
  simp only [CollatzResearch.WordTrace]
  refine ⟨37234443122544455755844885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24822962081696303837229923 37234443122544455755844885)
  ·
    refine ⟨1745364521369271363555229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37234443122544455755844885 1745364521369271363555229)
    ·
      refine ⟨654511695513476761333211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1745364521369271363555229 654511695513476761333211)
      ·
        refine ⟨981767543270215141999817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654511695513476761333211 981767543270215141999817)
        ·
          refine ⟨736325657452661356499863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 981767543270215141999817 736325657452661356499863)
          ·
            refine ⟨1104488486178992034749795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736325657452661356499863 1104488486178992034749795)
            ·
              refine ⟨1656732729268488052124693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1104488486178992034749795 1656732729268488052124693)
              ·
                refine ⟨77659346684460377443345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1656732729268488052124693 77659346684460377443345)
                ·
                  rfl

theorem cell21_1020877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 6].length) (baseStart_1020877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1020877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1020877 prefixEnd_1020877 := by exact prefixLift 1020877
  have htrace : WordTrace (prefixWord ++ tailWord_1020877) baseStart_1020877 baseEnd_1020877 := by
    simpa [prefixWord, tailWord_1020877, baseEnd_1020877] using wordTrace_append hprefix tailTrace_1020877
  have hstable : (prefixWord ++ tailWord_1020877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020877).length < 2 ^ (prefixWord ++ tailWord_1020877).sum := by decide
  have hdescent : baseEnd_1020877 < baseStart_1020877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020899 : List Nat := [1, 1, 1, 6, 1, 1, 3, 2, 5]
def baseStart_1020899 : Nat := 118140960795 + 1020899 * 2 ^ 59
def prefixEnd_1020899 : Nat := 4983230072969 + 3 ^ 40 * 1020899 * 2
def baseEnd_1020899 : Nat := 232983060753113982963323

theorem tailTrace_1020899 : CollatzResearch.WordTrace tailWord_1020899 prefixEnd_1020899 232983060753113982963323 := by
  unfold tailWord_1020899
  simp only [CollatzResearch.WordTrace]
  refine ⟨37235245528464753513145751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24823497018976502342097167 37235245528464753513145751)
  ·
    refine ⟨55852868292697130269718627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37235245528464753513145751 55852868292697130269718627)
    ·
      refine ⟨83779302439045695404577941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55852868292697130269718627 83779302439045695404577941)
      ·
        refine ⟨3927154801830266972089591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 83779302439045695404577941 3927154801830266972089591)
        ·
          refine ⟨5890732202745400458134387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3927154801830266972089591 5890732202745400458134387)
          ·
            refine ⟨8836098304118100687201581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5890732202745400458134387 8836098304118100687201581)
            ·
              refine ⟨3313536864044287757700593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8836098304118100687201581 3313536864044287757700593)
              ·
                refine ⟨2485152648033215818275445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3313536864044287757700593 2485152648033215818275445)
                ·
                  refine ⟨232983060753113982963323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2485152648033215818275445 232983060753113982963323)
                  ·
                    rfl

theorem cell21_1020899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 5].length) (baseStart_1020899 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1020899 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1020899 prefixEnd_1020899 := by exact prefixLift 1020899
  have htrace : WordTrace (prefixWord ++ tailWord_1020899) baseStart_1020899 baseEnd_1020899 := by
    simpa [prefixWord, tailWord_1020899, baseEnd_1020899] using wordTrace_append hprefix tailTrace_1020899
  have hstable : (prefixWord ++ tailWord_1020899).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020899).length < 2 ^ (prefixWord ++ tailWord_1020899).sum := by decide
  have hdescent : baseEnd_1020899 < baseStart_1020899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020961 : List Nat := [1, 2, 3, 2, 3, 1, 4, 5]
def baseStart_1020961 : Nat := 118140960795 + 1020961 * 2 ^ 59
def prefixEnd_1020961 : Nat := 4983230072969 + 3 ^ 40 * 1020961 * 2
def baseEnd_1020961 : Nat := 77665736665938550976621

theorem tailTrace_1020961 : CollatzResearch.WordTrace tailWord_1020961 prefixEnd_1020961 77665736665938550976621 := by
  unfold tailWord_1020961
  simp only [CollatzResearch.WordTrace]
  refine ⟨37237506854240138101902737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24825004569493425401268491 37237506854240138101902737)
  ·
    refine ⟨27928130140680103576427053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37237506854240138101902737 27928130140680103576427053)
    ·
      refine ⟨10473048802755038841160145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27928130140680103576427053 10473048802755038841160145)
      ·
        refine ⟨7854786602066279130870109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10473048802755038841160145 7854786602066279130870109)
        ·
          refine ⟨2945544975774854674076291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7854786602066279130870109 2945544975774854674076291)
          ·
            refine ⟨4418317463662282011114437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2945544975774854674076291 4418317463662282011114437)
            ·
              refine ⟨828434524436677877083957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4418317463662282011114437 828434524436677877083957)
              ·
                refine ⟨77665736665938550976621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 828434524436677877083957 77665736665938550976621)
                ·
                  rfl

theorem cell21_1020961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 5].length) (baseStart_1020961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1020961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1020961 prefixEnd_1020961 := by exact prefixLift 1020961
  have htrace : WordTrace (prefixWord ++ tailWord_1020961) baseStart_1020961 baseEnd_1020961 := by
    simpa [prefixWord, tailWord_1020961, baseEnd_1020961] using wordTrace_append hprefix tailTrace_1020961
  have hstable : (prefixWord ++ tailWord_1020961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020961).length < 2 ^ (prefixWord ++ tailWord_1020961).sum := by decide
  have hdescent : baseEnd_1020961 < baseStart_1020961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021006 : List Nat := [4, 1, 1, 1, 1, 3, 3, 3, 4]
def baseStart_1021006 : Nat := 118140960795 + 1021006 * 2 ^ 59
def prefixEnd_1021006 : Nat := 4983230072969 + 3 ^ 40 * 1021006 * 2
def baseEnd_1021006 : Nat := 233007479610905574679771

theorem tailTrace_1021006 : CollatzResearch.WordTrace tailWord_1021006 prefixEnd_1021006 233007479610905574679771 := by
  unfold tailWord_1021006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4654893517384638848411359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24826098759384740524860581 4654893517384638848411359)
  ·
    refine ⟨6982340276076958272617039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4654893517384638848411359 6982340276076958272617039)
    ·
      refine ⟨10473510414115437408925559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6982340276076958272617039 10473510414115437408925559)
      ·
        refine ⟨15710265621173156113388339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10473510414115437408925559 15710265621173156113388339)
        ·
          refine ⟨23565398431759734170082509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15710265621173156113388339 23565398431759734170082509)
          ·
            refine ⟨8837024411909900313780941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23565398431759734170082509 8837024411909900313780941)
            ·
              refine ⟨3313884154466212617667853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8837024411909900313780941 3313884154466212617667853)
              ·
                refine ⟨1242706557924829731625445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3313884154466212617667853 1242706557924829731625445)
                ·
                  refine ⟨233007479610905574679771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1242706557924829731625445 233007479610905574679771)
                  ·
                    rfl

theorem cell21_1021006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_1021006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1021006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1021006 prefixEnd_1021006 := by exact prefixLift 1021006
  have htrace : WordTrace (prefixWord ++ tailWord_1021006) baseStart_1021006 baseEnd_1021006 := by
    simpa [prefixWord, tailWord_1021006, baseEnd_1021006] using wordTrace_append hprefix tailTrace_1021006
  have hstable : (prefixWord ++ tailWord_1021006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021006).length < 2 ^ (prefixWord ++ tailWord_1021006).sum := by decide
  have hdescent : baseEnd_1021006 < baseStart_1021006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021020 : List Nat := [2, 2, 4, 1, 1, 1, 1, 9]
def baseStart_1021020 : Nat := 118140960795 + 1021020 * 2 ^ 59
def prefixEnd_1021020 : Nat := 4983230072969 + 3 ^ 40 * 1021020 * 2
def baseEnd_1021020 : Nat := 77670224867214887148803

theorem tailTrace_1021020 : CollatzResearch.WordTrace tailWord_1021020 prefixEnd_1021020 77670224867214887148803 := by
  unfold tailWord_1021020
  simp only [CollatzResearch.WordTrace]
  refine ⟨18619829380513195589150257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24826439174017594118867009 18619829380513195589150257)
  ·
    refine ⟨13964872035384896691862693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18619829380513195589150257 13964872035384896691862693)
    ·
      refine ⟨2618413506634668129724255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13964872035384896691862693 2618413506634668129724255)
      ·
        refine ⟨3927620259952002194586383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2618413506634668129724255 3927620259952002194586383)
        ·
          refine ⟨5891430389928003291879575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3927620259952002194586383 5891430389928003291879575)
          ·
            refine ⟨8837145584892004937819363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5891430389928003291879575 8837145584892004937819363)
            ·
              refine ⟨13255718377338007406729045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8837145584892004937819363 13255718377338007406729045)
              ·
                refine ⟨77670224867214887148803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13255718377338007406729045 77670224867214887148803)
                ·
                  rfl

theorem cell21_1021020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 9].length) (baseStart_1021020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1021020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1021020 prefixEnd_1021020 := by exact prefixLift 1021020
  have htrace : WordTrace (prefixWord ++ tailWord_1021020) baseStart_1021020 baseEnd_1021020 := by
    simpa [prefixWord, tailWord_1021020, baseEnd_1021020] using wordTrace_append hprefix tailTrace_1021020
  have hstable : (prefixWord ++ tailWord_1021020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021020).length < 2 ^ (prefixWord ++ tailWord_1021020).sum := by decide
  have hdescent : baseEnd_1021020 < baseStart_1021020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021220 : List Nat := [2, 3, 1, 3, 1, 1, 3, 4, 3]
def baseStart_1021220 : Nat := 118140960795 + 1021220 * 2 ^ 59
def prefixEnd_1021220 : Nat := 4983230072969 + 3 ^ 40 * 1021220 * 2
def baseEnd_1021220 : Nat := 233056317326488758112667

theorem tailTrace_1021220 : CollatzResearch.WordTrace tailWord_1021220 prefixEnd_1021220 233056317326488758112667 := by
  unfold tailWord_1021220
  simp only [CollatzResearch.WordTrace]
  refine ⟨18623476680150912667790557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24831302240201216890387409 18623476680150912667790557)
  ·
    refine ⟨6983803755056592250421459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18623476680150912667790557 6983803755056592250421459)
    ·
      refine ⟨10475705632584888375632189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6983803755056592250421459 10475705632584888375632189)
      ·
        refine ⟨3928389612219333140862071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10475705632584888375632189 3928389612219333140862071)
        ·
          refine ⟨5892584418328999711293107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3928389612219333140862071 5892584418328999711293107)
          ·
            refine ⟨8838876627493499566939661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5892584418328999711293107 8838876627493499566939661)
            ·
              refine ⟨3314578735310062337602373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8838876627493499566939661 3314578735310062337602373)
              ·
                refine ⟨621483512870636688300445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3314578735310062337602373 621483512870636688300445)
                ·
                  refine ⟨233056317326488758112667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 621483512870636688300445 233056317326488758112667)
                  ·
                    rfl

theorem cell21_1021220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_1021220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1021220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1021220 prefixEnd_1021220 := by exact prefixLift 1021220
  have htrace : WordTrace (prefixWord ++ tailWord_1021220) baseStart_1021220 baseEnd_1021220 := by
    simpa [prefixWord, tailWord_1021220, baseEnd_1021220] using wordTrace_append hprefix tailTrace_1021220
  have hstable : (prefixWord ++ tailWord_1021220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021220).length < 2 ^ (prefixWord ++ tailWord_1021220).sum := by decide
  have hdescent : baseEnd_1021220 < baseStart_1021220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021234 : List Nat := [3, 2, 1, 1, 4, 1, 2, 3, 4]
def baseStart_1021234 : Nat := 118140960795 + 1021234 * 2 ^ 59
def prefixEnd_1021234 : Nat := 4983230072969 + 3 ^ 40 * 1021234 * 2
def baseEnd_1021234 : Nat := 233059512317227844879305

theorem tailTrace_1021234 : CollatzResearch.WordTrace tailWord_1021234 prefixEnd_1021234 233059512317227844879305 := by
  unfold tailWord_1021234
  simp only [CollatzResearch.WordTrace]
  refine ⟨9311865995562776431647689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24831642654834070484393837 9311865995562776431647689)
  ·
    refine ⟨6983899496672082323735767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9311865995562776431647689 6983899496672082323735767)
    ·
      refine ⟨10475849245008123485603651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6983899496672082323735767 10475849245008123485603651)
      ·
        refine ⟨15713773867512185228405477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10475849245008123485603651 15713773867512185228405477)
        ·
          refine ⟨2946332600158534730326027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15713773867512185228405477 2946332600158534730326027)
          ·
            refine ⟨4419498900237802095489041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2946332600158534730326027 4419498900237802095489041)
            ·
              refine ⟨3314624175178351571616781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4419498900237802095489041 3314624175178351571616781)
              ·
                refine ⟨1242984065691881839356293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3314624175178351571616781 1242984065691881839356293)
                ·
                  refine ⟨233059512317227844879305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1242984065691881839356293 233059512317227844879305)
                  ·
                    rfl

theorem cell21_1021234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_1021234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1021234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1021234 prefixEnd_1021234 := by exact prefixLift 1021234
  have htrace : WordTrace (prefixWord ++ tailWord_1021234) baseStart_1021234 baseEnd_1021234 := by
    simpa [prefixWord, tailWord_1021234, baseEnd_1021234] using wordTrace_append hprefix tailTrace_1021234
  have hstable : (prefixWord ++ tailWord_1021234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021234).length < 2 ^ (prefixWord ++ tailWord_1021234).sum := by decide
  have hdescent : baseEnd_1021234 < baseStart_1021234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021248 : List Nat := [2, 1, 1, 2, 2, 1, 7, 5]
def baseStart_1021248 : Nat := 118140960795 + 1021248 * 2 ^ 59
def prefixEnd_1021248 : Nat := 4983230072969 + 3 ^ 40 * 1021248 * 2
def baseEnd_1021248 : Nat := 77687569102655643881981

theorem tailTrace_1021248 : CollatzResearch.WordTrace tailWord_1021248 prefixEnd_1021248 77687569102655643881981 := by
  unfold tailWord_1021248
  simp only [CollatzResearch.WordTrace]
  refine ⟨18623987302100193058800199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24831983069466924078400265 18623987302100193058800199)
  ·
    refine ⟨27935980953150289588200299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18623987302100193058800199 27935980953150289588200299)
    ·
      refine ⟨41903971429725434382300449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27935980953150289588200299 41903971429725434382300449)
      ·
        refine ⟨31427978572294075786725337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41903971429725434382300449 31427978572294075786725337)
        ·
          refine ⟨23570983929220556840044003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31427978572294075786725337 23570983929220556840044003)
          ·
            refine ⟨35356475893830835260066005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23570983929220556840044003 35356475893830835260066005)
            ·
              refine ⟨828667403761660201407797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 35356475893830835260066005 828667403761660201407797)
              ·
                refine ⟨77687569102655643881981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 828667403761660201407797 77687569102655643881981)
                ·
                  rfl

theorem cell21_1021248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 5].length) (baseStart_1021248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1021248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1021248 prefixEnd_1021248 := by exact prefixLift 1021248
  have htrace : WordTrace (prefixWord ++ tailWord_1021248) baseStart_1021248 baseEnd_1021248 := by
    simpa [prefixWord, tailWord_1021248, baseEnd_1021248] using wordTrace_append hprefix tailTrace_1021248
  have hstable : (prefixWord ++ tailWord_1021248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021248).length < 2 ^ (prefixWord ++ tailWord_1021248).sum := by decide
  have hdescent : baseEnd_1021248 < baseStart_1021248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021262 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 7]
def baseStart_1021262 : Nat := 118140960795 + 1021262 * 2 ^ 59
def prefixEnd_1021262 : Nat := 4983230072969 + 3 ^ 40 * 1021262 * 2
def baseEnd_1021262 : Nat := 233065902298706018412581

theorem tailTrace_1021262 : CollatzResearch.WordTrace tailWord_1021262 prefixEnd_1021262 233065902298706018412581 := by
  unfold tailWord_1021262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4656060653268708313576255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24832323484099777672406693 4656060653268708313576255)
  ·
    refine ⟨6984090979903062470364383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4656060653268708313576255 6984090979903062470364383)
    ·
      refine ⟨10476136469854593705546575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6984090979903062470364383 10476136469854593705546575)
      ·
        refine ⟨15714204704781890558319863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10476136469854593705546575 15714204704781890558319863)
        ·
          refine ⟨23571307057172835837479795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15714204704781890558319863 23571307057172835837479795)
          ·
            refine ⟨35356960585759253756219693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23571307057172835837479795 35356960585759253756219693)
            ·
              refine ⟨13258860219659720158582385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35356960585759253756219693 13258860219659720158582385)
              ·
                refine ⟨9944145164744790118936789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13258860219659720158582385 9944145164744790118936789)
                ·
                  refine ⟨233065902298706018412581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9944145164744790118936789 233065902298706018412581)
                  ·
                    rfl

theorem cell21_1021262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_1021262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1021262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1021262 prefixEnd_1021262 := by exact prefixLift 1021262
  have htrace : WordTrace (prefixWord ++ tailWord_1021262) baseStart_1021262 baseEnd_1021262 := by
    simpa [prefixWord, tailWord_1021262, baseEnd_1021262] using wordTrace_append hprefix tailTrace_1021262
  have hstable : (prefixWord ++ tailWord_1021262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021262).length < 2 ^ (prefixWord ++ tailWord_1021262).sum := by decide
  have hdescent : baseEnd_1021262 < baseStart_1021262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021307 : List Nat := [1, 1, 1, 1, 1, 6, 3, 7]
def baseStart_1021307 : Nat := 118140960795 + 1021307 * 2 ^ 59
def prefixEnd_1021307 : Nat := 4983230072969 + 3 ^ 40 * 1021307 * 2
def baseEnd_1021307 : Nat := 77692057303931980054163

theorem tailTrace_1021307 : CollatzResearch.WordTrace tailWord_1021307 prefixEnd_1021307 77692057303931980054163 := by
  unfold tailWord_1021307
  simp only [CollatzResearch.WordTrace]
  refine ⟨37250126510986639193998175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24833417673991092795998783 37250126510986639193998175)
  ·
    refine ⟨55875189766479958790997263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37250126510986639193998175 55875189766479958790997263)
    ·
      refine ⟨83812784649719938186495895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55875189766479958790997263 83812784649719938186495895)
      ·
        refine ⟨125719176974579907279743843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83812784649719938186495895 125719176974579907279743843)
        ·
          refine ⟨188578765461869860919615765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125719176974579907279743843 188578765461869860919615765)
          ·
            refine ⟨8839629631025149730606989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 188578765461869860919615765 8839629631025149730606989)
            ·
              refine ⟨3314861111634431148977621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8839629631025149730606989 3314861111634431148977621)
              ·
                refine ⟨77692057303931980054163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3314861111634431148977621 77692057303931980054163)
                ·
                  rfl

theorem cell21_1021307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 7].length) (baseStart_1021307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1021307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1021307 prefixEnd_1021307 := by exact prefixLift 1021307
  have htrace : WordTrace (prefixWord ++ tailWord_1021307) baseStart_1021307 baseEnd_1021307 := by
    simpa [prefixWord, tailWord_1021307, baseEnd_1021307] using wordTrace_append hprefix tailTrace_1021307
  have hstable : (prefixWord ++ tailWord_1021307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021307).length < 2 ^ (prefixWord ++ tailWord_1021307).sum := by decide
  have hdescent : baseEnd_1021307 < baseStart_1021307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021330 : List Nat := [3, 2, 3, 3, 2, 1, 1, 1, 5]
def baseStart_1021330 : Nat := 118140960795 + 1021330 * 2 ^ 59
def prefixEnd_1021330 : Nat := 4983230072969 + 3 ^ 40 * 1021330 * 2
def baseEnd_1021330 : Nat := 233081420825153011279109

theorem tailTrace_1021330 : CollatzResearch.WordTrace tailWord_1021330 prefixEnd_1021330 233081420825153011279109 := by
  unfold tailWord_1021330
  simp only [CollatzResearch.WordTrace]
  refine ⟨9312741347475828530521361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24833976926602209414723629 9312741347475828530521361)
  ·
    refine ⟨6984556010606871397891021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9312741347475828530521361 6984556010606871397891021)
    ·
      refine ⟨2619208503977576774209133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6984556010606871397891021 2619208503977576774209133)
      ·
        refine ⟨982203188991591290328425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2619208503977576774209133 982203188991591290328425)
        ·
          refine ⟨736652391743693467746319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 982203188991591290328425 736652391743693467746319)
          ·
            refine ⟨1104978587615540201619479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736652391743693467746319 1104978587615540201619479)
            ·
              refine ⟨1657467881423310302429219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1104978587615540201619479 1657467881423310302429219)
              ·
                refine ⟨2486201822134965453643829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1657467881423310302429219 2486201822134965453643829)
                ·
                  refine ⟨233081420825153011279109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2486201822134965453643829 233081420825153011279109)
                  ·
                    rfl

theorem cell21_1021330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_1021330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1021330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1021330 prefixEnd_1021330 := by exact prefixLift 1021330
  have htrace : WordTrace (prefixWord ++ tailWord_1021330) baseStart_1021330 baseEnd_1021330 := by
    simpa [prefixWord, tailWord_1021330, baseEnd_1021330] using wordTrace_append hprefix tailTrace_1021330
  have hstable : (prefixWord ++ tailWord_1021330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021330).length < 2 ^ (prefixWord ++ tailWord_1021330).sum := by decide
  have hdescent : baseEnd_1021330 < baseStart_1021330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021378 : List Nat := [3, 5, 2, 1, 1, 1, 2, 2, 4]
def baseStart_1021378 : Nat := 118140960795 + 1021378 * 2 ^ 59
def prefixEnd_1021378 : Nat := 4983230072969 + 3 ^ 40 * 1021378 * 2
def baseEnd_1021378 : Nat := 233092375079115594479011

theorem tailTrace_1021378 : CollatzResearch.WordTrace tailWord_1021378 prefixEnd_1021378 233092375079115594479011 := by
  unfold tailWord_1021378
  simp only [CollatzResearch.WordTrace]
  refine ⟨9313179023432354579958197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24835144062486278879888525 9313179023432354579958197)
  ·
    refine ⟨873110533446783241871081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9313179023432354579958197 873110533446783241871081)
    ·
      refine ⟨654832900085087431403311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 873110533446783241871081 654832900085087431403311)
      ·
        refine ⟨982249350127631147104967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654832900085087431403311 982249350127631147104967)
        ·
          refine ⟨1473374025191446720657451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 982249350127631147104967 1473374025191446720657451)
          ·
            refine ⟨2210061037787170080986177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1473374025191446720657451 2210061037787170080986177)
            ·
              refine ⟨1657545778340377560739633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2210061037787170080986177 1657545778340377560739633)
              ·
                refine ⟨1243159333755283170554725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1657545778340377560739633 1243159333755283170554725)
                ·
                  refine ⟨233092375079115594479011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1243159333755283170554725 233092375079115594479011)
                  ·
                    rfl

theorem cell21_1021378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_1021378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1021378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1021378 prefixEnd_1021378 := by exact prefixLift 1021378
  have htrace : WordTrace (prefixWord ++ tailWord_1021378) baseStart_1021378 baseEnd_1021378 := by
    simpa [prefixWord, tailWord_1021378, baseEnd_1021378] using wordTrace_append hprefix tailTrace_1021378
  have hstable : (prefixWord ++ tailWord_1021378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021378).length < 2 ^ (prefixWord ++ tailWord_1021378).sum := by decide
  have hdescent : baseEnd_1021378 < baseStart_1021378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021386 : List Nat := [3, 1, 2, 1, 2, 4, 2, 2, 4]
def baseStart_1021386 : Nat := 118140960795 + 1021386 * 2 ^ 59
def prefixEnd_1021386 : Nat := 4983230072969 + 3 ^ 40 * 1021386 * 2
def baseEnd_1021386 : Nat := 233094200788109358345661

theorem tailTrace_1021386 : CollatzResearch.WordTrace tailWord_1021386 prefixEnd_1021386 233094200788109358345661 := by
  unfold tailWord_1021386
  simp only [CollatzResearch.WordTrace]
  refine ⟨9313251969425108921531003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24835338585133623790749341 9313251969425108921531003)
  ·
    refine ⟨13969877954137663382296505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9313251969425108921531003 13969877954137663382296505)
    ·
      refine ⟨10477408465603247536722379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13969877954137663382296505 10477408465603247536722379)
      ·
        refine ⟨15716112698404871305083569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10477408465603247536722379 15716112698404871305083569)
        ·
          refine ⟨11787084523803653478812677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15716112698404871305083569 11787084523803653478812677)
          ·
            refine ⟨2210078348213185027277377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11787084523803653478812677 2210078348213185027277377)
            ·
              refine ⟨1657558761159888770458033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2210078348213185027277377 1657558761159888770458033)
              ·
                refine ⟨1243169070869916577843525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1657558761159888770458033 1243169070869916577843525)
                ·
                  refine ⟨233094200788109358345661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1243169070869916577843525 233094200788109358345661)
                  ·
                    rfl

theorem cell21_1021386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_1021386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1021386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1021386 prefixEnd_1021386 := by exact prefixLift 1021386
  have htrace : WordTrace (prefixWord ++ tailWord_1021386) baseStart_1021386 baseEnd_1021386 := by
    simpa [prefixWord, tailWord_1021386, baseEnd_1021386] using wordTrace_append hprefix tailTrace_1021386
  have hstable : (prefixWord ++ tailWord_1021386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021386).length < 2 ^ (prefixWord ++ tailWord_1021386).sum := by decide
  have hdescent : baseEnd_1021386 < baseStart_1021386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021510 : List Nat := [6, 1, 1, 1, 3, 1, 2, 6]
def baseStart_1021510 : Nat := 118140960795 + 1021510 * 2 ^ 59
def prefixEnd_1021510 : Nat := 4983230072969 + 3 ^ 40 * 1021510 * 2
def baseEnd_1021510 : Nat := 77707499759170899426247

theorem tailTrace_1021510 : CollatzResearch.WordTrace tailWord_1021510 prefixEnd_1021510 77707499759170899426247 := by
  unfold tailWord_1021510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1164297829039100151988687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24838353686167469909091989 1164297829039100151988687)
  ·
    refine ⟨1746446743558650227983031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1164297829039100151988687 1746446743558650227983031)
    ·
      refine ⟨2619670115337975341974547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1746446743558650227983031 2619670115337975341974547)
      ·
        refine ⟨3929505173006963012961821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2619670115337975341974547 3929505173006963012961821)
        ·
          refine ⟨1473564439877611129860683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3929505173006963012961821 1473564439877611129860683)
          ·
            refine ⟨2210346659816416694791025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1473564439877611129860683 2210346659816416694791025)
            ·
              refine ⟨1657759994862312521093269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2210346659816416694791025 1657759994862312521093269)
              ·
                refine ⟨77707499759170899426247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1657759994862312521093269 77707499759170899426247)
                ·
                  rfl

theorem cell21_1021510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_1021510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1021510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1021510 prefixEnd_1021510 := by exact prefixLift 1021510
  have htrace : WordTrace (prefixWord ++ tailWord_1021510) baseStart_1021510 baseEnd_1021510 := by
    simpa [prefixWord, tailWord_1021510, baseEnd_1021510] using wordTrace_append hprefix tailTrace_1021510
  have hstable : (prefixWord ++ tailWord_1021510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021510).length < 2 ^ (prefixWord ++ tailWord_1021510).sum := by decide
  have hdescent : baseEnd_1021510 < baseStart_1021510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021521 : List Nat := [1, 2, 2, 1, 3, 2, 3, 3, 4]
def baseStart_1021521 : Nat := 118140960795 + 1021521 * 2 ^ 59
def prefixEnd_1021521 : Nat := 4983230072969 + 3 ^ 40 * 1021521 * 2
def baseEnd_1021521 : Nat := 233125009627379123595385

theorem tailTrace_1021521 : CollatzResearch.WordTrace tailWord_1021521 prefixEnd_1021521 233125009627379123595385 := by
  unfold tailWord_1021521
  simp only [CollatzResearch.WordTrace]
  refine ⟨37257931732211353742288417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24838621154807569161525611 37257931732211353742288417)
  ·
    refine ⟨27943448799158515306716313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37257931732211353742288417 27943448799158515306716313)
    ·
      refine ⟨20957586599368886480037235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27943448799158515306716313 20957586599368886480037235)
      ·
        refine ⟨31436379899053329720055853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20957586599368886480037235 31436379899053329720055853)
        ·
          refine ⟨11788642462144998645020945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31436379899053329720055853 11788642462144998645020945)
          ·
            refine ⟨8841481846608748983765709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11788642462144998645020945 8841481846608748983765709)
            ·
              refine ⟨3315555692478280868912141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8841481846608748983765709 3315555692478280868912141)
              ·
                refine ⟨1243333384679355325842053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3315555692478280868912141 1243333384679355325842053)
                ·
                  refine ⟨233125009627379123595385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1243333384679355325842053 233125009627379123595385)
                  ·
                    rfl

theorem cell21_1021521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 4].length) (baseStart_1021521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1021521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1021521 prefixEnd_1021521 := by exact prefixLift 1021521
  have htrace : WordTrace (prefixWord ++ tailWord_1021521) baseStart_1021521 baseEnd_1021521 := by
    simpa [prefixWord, tailWord_1021521, baseEnd_1021521] using wordTrace_append hprefix tailTrace_1021521
  have hstable : (prefixWord ++ tailWord_1021521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021521).length < 2 ^ (prefixWord ++ tailWord_1021521).sum := by decide
  have hdescent : baseEnd_1021521 < baseStart_1021521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021558 : List Nat := [5, 1, 1, 2, 2, 3, 2, 2, 3]
def baseStart_1021558 : Nat := 118140960795 + 1021558 * 2 ^ 59
def prefixEnd_1021558 : Nat := 4983230072969 + 3 ^ 40 * 1021558 * 2
def baseEnd_1021558 : Nat := 233133453531475281478643

theorem tailTrace_1021558 : CollatzResearch.WordTrace tailWord_1021558 prefixEnd_1021558 233133453531475281478643 := by
  unfold tailWord_1021558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2328705077067331816336583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24839520822051539374256885 2328705077067331816336583)
  ·
    refine ⟨3493057615600997724504875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2328705077067331816336583 3493057615600997724504875)
    ·
      refine ⟨5239586423401496586757313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3493057615600997724504875 5239586423401496586757313)
      ·
        refine ⟨3929689817551122440067985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5239586423401496586757313 3929689817551122440067985)
        ·
          refine ⟨2947267363163341830050989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3929689817551122440067985 2947267363163341830050989)
          ·
            refine ⟨1105225261186253186269121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2947267363163341830050989 1105225261186253186269121)
            ·
              refine ⟨828918945889689889701841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1105225261186253186269121 828918945889689889701841)
              ·
                refine ⟨621689209417267417276381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 828918945889689889701841 621689209417267417276381)
                ·
                  refine ⟨233133453531475281478643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 621689209417267417276381 233133453531475281478643)
                  ·
                    rfl

theorem cell21_1021558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_1021558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1021558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1021558 prefixEnd_1021558 := by exact prefixLift 1021558
  have htrace : WordTrace (prefixWord ++ tailWord_1021558) baseStart_1021558 baseEnd_1021558 := by
    simpa [prefixWord, tailWord_1021558, baseEnd_1021558] using wordTrace_append hprefix tailTrace_1021558
  have hstable : (prefixWord ++ tailWord_1021558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021558).length < 2 ^ (prefixWord ++ tailWord_1021558).sum := by decide
  have hdescent : baseEnd_1021558 < baseStart_1021558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021600 : List Nat := [2, 1, 1, 4, 3, 2, 2, 3, 3]
def baseStart_1021600 : Nat := 118140960795 + 1021600 * 2 ^ 59
def prefixEnd_1021600 : Nat := 4983230072969 + 3 ^ 40 * 1021600 * 2
def baseEnd_1021600 : Nat := 233143038503692541778557

theorem tailTrace_1021600 : CollatzResearch.WordTrace tailWord_1021600 prefixEnd_1021600 233143038503692541778557 := by
  unfold tailWord_1021600
  simp only [CollatzResearch.WordTrace]
  refine ⟨18630406549462575117207127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24840542065950100156276169 18630406549462575117207127)
  ·
    refine ⟨27945609824193862675810691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18630406549462575117207127 27945609824193862675810691)
    ·
      refine ⟨41918414736290794013716037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27945609824193862675810691 41918414736290794013716037)
      ·
        refine ⟨7859702763054523877571757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41918414736290794013716037 7859702763054523877571757)
        ·
          refine ⟨2947388536145446454089409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7859702763054523877571757 2947388536145446454089409)
          ·
            refine ⟨2210541402109084840567057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2947388536145446454089409 2210541402109084840567057)
            ·
              refine ⟨1657906051581813630425293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2210541402109084840567057 1657906051581813630425293)
              ·
                refine ⟨621714769343180111409485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1657906051581813630425293 621714769343180111409485)
                ·
                  refine ⟨233143038503692541778557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 621714769343180111409485 233143038503692541778557)
                  ·
                    rfl

theorem cell21_1021600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 3, 3].length) (baseStart_1021600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1021600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1021600 prefixEnd_1021600 := by exact prefixLift 1021600
  have htrace : WordTrace (prefixWord ++ tailWord_1021600) baseStart_1021600 baseEnd_1021600 := by
    simpa [prefixWord, tailWord_1021600, baseEnd_1021600] using wordTrace_append hprefix tailTrace_1021600
  have hstable : (prefixWord ++ tailWord_1021600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021600).length < 2 ^ (prefixWord ++ tailWord_1021600).sum := by decide
  have hdescent : baseEnd_1021600 < baseStart_1021600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021645 : List Nat := [1, 6, 2, 1, 1, 2, 1, 7]
def baseStart_1021645 : Nat := 118140960795 + 1021645 * 2 ^ 59
def prefixEnd_1021645 : Nat := 4983230072969 + 3 ^ 40 * 1021645 * 2
def baseEnd_1021645 : Nat := 77717769372260821176155

theorem tailTrace_1021645 : CollatzResearch.WordTrace tailWord_1021645 prefixEnd_1021645 77717769372260821176155 := by
  unfold tailWord_1021645
  simp only [CollatzResearch.WordTrace]
  refine ⟨37262454383762122919802389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24841636255841415279868259 37262454383762122919802389)
  ·
    refine ⟨1746677549238849511865737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37262454383762122919802389 1746677549238849511865737)
    ·
      refine ⟨1310008161929137133899303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1746677549238849511865737 1310008161929137133899303)
      ·
        refine ⟨1965012242893705700848955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1310008161929137133899303 1965012242893705700848955)
        ·
          refine ⟨2947518364340558551273433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1965012242893705700848955 2947518364340558551273433)
          ·
            refine ⟨2210638773255418913455075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2947518364340558551273433 2210638773255418913455075)
            ·
              refine ⟨3315958159883128370182613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2210638773255418913455075 3315958159883128370182613)
              ·
                refine ⟨77717769372260821176155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3315958159883128370182613 77717769372260821176155)
                ·
                  rfl

theorem cell21_1021645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 7].length) (baseStart_1021645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1021645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1021645 prefixEnd_1021645 := by exact prefixLift 1021645
  have htrace : WordTrace (prefixWord ++ tailWord_1021645) baseStart_1021645 baseEnd_1021645 := by
    simpa [prefixWord, tailWord_1021645, baseEnd_1021645] using wordTrace_append hprefix tailTrace_1021645
  have hstable : (prefixWord ++ tailWord_1021645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021645).length < 2 ^ (prefixWord ++ tailWord_1021645).sum := by decide
  have hdescent : baseEnd_1021645 < baseStart_1021645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021656 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 8]
def baseStart_1021656 : Nat := 118140960795 + 1021656 * 2 ^ 59
def prefixEnd_1021656 : Nat := 4983230072969 + 3 ^ 40 * 1021656 * 2
def baseEnd_1021656 : Nat := 233155818466648888845109

theorem tailTrace_1021656 : CollatzResearch.WordTrace tailWord_1021656 prefixEnd_1021656 233155818466648888845109 := by
  unfold tailWord_1021656
  simp only [CollatzResearch.WordTrace]
  refine ⟨18631427793361135899226411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24841903724481514532301881 18631427793361135899226411)
  ·
    refine ⟨27947141690041703848839617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18631427793361135899226411 27947141690041703848839617)
    ·
      refine ⟨20960356267531277886629713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27947141690041703848839617 20960356267531277886629713)
      ·
        refine ⟨15720267200648458414972285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20960356267531277886629713 15720267200648458414972285)
        ·
          refine ⟨5895100200243171905614607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15720267200648458414972285 5895100200243171905614607)
          ·
            refine ⟨8842650300364757858421911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5895100200243171905614607 8842650300364757858421911)
            ·
              refine ⟨13263975450547136787632867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8842650300364757858421911 13263975450547136787632867)
              ·
                refine ⟨19895963175820705181449301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13263975450547136787632867 19895963175820705181449301)
                ·
                  refine ⟨233155818466648888845109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19895963175820705181449301 233155818466648888845109)
                  ·
                    rfl

theorem cell21_1021656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 8].length) (baseStart_1021656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1021656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1021656 prefixEnd_1021656 := by exact prefixLift 1021656
  have htrace : WordTrace (prefixWord ++ tailWord_1021656) baseStart_1021656 baseEnd_1021656 := by
    simpa [prefixWord, tailWord_1021656, baseEnd_1021656] using wordTrace_append hprefix tailTrace_1021656
  have hstable : (prefixWord ++ tailWord_1021656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021656).length < 2 ^ (prefixWord ++ tailWord_1021656).sum := by decide
  have hdescent : baseEnd_1021656 < baseStart_1021656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021783 : List Nat := [1, 1, 3, 2, 6, 1, 1, 2, 4]
def baseStart_1021783 : Nat := 118140960795 + 1021783 * 2 ^ 59
def prefixEnd_1021783 : Nat := 4983230072969 + 3 ^ 40 * 1021783 * 2
def baseEnd_1021783 : Nat := 233184801596924890228183

theorem tailTrace_1021783 : CollatzResearch.WordTrace tailWord_1021783 prefixEnd_1021783 233184801596924890228183 := by
  unfold tailWord_1021783
  simp only [CollatzResearch.WordTrace]
  refine ⟨37267487657262172488326003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24844991771508114992217335 37267487657262172488326003)
  ·
    refine ⟨55901231485893258732489005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37267487657262172488326003 55901231485893258732489005)
    ·
      refine ⟨20962961807209972024683377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55901231485893258732489005 20962961807209972024683377)
      ·
        refine ⟨15722221355407479018512533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20962961807209972024683377 15722221355407479018512533)
        ·
          refine ⟨736979126034725578992775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15722221355407479018512533 736979126034725578992775)
          ·
            refine ⟨1105468689052088368489163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736979126034725578992775 1105468689052088368489163)
            ·
              refine ⟨1658203033578132552733745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1105468689052088368489163 1658203033578132552733745)
              ·
                refine ⟨1243652275183599414550309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1658203033578132552733745 1243652275183599414550309)
                ·
                  refine ⟨233184801596924890228183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1243652275183599414550309 233184801596924890228183)
                  ·
                    rfl

theorem cell21_1021783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 4].length) (baseStart_1021783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1021783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1021783 prefixEnd_1021783 := by exact prefixLift 1021783
  have htrace : WordTrace (prefixWord ++ tailWord_1021783) baseStart_1021783 baseEnd_1021783 := by
    simpa [prefixWord, tailWord_1021783, baseEnd_1021783] using wordTrace_append hprefix tailTrace_1021783
  have hstable : (prefixWord ++ tailWord_1021783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021783).length < 2 ^ (prefixWord ++ tailWord_1021783).sum := by decide
  have hdescent : baseEnd_1021783 < baseStart_1021783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021814 : List Nat := [5, 1, 1, 3, 2, 2, 2, 5]
def baseStart_1021814 : Nat := 118140960795 + 1021814 * 2 ^ 59
def prefixEnd_1021814 : Nat := 4983230072969 + 3 ^ 40 * 1021814 * 2
def baseEnd_1021814 : Nat := 77730625406425241737151

theorem tailTrace_1021814 : CollatzResearch.WordTrace tailWord_1021814 prefixEnd_1021814 77730625406425241737151 := by
  unfold tailWord_1021814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2329288645009366548919031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24845745546766576521802997 2329288645009366548919031)
  ·
    refine ⟨3493932967514049823378547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2329288645009366548919031 3493932967514049823378547)
    ·
      refine ⟨5240899451271074735067821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3493932967514049823378547 5240899451271074735067821)
      ·
        refine ⟨1965337294226653025650433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5240899451271074735067821 1965337294226653025650433)
        ·
          refine ⟨1474002970669989769237825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1965337294226653025650433 1474002970669989769237825)
          ·
            refine ⟨1105502228002492326928369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1474002970669989769237825 1105502228002492326928369)
            ·
              refine ⟨829126671001869245196277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1105502228002492326928369 829126671001869245196277)
              ·
                refine ⟨77730625406425241737151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 829126671001869245196277 77730625406425241737151)
                ·
                  rfl

theorem cell21_1021814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_1021814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1021814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1021814 prefixEnd_1021814 := by exact prefixLift 1021814
  have htrace : WordTrace (prefixWord ++ tailWord_1021814) baseStart_1021814 baseEnd_1021814 := by
    simpa [prefixWord, tailWord_1021814, baseEnd_1021814] using wordTrace_append hprefix tailTrace_1021814
  have hstable : (prefixWord ++ tailWord_1021814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021814).length < 2 ^ (prefixWord ++ tailWord_1021814).sum := by decide
  have hdescent : baseEnd_1021814 < baseStart_1021814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021960 : List Nat := [2, 1, 3, 2, 1, 2, 3, 1, 6]
def baseStart_1021960 : Nat := 118140960795 + 1021960 * 2 ^ 59
def prefixEnd_1021960 : Nat := 4983230072969 + 3 ^ 40 * 1021960 * 2
def baseEnd_1021960 : Nat := 233225195408411915777821

theorem tailTrace_1021960 : CollatzResearch.WordTrace tailWord_1021960 prefixEnd_1021960 233225195408411915777821 := by
  unfold tailWord_1021960
  simp only [CollatzResearch.WordTrace]
  refine ⟨18636971688810465858759667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24849295585080621145012889 18636971688810465858759667)
  ·
    refine ⟨27955457533215698788139501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18636971688810465858759667 27955457533215698788139501)
    ·
      refine ⟨10483296574955887045552313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27955457533215698788139501 10483296574955887045552313)
      ·
        refine ⟨7862472431216915284164235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10483296574955887045552313 7862472431216915284164235)
        ·
          refine ⟨11793708646825372926246353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7862472431216915284164235 11793708646825372926246353)
          ·
            refine ⟨8845281485119029694684765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11793708646825372926246353 8845281485119029694684765)
            ·
              refine ⟨3316980556919636135506787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8845281485119029694684765 3316980556919636135506787)
              ·
                refine ⟨4975470835379454203260181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3316980556919636135506787 4975470835379454203260181)
                ·
                  refine ⟨233225195408411915777821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4975470835379454203260181 233225195408411915777821)
                  ·
                    rfl

theorem cell21_1021960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 6].length) (baseStart_1021960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1021960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1021960 prefixEnd_1021960 := by exact prefixLift 1021960
  have htrace : WordTrace (prefixWord ++ tailWord_1021960) baseStart_1021960 baseEnd_1021960 := by
    simpa [prefixWord, tailWord_1021960, baseEnd_1021960] using wordTrace_append hprefix tailTrace_1021960
  have hstable : (prefixWord ++ tailWord_1021960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021960).length < 2 ^ (prefixWord ++ tailWord_1021960).sum := by decide
  have hdescent : baseEnd_1021960 < baseStart_1021960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022005 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 7]
def baseStart_1022005 : Nat := 118140960795 + 1022005 * 2 ^ 59
def prefixEnd_1022005 : Nat := 4983230072969 + 3 ^ 40 * 1022005 * 2
def baseEnd_1022005 : Nat := 233235465021501837527729

theorem tailTrace_1022005 : CollatzResearch.WordTrace tailWord_1022005 prefixEnd_1022005 233235465021501837527729 := by
  unfold tailWord_1022005
  simp only [CollatzResearch.WordTrace]
  refine ⟨37275584662457904402907469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24850389774971936268604979 37275584662457904402907469)
  ·
    refine ⟨13978344248421714151090301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37275584662457904402907469 13978344248421714151090301)
    ·
      refine ⟨5241879093158142806658863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13978344248421714151090301 5241879093158142806658863)
      ·
        refine ⟨7862818639737214209988295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5241879093158142806658863 7862818639737214209988295)
        ·
          refine ⟨11794227959605821314982443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7862818639737214209988295 11794227959605821314982443)
          ·
            refine ⟨17691341939408731972473665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11794227959605821314982443 17691341939408731972473665)
            ·
              refine ⟨13268506454556548979355249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17691341939408731972473665 13268506454556548979355249)
              ·
                refine ⟨9951379840917411734516437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13268506454556548979355249 9951379840917411734516437)
                ·
                  refine ⟨233235465021501837527729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9951379840917411734516437 233235465021501837527729)
                  ·
                    rfl

theorem cell21_1022005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_1022005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1022005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1022005 prefixEnd_1022005 := by exact prefixLift 1022005
  have htrace : WordTrace (prefixWord ++ tailWord_1022005) baseStart_1022005 baseEnd_1022005 := by
    simpa [prefixWord, tailWord_1022005, baseEnd_1022005] using wordTrace_append hprefix tailTrace_1022005
  have hstable : (prefixWord ++ tailWord_1022005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022005).length < 2 ^ (prefixWord ++ tailWord_1022005).sum := by decide
  have hdescent : baseEnd_1022005 < baseStart_1022005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022008 : List Nat := [2, 1, 2, 1, 7, 1, 7]
def baseStart_1022008 : Nat := 118140960795 + 1022008 * 2 ^ 59
def prefixEnd_1022008 : Nat := 4983230072969 + 3 ^ 40 * 1022008 * 2
def baseEnd_1022008 : Nat := 25915127740263833219747

theorem tailTrace_1022008 : CollatzResearch.WordTrace tailWord_1022008 prefixEnd_1022008 25915127740263833219747 := by
  unfold tailWord_1022008
  simp only [CollatzResearch.WordTrace]
  refine ⟨18637847040723517957633339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24850462720964690610177785 18637847040723517957633339)
  ·
    refine ⟨27956770561085276936450009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18637847040723517957633339 27956770561085276936450009)
    ·
      refine ⟨20967577920813957702337507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27956770561085276936450009 20967577920813957702337507)
      ·
        refine ⟨31451366881220936553506261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20967577920813957702337507 31451366881220936553506261)
        ·
          refine ⟨737141411278615700472803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 31451366881220936553506261 737141411278615700472803)
          ·
            refine ⟨1105712116917923550709205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737141411278615700472803 1105712116917923550709205)
            ·
              refine ⟨25915127740263833219747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1105712116917923550709205 25915127740263833219747)
              ·
                rfl

theorem cell21_1022008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 7].length) (baseStart_1022008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1022008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1022008 prefixEnd_1022008 := by exact prefixLift 1022008
  have htrace : WordTrace (prefixWord ++ tailWord_1022008) baseStart_1022008 baseEnd_1022008 := by
    simpa [prefixWord, tailWord_1022008, baseEnd_1022008] using wordTrace_append hprefix tailTrace_1022008
  have hstable : (prefixWord ++ tailWord_1022008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022008).length < 2 ^ (prefixWord ++ tailWord_1022008).sum := by decide
  have hdescent : baseEnd_1022008 < baseStart_1022008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022070 : List Nat := [5, 1, 1, 2, 1, 3, 2, 2, 4]
def baseStart_1022070 : Nat := 118140960795 + 1022070 * 2 ^ 59
def prefixEnd_1022070 : Nat := 4983230072969 + 3 ^ 40 * 1022070 * 2
def baseEnd_1022070 : Nat := 233250298907076168944263

theorem tailTrace_1022070 : CollatzResearch.WordTrace tailWord_1022070 prefixEnd_1022070 233250298907076168944263 := by
  unfold tailWord_1022070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2329872212951401281501479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24851970271481613669349109 2329872212951401281501479)
  ·
    refine ⟨3494808319427101922252219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2329872212951401281501479 3494808319427101922252219)
    ·
      refine ⟨5242212479140652883378329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3494808319427101922252219 5242212479140652883378329)
      ·
        refine ⟨3931659359355489662533747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5242212479140652883378329 3931659359355489662533747)
        ·
          refine ⟨5897489039033234493800621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3931659359355489662533747 5897489039033234493800621)
          ·
            refine ⟨2211558389637462935175233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5897489039033234493800621 2211558389637462935175233)
            ·
              refine ⟨1658668792228097201381425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2211558389637462935175233 1658668792228097201381425)
              ·
                refine ⟨1244001594171072901036069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1658668792228097201381425 1244001594171072901036069)
                ·
                  refine ⟨233250298907076168944263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1244001594171072901036069 233250298907076168944263)
                  ·
                    rfl

theorem cell21_1022070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_1022070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1022070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1022070 prefixEnd_1022070 := by exact prefixLift 1022070
  have htrace : WordTrace (prefixWord ++ tailWord_1022070) baseStart_1022070 baseEnd_1022070 := by
    simpa [prefixWord, tailWord_1022070, baseEnd_1022070] using wordTrace_append hprefix tailTrace_1022070
  have hstable : (prefixWord ++ tailWord_1022070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022070).length < 2 ^ (prefixWord ++ tailWord_1022070).sum := by decide
  have hdescent : baseEnd_1022070 < baseStart_1022070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022098 : List Nat := [3, 2, 3, 1, 1, 1, 3, 2, 5]
def baseStart_1022098 : Nat := 118140960795 + 1022098 * 2 ^ 59
def prefixEnd_1022098 : Nat := 4983230072969 + 3 ^ 40 * 1022098 * 2
def baseEnd_1022098 : Nat := 233256688888554342477539

theorem tailTrace_1022098 : CollatzResearch.WordTrace tailWord_1022098 prefixEnd_1022098 233256688888554342477539 := by
  unfold tailWord_1022098
  simp only [CollatzResearch.WordTrace]
  refine ⟨9319744162780245321510737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24852651100747320857361965 9319744162780245321510737)
  ·
    refine ⟨6989808122085183991133053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9319744162780245321510737 6989808122085183991133053)
    ·
      refine ⟨2621178045781943996674895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6989808122085183991133053 2621178045781943996674895)
      ·
        refine ⟨3931767068672915995012343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2621178045781943996674895 3931767068672915995012343)
        ·
          refine ⟨5897650603009373992518515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3931767068672915995012343 5897650603009373992518515)
          ·
            refine ⟨8846475904514060988777773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5897650603009373992518515 8846475904514060988777773)
            ·
              refine ⟨3317428464192772870791665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8846475904514060988777773 3317428464192772870791665)
              ·
                refine ⟨2488071348144579653093749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3317428464192772870791665 2488071348144579653093749)
                ·
                  refine ⟨233256688888554342477539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2488071348144579653093749 233256688888554342477539)
                  ·
                    rfl

theorem cell21_1022098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_1022098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1022098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1022098 prefixEnd_1022098 := by exact prefixLift 1022098
  have htrace : WordTrace (prefixWord ++ tailWord_1022098) baseStart_1022098 baseEnd_1022098 := by
    simpa [prefixWord, tailWord_1022098, baseEnd_1022098] using wordTrace_append hprefix tailTrace_1022098
  have hstable : (prefixWord ++ tailWord_1022098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022098).length < 2 ^ (prefixWord ++ tailWord_1022098).sum := by decide
  have hdescent : baseEnd_1022098 < baseStart_1022098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022129 : List Nat := [1, 2, 2, 5, 2, 1, 1, 1, 6]
def baseStart_1022129 : Nat := 118140960795 + 1022129 * 2 ^ 59
def prefixEnd_1022129 : Nat := 4983230072969 + 3 ^ 40 * 1022129 * 2
def baseEnd_1022129 : Nat := 233263763510905177460809

theorem tailTrace_1022129 : CollatzResearch.WordTrace tailWord_1022129 prefixEnd_1022129 233263763510905177460809 := by
  unfold tailWord_1022129
  simp only [CollatzResearch.WordTrace]
  refine ⟨37280107314008673580421441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24853404876005782386947627 37280107314008673580421441)
  ·
    refine ⟨27960080485506505185316081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37280107314008673580421441 27960080485506505185316081)
    ·
      refine ⟨20970060364129878888987061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27960080485506505185316081 20970060364129878888987061)
      ·
        refine ⟨1965943159137176145842537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20970060364129878888987061 1965943159137176145842537)
        ·
          refine ⟨1474457369352882109381903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1965943159137176145842537 1474457369352882109381903)
          ·
            refine ⟨2211686054029323164072855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1474457369352882109381903 2211686054029323164072855)
            ·
              refine ⟨3317529081043984746109283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2211686054029323164072855 3317529081043984746109283)
              ·
                refine ⟨4976293621565977119163925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3317529081043984746109283 4976293621565977119163925)
                ·
                  refine ⟨233263763510905177460809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4976293621565977119163925 233263763510905177460809)
                  ·
                    rfl

theorem cell21_1022129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 6].length) (baseStart_1022129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1022129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1022129 prefixEnd_1022129 := by exact prefixLift 1022129
  have htrace : WordTrace (prefixWord ++ tailWord_1022129) baseStart_1022129 baseEnd_1022129 := by
    simpa [prefixWord, tailWord_1022129, baseEnd_1022129] using wordTrace_append hprefix tailTrace_1022129
  have hstable : (prefixWord ++ tailWord_1022129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022129).length < 2 ^ (prefixWord ++ tailWord_1022129).sum := by decide
  have hdescent : baseEnd_1022129 < baseStart_1022129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022171 : List Nat := [1, 1, 1, 1, 1, 1, 1, 8, 6]
def baseStart_1022171 : Nat := 118140960795 + 1022171 * 2 ^ 59
def prefixEnd_1022171 : Nat := 4983230072969 + 3 ^ 40 * 1022171 * 2
def baseEnd_1022171 : Nat := 233273348483122437760723

theorem tailTrace_1022171 : CollatzResearch.WordTrace tailWord_1022171 prefixEnd_1022171 233273348483122437760723 := by
  unfold tailWord_1022171
  simp only [CollatzResearch.WordTrace]
  refine ⟨37281639179856514753450367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24854426119904343168966911 37281639179856514753450367)
  ·
    refine ⟨55922458769784772130175551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37281639179856514753450367 55922458769784772130175551)
    ·
      refine ⟨83883688154677158195263327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55922458769784772130175551 83883688154677158195263327)
      ·
        refine ⟨125825532232015737292894991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83883688154677158195263327 125825532232015737292894991)
        ·
          refine ⟨188738298348023605939342487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125825532232015737292894991 188738298348023605939342487)
          ·
            refine ⟨283107447522035408909013731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188738298348023605939342487 283107447522035408909013731)
            ·
              refine ⟨424661171283053113363520597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283107447522035408909013731 424661171283053113363520597)
              ·
                refine ⟨4976498100973278672228757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 424661171283053113363520597 4976498100973278672228757)
                ·
                  refine ⟨233273348483122437760723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4976498100973278672228757 233273348483122437760723)
                  ·
                    rfl

theorem cell21_1022171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 6].length) (baseStart_1022171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1022171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1022171 prefixEnd_1022171 := by exact prefixLift 1022171
  have htrace : WordTrace (prefixWord ++ tailWord_1022171) baseStart_1022171 baseEnd_1022171 := by
    simpa [prefixWord, tailWord_1022171, baseEnd_1022171] using wordTrace_append hprefix tailTrace_1022171
  have hstable : (prefixWord ++ tailWord_1022171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022171).length < 2 ^ (prefixWord ++ tailWord_1022171).sum := by decide
  have hdescent : baseEnd_1022171 < baseStart_1022171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022188 : List Nat := [2, 2, 1, 1, 2, 3, 2, 4, 4]
def baseStart_1022188 : Nat := 118140960795 + 1022188 * 2 ^ 59
def prefixEnd_1022188 : Nat := 4983230072969 + 3 ^ 40 * 1022188 * 2
def baseEnd_1022188 : Nat := 233277228114734185977355

theorem tailTrace_1022188 : CollatzResearch.WordTrace tailWord_1022188 prefixEnd_1022188 233277228114734185977355 := by
  unfold tailWord_1022188
  simp only [CollatzResearch.WordTrace]
  refine ⟨18641129610397463328409609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24854839480529951104546145 18641129610397463328409609)
  ·
    refine ⟨13980847207798097496307207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18641129610397463328409609 13980847207798097496307207)
    ·
      refine ⟨20971270811697146244460811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13980847207798097496307207 20971270811697146244460811)
      ·
        refine ⟨31456906217545719366691217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20971270811697146244460811 31456906217545719366691217)
        ·
          refine ⟨23592679663159289525018413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31456906217545719366691217 23592679663159289525018413)
          ·
            refine ⟨8847254873684733571881905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23592679663159289525018413 8847254873684733571881905)
            ·
              refine ⟨6635441155263550178911429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8847254873684733571881905 6635441155263550178911429)
              ·
                refine ⟨1244145216611915658545893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6635441155263550178911429 1244145216611915658545893)
                ·
                  refine ⟨233277228114734185977355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1244145216611915658545893 233277228114734185977355)
                  ·
                    rfl

theorem cell21_1022188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_1022188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1022188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1022188 prefixEnd_1022188 := by exact prefixLift 1022188
  have htrace : WordTrace (prefixWord ++ tailWord_1022188) baseStart_1022188 baseEnd_1022188 := by
    simpa [prefixWord, tailWord_1022188, baseEnd_1022188] using wordTrace_append hprefix tailTrace_1022188
  have hstable : (prefixWord ++ tailWord_1022188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022188).length < 2 ^ (prefixWord ++ tailWord_1022188).sum := by decide
  have hdescent : baseEnd_1022188 < baseStart_1022188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022202 : List Nat := [3, 1, 1, 1, 1, 5, 1, 8]
def baseStart_1022202 : Nat := 118140960795 + 1022202 * 2 ^ 59
def prefixEnd_1022202 : Nat := 4983230072969 + 3 ^ 40 * 1022202 * 2
def baseEnd_1022202 : Nat := 77760141035157757581331

theorem tailTrace_1022202 : CollatzResearch.WordTrace tailWord_1022202 prefixEnd_1022202 77760141035157757581331 := by
  unfold tailWord_1022202
  simp only [CollatzResearch.WordTrace]
  refine ⟨9320692460686051761957215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24855179895162804698552573 9320692460686051761957215)
  ·
    refine ⟨13981038691029077642935823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9320692460686051761957215 13981038691029077642935823)
    ·
      refine ⟨20971558036543616464403735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13981038691029077642935823 20971558036543616464403735)
      ·
        refine ⟨31457337054815424696605603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20971558036543616464403735 31457337054815424696605603)
        ·
          refine ⟨47186005582223137044908405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31457337054815424696605603 47186005582223137044908405)
          ·
            refine ⟨4423688023333419097960163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47186005582223137044908405 4423688023333419097960163)
            ·
              refine ⟨6635532035000128646940245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4423688023333419097960163 6635532035000128646940245)
              ·
                refine ⟨77760141035157757581331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6635532035000128646940245 77760141035157757581331)
                ·
                  rfl

theorem cell21_1022202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 8].length) (baseStart_1022202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1022202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1022202 prefixEnd_1022202 := by exact prefixLift 1022202
  have htrace : WordTrace (prefixWord ++ tailWord_1022202) baseStart_1022202 baseEnd_1022202 := by
    simpa [prefixWord, tailWord_1022202, baseEnd_1022202] using wordTrace_append hprefix tailTrace_1022202
  have hstable : (prefixWord ++ tailWord_1022202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022202).length < 2 ^ (prefixWord ++ tailWord_1022202).sum := by decide
  have hdescent : baseEnd_1022202 < baseStart_1022202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022253 : List Nat := [1, 5, 3, 1, 2, 2, 1, 6]
def baseStart_1022253 : Nat := 118140960795 + 1022253 * 2 ^ 59
def prefixEnd_1022253 : Nat := 4983230072969 + 3 ^ 40 * 1022253 * 2
def baseEnd_1022253 : Nat := 77764020666769505797963

theorem tailTrace_1022253 : CollatzResearch.WordTrace tailWord_1022253 prefixEnd_1022253 77764020666769505797963 := by
  unfold tailWord_1022253
  simp only [CollatzResearch.WordTrace]
  refine ⟨37284629965559442757935413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24856419977039628505290275 37284629965559442757935413)
  ·
    refine ⟨3495434059271197758556445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37284629965559442757935413 3495434059271197758556445)
    ·
      refine ⟨1310787772226699159458667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3495434059271197758556445 1310787772226699159458667)
      ·
        refine ⟨1966181658340048739188001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1310787772226699159458667 1966181658340048739188001)
        ·
          refine ⟨1474636243755036554391001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1966181658340048739188001 1474636243755036554391001)
          ·
            refine ⟨1105977182816277415793251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1474636243755036554391001 1105977182816277415793251)
            ·
              refine ⟨1658965774224416123689877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1105977182816277415793251 1658965774224416123689877)
              ·
                refine ⟨77764020666769505797963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1658965774224416123689877 77764020666769505797963)
                ·
                  rfl

theorem cell21_1022253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 6].length) (baseStart_1022253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1022253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1022253 prefixEnd_1022253 := by exact prefixLift 1022253
  have htrace : WordTrace (prefixWord ++ tailWord_1022253) baseStart_1022253 baseEnd_1022253 := by
    simpa [prefixWord, tailWord_1022253, baseEnd_1022253] using wordTrace_append hprefix tailTrace_1022253
  have hstable : (prefixWord ++ tailWord_1022253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022253).length < 2 ^ (prefixWord ++ tailWord_1022253).sum := by decide
  have hdescent : baseEnd_1022253 < baseStart_1022253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022264 : List Nat := [2, 1, 2, 1, 3, 1, 4, 3, 4]
def baseStart_1022264 : Nat := 118140960795 + 1022264 * 2 ^ 59
def prefixEnd_1022264 : Nat := 4983230072969 + 3 ^ 40 * 1022264 * 2
def baseEnd_1022264 : Nat := 233294572350174942710533

theorem tailTrace_1022264 : CollatzResearch.WordTrace tailWord_1022264 prefixEnd_1022264 233294572350174942710533 := by
  unfold tailWord_1022264
  simp only [CollatzResearch.WordTrace]
  refine ⟨18642515584259795818292923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24856687445679727757723897 18642515584259795818292923)
  ·
    refine ⟨27963773376389693727439385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18642515584259795818292923 27963773376389693727439385)
    ·
      refine ⟨20972830032292270295579539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27963773376389693727439385 20972830032292270295579539)
      ·
        refine ⟨31459245048438405443369309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20972830032292270295579539 31459245048438405443369309)
        ·
          refine ⟨11797216893164402041263491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31459245048438405443369309 11797216893164402041263491)
          ·
            refine ⟨17695825339746603061895237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11797216893164402041263491 17695825339746603061895237)
            ·
              refine ⟨3317967251202488074105357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17695825339746603061895237 3317967251202488074105357)
              ·
                refine ⟨1244237719200933027789509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3317967251202488074105357 1244237719200933027789509)
                ·
                  refine ⟨233294572350174942710533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1244237719200933027789509 233294572350174942710533)
                  ·
                    rfl

theorem cell21_1022264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 4].length) (baseStart_1022264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1022264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1022264 prefixEnd_1022264 := by exact prefixLift 1022264
  have htrace : WordTrace (prefixWord ++ tailWord_1022264) baseStart_1022264 baseEnd_1022264 := by
    simpa [prefixWord, tailWord_1022264, baseEnd_1022264] using wordTrace_append hprefix tailTrace_1022264
  have hstable : (prefixWord ++ tailWord_1022264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022264).length < 2 ^ (prefixWord ++ tailWord_1022264).sum := by decide
  have hdescent : baseEnd_1022264 < baseStart_1022264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022309 : List Nat := [1, 3, 1, 3, 1, 3, 1, 3, 5]
def baseStart_1022309 : Nat := 118140960795 + 1022309 * 2 ^ 59
def prefixEnd_1022309 : Nat := 4983230072969 + 3 ^ 40 * 1022309 * 2
def baseEnd_1022309 : Nat := 233304841963264864460441

theorem tailTrace_1022309 : CollatzResearch.WordTrace tailWord_1022309 prefixEnd_1022309 233304841963264864460441 := by
  unfold tailWord_1022309
  simp only [CollatzResearch.WordTrace]
  refine ⟨37286672453356564321973981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24857781635571042881315987 37286672453356564321973981)
  ·
    refine ⟨13982502170008711620740243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37286672453356564321973981 13982502170008711620740243)
    ·
      refine ⟨20973753255013067431110365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13982502170008711620740243 20973753255013067431110365)
      ·
        refine ⟨7865157470629900286666387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20973753255013067431110365 7865157470629900286666387)
        ·
          refine ⟨11797736205944850429999581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7865157470629900286666387 11797736205944850429999581)
          ·
            refine ⟨4424151077229318911249843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11797736205944850429999581 4424151077229318911249843)
            ·
              refine ⟨6636226615843978366874765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4424151077229318911249843 6636226615843978366874765)
              ·
                refine ⟨2488584980941491887578037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6636226615843978366874765 2488584980941491887578037)
                ·
                  refine ⟨233304841963264864460441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2488584980941491887578037 233304841963264864460441)
                  ·
                    rfl

theorem cell21_1022309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_1022309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1022309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1022309 prefixEnd_1022309 := by exact prefixLift 1022309
  have htrace : WordTrace (prefixWord ++ tailWord_1022309) baseStart_1022309 baseEnd_1022309 := by
    simpa [prefixWord, tailWord_1022309, baseEnd_1022309] using wordTrace_append hprefix tailTrace_1022309
  have hstable : (prefixWord ++ tailWord_1022309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022309).length < 2 ^ (prefixWord ++ tailWord_1022309).sum := by decide
  have hdescent : baseEnd_1022309 < baseStart_1022309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022360 : List Nat := [2, 1, 2, 5, 1, 2, 3, 2, 3]
def baseStart_1022360 : Nat := 118140960795 + 1022360 * 2 ^ 59
def prefixEnd_1022360 : Nat := 4983230072969 + 3 ^ 40 * 1022360 * 2
def baseEnd_1022360 : Nat := 233316480858100109110337

theorem tailTrace_1022360 : CollatzResearch.WordTrace tailWord_1022360 prefixEnd_1022360 233316480858100109110337 := by
  unfold tailWord_1022360
  simp only [CollatzResearch.WordTrace]
  refine ⟨18644266288085900016040267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24859021717447866688053689 18644266288085900016040267)
  ·
    refine ⟨27966399432128850024060401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18644266288085900016040267 27966399432128850024060401)
    ·
      refine ⟨20974799574096637518045301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27966399432128850024060401 20974799574096637518045301)
      ·
        refine ⟨1966387460071559767316747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20974799574096637518045301 1966387460071559767316747)
        ·
          refine ⟨2949581190107339650975121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1966387460071559767316747 2949581190107339650975121)
          ·
            refine ⟨2212185892580504738231341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2949581190107339650975121 2212185892580504738231341)
            ·
              refine ⟨829569709717689276836753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2212185892580504738231341 829569709717689276836753)
              ·
                refine ⟨622177282288266957627565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 829569709717689276836753 622177282288266957627565)
                ·
                  refine ⟨233316480858100109110337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 622177282288266957627565 233316480858100109110337)
                  ·
                    rfl

theorem cell21_1022360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 2, 3].length) (baseStart_1022360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1022360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1022360 prefixEnd_1022360 := by exact prefixLift 1022360
  have htrace : WordTrace (prefixWord ++ tailWord_1022360) baseStart_1022360 baseEnd_1022360 := by
    simpa [prefixWord, tailWord_1022360, baseEnd_1022360] using wordTrace_append hprefix tailTrace_1022360
  have hstable : (prefixWord ++ tailWord_1022360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022360).length < 2 ^ (prefixWord ++ tailWord_1022360).sum := by decide
  have hdescent : baseEnd_1022360 < baseStart_1022360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022478 : List Nat := [4, 1, 1, 2, 3, 2, 2, 1, 5]
def baseStart_1022478 : Nat := 118140960795 + 1022478 * 2 ^ 59
def prefixEnd_1022478 : Nat := 4983230072969 + 3 ^ 40 * 1022478 * 2
def baseEnd_1022478 : Nat := 233343410065758126143429

theorem tailTrace_1022478 : CollatzResearch.WordTrace tailWord_1022478 prefixEnd_1022478 233343410065758126143429 := by
  unfold tailWord_1022478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4661604548718038273109511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24861890926496204123250725 4661604548718038273109511)
  ·
    refine ⟨6992406823077057409664267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4661604548718038273109511 6992406823077057409664267)
    ·
      refine ⟨10488610234615586114496401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6992406823077057409664267 10488610234615586114496401)
      ·
        refine ⟨7866457675961689585872301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10488610234615586114496401 7866457675961689585872301)
        ·
          refine ⟨2949921628485633594702113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7866457675961689585872301 2949921628485633594702113)
          ·
            refine ⟨2212441221364225196026585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2949921628485633594702113 2212441221364225196026585)
            ·
              refine ⟨1659330916023168897019939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2212441221364225196026585 1659330916023168897019939)
              ·
                refine ⟨2488996374034753345529909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1659330916023168897019939 2488996374034753345529909)
                ·
                  refine ⟨233343410065758126143429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2488996374034753345529909 233343410065758126143429)
                  ·
                    rfl

theorem cell21_1022478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_1022478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1022478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1022478 prefixEnd_1022478 := by exact prefixLift 1022478
  have htrace : WordTrace (prefixWord ++ tailWord_1022478) baseStart_1022478 baseEnd_1022478 := by
    simpa [prefixWord, tailWord_1022478, baseEnd_1022478] using wordTrace_append hprefix tailTrace_1022478
  have hstable : (prefixWord ++ tailWord_1022478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022478).length < 2 ^ (prefixWord ++ tailWord_1022478).sum := by decide
  have hdescent : baseEnd_1022478 < baseStart_1022478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022582 : List Nat := [5, 1, 1, 2, 12]
def baseStart_1022582 : Nat := 118140960795 + 1022582 * 2 ^ 59
def prefixEnd_1022582 : Nat := 4983230072969 + 3 ^ 40 * 1022582 * 2
def baseEnd_1022582 : Nat := 2881075855341692054443

theorem tailTrace_1022582 : CollatzResearch.WordTrace tailWord_1022582 prefixEnd_1022582 2881075855341692054443 := by
  unfold tailWord_1022582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2331039348835470746666375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24864419720911687964441333 2331039348835470746666375)
  ·
    refine ⟨3496559023253206119999563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2331039348835470746666375 3496559023253206119999563)
    ·
      refine ⟨5244838534879809179999345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3496559023253206119999563 5244838534879809179999345)
      ·
        refine ⟨3933628901159856884999509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5244838534879809179999345 3933628901159856884999509)
        ·
          refine ⟨2881075855341692054443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3933628901159856884999509 2881075855341692054443)
          ·
            rfl

theorem cell21_1022582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 12].length) (baseStart_1022582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1022582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1022582 prefixEnd_1022582 := by exact prefixLift 1022582
  have htrace : WordTrace (prefixWord ++ tailWord_1022582) baseStart_1022582 baseEnd_1022582 := by
    simpa [prefixWord, tailWord_1022582, baseEnd_1022582] using wordTrace_append hprefix tailTrace_1022582
  have hstable : (prefixWord ++ tailWord_1022582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022582).length < 2 ^ (prefixWord ++ tailWord_1022582).sum := by decide
  have hdescent : baseEnd_1022582 < baseStart_1022582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022703 : List Nat := [1, 1, 2, 1, 5, 2, 2, 1, 6]
def baseStart_1022703 : Nat := 118140960795 + 1022703 * 2 ^ 59
def prefixEnd_1022703 : Nat := 4983230072969 + 3 ^ 40 * 1022703 * 2
def baseEnd_1022703 : Nat := 233394758131207734892969

theorem tailTrace_1022703 : CollatzResearch.WordTrace tailWord_1022703 prefixEnd_1022703 233394758131207734892969 := by
  unfold tailWord_1022703
  simp only [CollatzResearch.WordTrace]
  refine ⟨37301042813929169611816763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24867361875952779741211175 37301042813929169611816763)
  ·
    refine ⟨55951564220893754417725145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37301042813929169611816763 55951564220893754417725145)
    ·
      refine ⟨41963673165670315813293859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55951564220893754417725145 41963673165670315813293859)
      ·
        refine ⟨62945509748505473719940789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41963673165670315813293859 62945509748505473719940789)
        ·
          refine ⟨5901141538922388161244449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62945509748505473719940789 5901141538922388161244449)
          ·
            refine ⟨4425856154191791120933337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5901141538922388161244449 4425856154191791120933337)
            ·
              refine ⟨3319392115643843340700003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4425856154191791120933337 3319392115643843340700003)
              ·
                refine ⟨4979088173465765011050005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3319392115643843340700003 4979088173465765011050005)
                ·
                  refine ⟨233394758131207734892969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4979088173465765011050005 233394758131207734892969)
                  ·
                    rfl

theorem cell21_1022703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 6].length) (baseStart_1022703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1022703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1022703 prefixEnd_1022703 := by exact prefixLift 1022703
  have htrace : WordTrace (prefixWord ++ tailWord_1022703) baseStart_1022703 baseEnd_1022703 := by
    simpa [prefixWord, tailWord_1022703, baseEnd_1022703] using wordTrace_append hprefix tailTrace_1022703
  have hstable : (prefixWord ++ tailWord_1022703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022703).length < 2 ^ (prefixWord ++ tailWord_1022703).sum := by decide
  have hdescent : baseEnd_1022703 < baseStart_1022703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022706 : List Nat := [3, 2, 1, 3, 1, 4, 1, 1, 5]
def baseStart_1022706 : Nat := 118140960795 + 1022706 * 2 ^ 59
def prefixEnd_1022706 : Nat := 4983230072969 + 3 ^ 40 * 1022706 * 2
def baseEnd_1022706 : Nat := 233395442772080396342963

theorem tailTrace_1022706 : CollatzResearch.WordTrace tailWord_1022706 prefixEnd_1022706 233395442772080396342963 := by
  unfold tailWord_1022706
  simp only [CollatzResearch.WordTrace]
  refine ⟨9325288058229575281043993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24867434821945534082783981 9325288058229575281043993)
  ·
    refine ⟨6993966043672181460782995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9325288058229575281043993 6993966043672181460782995)
    ·
      refine ⟨10490949065508272191174493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6993966043672181460782995 10490949065508272191174493)
      ·
        refine ⟨3934105899565602071690435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10490949065508272191174493 3934105899565602071690435)
        ·
          refine ⟨5901158849348403107535653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3934105899565602071690435 5901158849348403107535653)
          ·
            refine ⟨1106467284252825582662935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5901158849348403107535653 1106467284252825582662935)
            ·
              refine ⟨1659700926379238373994403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1106467284252825582662935 1659700926379238373994403)
              ·
                refine ⟨2489551389568857560991605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1659700926379238373994403 2489551389568857560991605)
                ·
                  refine ⟨233395442772080396342963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2489551389568857560991605 233395442772080396342963)
                  ·
                    rfl

theorem cell21_1022706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_1022706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1022706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1022706 prefixEnd_1022706 := by exact prefixLift 1022706
  have htrace : WordTrace (prefixWord ++ tailWord_1022706) baseStart_1022706 baseEnd_1022706 := by
    simpa [prefixWord, tailWord_1022706, baseEnd_1022706] using wordTrace_append hprefix tailTrace_1022706
  have hstable : (prefixWord ++ tailWord_1022706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022706).length < 2 ^ (prefixWord ++ tailWord_1022706).sum := by decide
  have hdescent : baseEnd_1022706 < baseStart_1022706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022709 : List Nat := [1, 3, 6, 1, 1, 1, 2, 6]
def baseStart_1022709 : Nat := 118140960795 + 1022709 * 2 ^ 59
def prefixEnd_1022709 : Nat := 4983230072969 + 3 ^ 40 * 1022709 * 2
def baseEnd_1022709 : Nat := 77798709137651019264319

theorem tailTrace_1022709 : CollatzResearch.WordTrace tailWord_1022709 prefixEnd_1022709 77798709137651019264319 := by
  unfold tailWord_1022709
  simp only [CollatzResearch.WordTrace]
  refine ⟨37301261651907432636535181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24867507767938288424356787 37301261651907432636535181)
  ·
    refine ⟨13987973119465287238700693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37301261651907432636535181 13987973119465287238700693)
    ·
      refine ⟨655686239974935339314095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13987973119465287238700693 655686239974935339314095)
      ·
        refine ⟨983529359962403008971143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655686239974935339314095 983529359962403008971143)
        ·
          refine ⟨1475294039943604513456715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 983529359962403008971143 1475294039943604513456715)
          ·
            refine ⟨2212941059915406770185073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1475294039943604513456715 2212941059915406770185073)
            ·
              refine ⟨1659705794936555077638805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2212941059915406770185073 1659705794936555077638805)
              ·
                refine ⟨77798709137651019264319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1659705794936555077638805 77798709137651019264319)
                ·
                  rfl

theorem cell21_1022709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 6].length) (baseStart_1022709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1022709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1022709 prefixEnd_1022709 := by exact prefixLift 1022709
  have htrace : WordTrace (prefixWord ++ tailWord_1022709) baseStart_1022709 baseEnd_1022709 := by
    simpa [prefixWord, tailWord_1022709, baseEnd_1022709] using wordTrace_append hprefix tailTrace_1022709
  have hstable : (prefixWord ++ tailWord_1022709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022709).length < 2 ^ (prefixWord ++ tailWord_1022709).sum := by decide
  have hdescent : baseEnd_1022709 < baseStart_1022709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022782 : List Nat := [4, 2, 1, 2, 3, 1, 1, 2, 5]
def baseStart_1022782 : Nat := 118140960795 + 1022782 * 2 ^ 59
def prefixEnd_1022782 : Nat := 4983230072969 + 3 ^ 40 * 1022782 * 2
def baseEnd_1022782 : Nat := 233412787007521153076141

theorem tailTrace_1022782 : CollatzResearch.WordTrace tailWord_1022782 prefixEnd_1022782 233412787007521153076141 := by
  unfold tailWord_1022782
  simp only [CollatzResearch.WordTrace]
  refine ⟨4662990522580370762992825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24869282787095310735961733 4662990522580370762992825)
  ·
    refine ⟨3497242891935278072244619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4662990522580370762992825 3497242891935278072244619)
    ·
      refine ⟨5245864337902917108366929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3497242891935278072244619 5245864337902917108366929)
      ·
        refine ⟨3934398253427187831275197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5245864337902917108366929 3934398253427187831275197)
        ·
          refine ⟨1475399345035195436728199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3934398253427187831275197 1475399345035195436728199)
          ·
            refine ⟨2213099017552793155092299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1475399345035195436728199 2213099017552793155092299)
            ·
              refine ⟨3319648526329189732638449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2213099017552793155092299 3319648526329189732638449)
              ·
                refine ⟨2489736394746892299478837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3319648526329189732638449 2489736394746892299478837)
                ·
                  refine ⟨233412787007521153076141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2489736394746892299478837 233412787007521153076141)
                  ·
                    rfl

theorem cell21_1022782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_1022782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1022782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1022782 prefixEnd_1022782 := by exact prefixLift 1022782
  have htrace : WordTrace (prefixWord ++ tailWord_1022782) baseStart_1022782 baseEnd_1022782 := by
    simpa [prefixWord, tailWord_1022782, baseEnd_1022782] using wordTrace_append hprefix tailTrace_1022782
  have hstable : (prefixWord ++ tailWord_1022782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022782).length < 2 ^ (prefixWord ++ tailWord_1022782).sum := by decide
  have hdescent : baseEnd_1022782 < baseStart_1022782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022830 : List Nat := [4, 1, 2, 3, 2, 1, 3, 1, 4]
def baseStart_1022830 : Nat := 118140960795 + 1022830 * 2 ^ 59
def prefixEnd_1022830 : Nat := 4983230072969 + 3 ^ 40 * 1022830 * 2
def baseEnd_1022830 : Nat := 233423741261483736276043

theorem tailTrace_1022830 : CollatzResearch.WordTrace tailWord_1022830 prefixEnd_1022830 233423741261483736276043 := by
  unfold tailWord_1022830
  simp only [CollatzResearch.WordTrace]
  refine ⟨4663209360558633787711243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24870449922979380201126629 4663209360558633787711243)
  ·
    refine ⟨6994814040837950681566865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4663209360558633787711243 6994814040837950681566865)
    ·
      refine ⟨5246110530628463011175149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6994814040837950681566865 5246110530628463011175149)
      ·
        refine ⟨1967291448985673629190681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5246110530628463011175149 1967291448985673629190681)
        ·
          refine ⟨1475468586739255221893011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1967291448985673629190681 1475468586739255221893011)
          ·
            refine ⟨2213202880108882832839517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1475468586739255221893011 2213202880108882832839517)
            ·
              refine ⟨829951080040831062314819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2213202880108882832839517 829951080040831062314819)
              ·
                refine ⟨1244926620061246593472229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 829951080040831062314819 1244926620061246593472229)
                ·
                  refine ⟨233423741261483736276043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1244926620061246593472229 233423741261483736276043)
                  ·
                    rfl

theorem cell21_1022830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_1022830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1022830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1022830 prefixEnd_1022830 := by exact prefixLift 1022830
  have htrace : WordTrace (prefixWord ++ tailWord_1022830) baseStart_1022830 baseEnd_1022830 := by
    simpa [prefixWord, tailWord_1022830, baseEnd_1022830] using wordTrace_append hprefix tailTrace_1022830
  have hstable : (prefixWord ++ tailWord_1022830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022830).length < 2 ^ (prefixWord ++ tailWord_1022830).sum := by decide
  have hdescent : baseEnd_1022830 < baseStart_1022830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022850 : List Nat := [3, 4, 2, 2, 2, 1, 1, 3, 3]
def baseStart_1022850 : Nat := 118140960795 + 1022850 * 2 ^ 59
def prefixEnd_1022850 : Nat := 4983230072969 + 3 ^ 40 * 1022850 * 2
def baseEnd_1022850 : Nat := 233428305533968145942669

theorem tailTrace_1022850 : CollatzResearch.WordTrace tailWord_1022850 prefixEnd_1022850 233428305533968145942669 := by
  unfold tailWord_1022850
  simp only [CollatzResearch.WordTrace]
  refine ⟨9326601086099153429354501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24870936229597742478278669 9326601086099153429354501)
  ·
    refine ⟨1748737703643591268003969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9326601086099153429354501 1748737703643591268003969)
    ·
      refine ⟨1311553277732693451002977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1748737703643591268003969 1311553277732693451002977)
      ·
        refine ⟨983664958299520088252233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1311553277732693451002977 983664958299520088252233)
        ·
          refine ⟨737748718724640066189175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 983664958299520088252233 737748718724640066189175)
          ·
            refine ⟨1106623078086960099283763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737748718724640066189175 1106623078086960099283763)
            ·
              refine ⟨1659934617130440148925645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1106623078086960099283763 1659934617130440148925645)
              ·
                refine ⟨622475481423915055847117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1659934617130440148925645 622475481423915055847117)
                ·
                  refine ⟨233428305533968145942669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 622475481423915055847117 233428305533968145942669)
                  ·
                    rfl

theorem cell21_1022850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_1022850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1022850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1022850 prefixEnd_1022850 := by exact prefixLift 1022850
  have htrace : WordTrace (prefixWord ++ tailWord_1022850) baseStart_1022850 baseEnd_1022850 := by
    simpa [prefixWord, tailWord_1022850, baseEnd_1022850] using wordTrace_append hprefix tailTrace_1022850
  have hstable : (prefixWord ++ tailWord_1022850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022850).length < 2 ^ (prefixWord ++ tailWord_1022850).sum := by decide
  have hdescent : baseEnd_1022850 < baseStart_1022850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022855 : List Nat := [1, 1, 4, 2, 3, 1, 1, 2, 6]
def baseStart_1022855 : Nat := 118140960795 + 1022855 * 2 ^ 59
def prefixEnd_1022855 : Nat := 4983230072969 + 3 ^ 40 * 1022855 * 2
def baseEnd_1022855 : Nat := 233429446602089248359325

theorem tailTrace_1022855 : CollatzResearch.WordTrace tailWord_1022855 prefixEnd_1022855 233429446602089248359325 := by
  unfold tailWord_1022855
  simp only [CollatzResearch.WordTrace]
  refine ⟨37306586709378499571350019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24871057806252333047566679 37306586709378499571350019)
  ·
    refine ⟨55959880064067749357025029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37306586709378499571350019 55959880064067749357025029)
    ·
      refine ⟨10492477512012703004442193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55959880064067749357025029 10492477512012703004442193)
      ·
        refine ⟨7869358134009527253331645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10492477512012703004442193 7869358134009527253331645)
        ·
          refine ⟨2951009300253572719999367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7869358134009527253331645 2951009300253572719999367)
          ·
            refine ⟨4426513950380359079999051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2951009300253572719999367 4426513950380359079999051)
            ·
              refine ⟨6639770925570538619998577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4426513950380359079999051 6639770925570538619998577)
              ·
                refine ⟨4979828194177903964998933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6639770925570538619998577 4979828194177903964998933)
                ·
                  refine ⟨233429446602089248359325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4979828194177903964998933 233429446602089248359325)
                  ·
                    rfl

theorem cell21_1022855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 6].length) (baseStart_1022855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1022855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1022855 prefixEnd_1022855 := by exact prefixLift 1022855
  have htrace : WordTrace (prefixWord ++ tailWord_1022855) baseStart_1022855 baseEnd_1022855 := by
    simpa [prefixWord, tailWord_1022855, baseEnd_1022855] using wordTrace_append hprefix tailTrace_1022855
  have hstable : (prefixWord ++ tailWord_1022855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022855).length < 2 ^ (prefixWord ++ tailWord_1022855).sum := by decide
  have hdescent : baseEnd_1022855 < baseStart_1022855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022869 : List Nat := [1, 3, 2, 1, 1, 4, 9]
def baseStart_1022869 : Nat := 118140960795 + 1022869 * 2 ^ 59
def prefixEnd_1022869 : Nat := 4983230072969 + 3 ^ 40 * 1022869 * 2
def baseEnd_1022869 : Nat := 25936960176980926125107

theorem tailTrace_1022869 : CollatzResearch.WordTrace tailWord_1022869 prefixEnd_1022869 25936960176980926125107 := by
  unfold tailWord_1022869
  simp only [CollatzResearch.WordTrace]
  refine ⟨37307097331327779962359661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24871398220885186641573107 37307097331327779962359661)
  ·
    refine ⟨13990161499247917485884873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37307097331327779962359661 13990161499247917485884873)
    ·
      refine ⟨10492621124435938114413655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13990161499247917485884873 10492621124435938114413655)
      ·
        refine ⟨15738931686653907171620483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10492621124435938114413655 15738931686653907171620483)
        ·
          refine ⟨23608397529980860757430725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15738931686653907171620483 23608397529980860757430725)
          ·
            refine ⟨4426574536871411392018261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23608397529980860757430725 4426574536871411392018261)
            ·
              refine ⟨25936960176980926125107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4426574536871411392018261 25936960176980926125107)
              ·
                rfl

theorem cell21_1022869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 9].length) (baseStart_1022869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1022869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1022869 prefixEnd_1022869 := by exact prefixLift 1022869
  have htrace : WordTrace (prefixWord ++ tailWord_1022869) baseStart_1022869 baseEnd_1022869 := by
    simpa [prefixWord, tailWord_1022869, baseEnd_1022869] using wordTrace_append hprefix tailTrace_1022869
  have hstable : (prefixWord ++ tailWord_1022869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022869).length < 2 ^ (prefixWord ++ tailWord_1022869).sum := by decide
  have hdescent : baseEnd_1022869 < baseStart_1022869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023038 : List Nat := [4, 2, 1, 3, 1, 1, 9]
def baseStart_1023038 : Nat := 118140960795 + 1023038 * 2 ^ 59
def prefixEnd_1023038 : Nat := 4983230072969 + 3 ^ 40 * 1023038 * 2
def baseEnd_1023038 : Nat := 25941245521702399645439

theorem tailTrace_1023038 : CollatzResearch.WordTrace tailWord_1023038 prefixEnd_1023038 25941245521702399645439 := by
  unfold tailWord_1023038
  simp only [CollatzResearch.WordTrace]
  refine ⟨4664157658464440228157721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24875507511810347883507845 4664157658464440228157721)
  ·
    refine ⟨3498118243848330171118291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4664157658464440228157721 3498118243848330171118291)
    ·
      refine ⟨5247177365772495256677437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3498118243848330171118291 5247177365772495256677437)
      ·
        refine ⟨1967691512164685721254039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5247177365772495256677437 1967691512164685721254039)
        ·
          refine ⟨2951537268247028581881059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1967691512164685721254039 2951537268247028581881059)
          ·
            refine ⟨4427305902370542872821589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2951537268247028581881059 4427305902370542872821589)
            ·
              refine ⟨25941245521702399645439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4427305902370542872821589 25941245521702399645439)
              ·
                rfl

theorem cell21_1023038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 9].length) (baseStart_1023038 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1023038 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1023038 prefixEnd_1023038 := by exact prefixLift 1023038
  have htrace : WordTrace (prefixWord ++ tailWord_1023038) baseStart_1023038 baseEnd_1023038 := by
    simpa [prefixWord, tailWord_1023038, baseEnd_1023038] using wordTrace_append hprefix tailTrace_1023038
  have hstable : (prefixWord ++ tailWord_1023038).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023038).length < 2 ^ (prefixWord ++ tailWord_1023038).sum := by decide
  have hdescent : baseEnd_1023038 < baseStart_1023038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023066 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 8]
def baseStart_1023066 : Nat := 118140960795 + 1023066 * 2 ^ 59
def prefixEnd_1023066 : Nat := 4983230072969 + 3 ^ 40 * 1023066 * 2
def baseEnd_1023066 : Nat := 233477599676799770342227

theorem tailTrace_1023066 : CollatzResearch.WordTrace tailWord_1023066 prefixEnd_1023066 233477599676799770342227 := by
  unfold tailWord_1023066
  simp only [CollatzResearch.WordTrace]
  refine ⟨9328570627903520651820263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24876188341076055071520701 9328570627903520651820263)
  ·
    refine ⟨13992855941855280977730395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9328570627903520651820263 13992855941855280977730395)
    ·
      refine ⟨20989283912782921466595593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13992855941855280977730395 20989283912782921466595593)
      ·
        refine ⟨15741962934587191099946695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20989283912782921466595593 15741962934587191099946695)
        ·
          refine ⟨23612944401880786649920043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15741962934587191099946695 23612944401880786649920043)
          ·
            refine ⟨35419416602821179974880065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23612944401880786649920043 35419416602821179974880065)
            ·
              refine ⟨26564562452115884981160049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35419416602821179974880065 26564562452115884981160049)
              ·
                refine ⟨19923421839086913735870037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26564562452115884981160049 19923421839086913735870037)
                ·
                  refine ⟨233477599676799770342227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19923421839086913735870037 233477599676799770342227)
                  ·
                    rfl

theorem cell21_1023066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_1023066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1023066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1023066 prefixEnd_1023066 := by exact prefixLift 1023066
  have htrace : WordTrace (prefixWord ++ tailWord_1023066) baseStart_1023066 baseEnd_1023066 := by
    simpa [prefixWord, tailWord_1023066, baseEnd_1023066] using wordTrace_append hprefix tailTrace_1023066
  have hstable : (prefixWord ++ tailWord_1023066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023066).length < 2 ^ (prefixWord ++ tailWord_1023066).sum := by decide
  have hdescent : baseEnd_1023066 < baseStart_1023066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023097 : List Nat := [1, 2, 1, 3, 5, 9]
def baseStart_1023097 : Nat := 118140960795 + 1023097 * 2 ^ 59
def prefixEnd_1023097 : Nat := 4983230072969 + 3 ^ 40 * 1023097 * 2
def baseEnd_1023097 : Nat := 8647580529598170567611

theorem tailTrace_1023097 : CollatzResearch.WordTrace tailWord_1023097 prefixEnd_1023097 8647580529598170567611 := by
  unfold tailWord_1023097
  simp only [CollatzResearch.WordTrace]
  refine ⟨37315413174501774901659545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24876942116334516601106363 37315413174501774901659545)
  ·
    refine ⟨27986559880876331176244659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37315413174501774901659545 27986559880876331176244659)
    ·
      refine ⟨41979839821314496764366989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27986559880876331176244659 41979839821314496764366989)
      ·
        refine ⟨15742439932992936286637621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41979839821314496764366989 15742439932992936286637621)
        ·
          refine ⟨1475853743718087776872277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15742439932992936286637621 1475853743718087776872277)
          ·
            refine ⟨8647580529598170567611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1475853743718087776872277 8647580529598170567611)
            ·
              rfl

theorem cell21_1023097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 9].length) (baseStart_1023097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1023097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1023097 prefixEnd_1023097 := by exact prefixLift 1023097
  have htrace : WordTrace (prefixWord ++ tailWord_1023097) baseStart_1023097 baseEnd_1023097 := by
    simpa [prefixWord, tailWord_1023097, baseEnd_1023097] using wordTrace_append hprefix tailTrace_1023097
  have hstable : (prefixWord ++ tailWord_1023097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023097).length < 2 ^ (prefixWord ++ tailWord_1023097).sum := by decide
  have hdescent : baseEnd_1023097 < baseStart_1023097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023128 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 7]
def baseStart_1023128 : Nat := 118140960795 + 1023128 * 2 ^ 59
def prefixEnd_1023128 : Nat := 4983230072969 + 3 ^ 40 * 1023128 * 2
def baseEnd_1023128 : Nat := 233491748921501440308767

theorem tailTrace_1023128 : CollatzResearch.WordTrace tailWord_1023128 prefixEnd_1023128 233491748921501440308767 := by
  unfold tailWord_1023128
  simp only [CollatzResearch.WordTrace]
  refine ⟨18658271918694733598019019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24877695891592978130692025 18658271918694733598019019)
  ·
    refine ⟨27987407878042100397028529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18658271918694733598019019 27987407878042100397028529)
    ·
      refine ⟨20990555908531575297771397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27987407878042100397028529 20990555908531575297771397)
      ·
        refine ⟨3935729232849670368332137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20990555908531575297771397 3935729232849670368332137)
        ·
          refine ⟨2951796924637252776249103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3935729232849670368332137 2951796924637252776249103)
          ·
            refine ⟨4427695386955879164373655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2951796924637252776249103 4427695386955879164373655)
            ·
              refine ⟨6641543080433818746560483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4427695386955879164373655 6641543080433818746560483)
              ·
                refine ⟨9962314620650728119840725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6641543080433818746560483 9962314620650728119840725)
                ·
                  refine ⟨233491748921501440308767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9962314620650728119840725 233491748921501440308767)
                  ·
                    rfl

theorem cell21_1023128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 7].length) (baseStart_1023128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1023128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1023128 prefixEnd_1023128 := by exact prefixLift 1023128
  have htrace : WordTrace (prefixWord ++ tailWord_1023128) baseStart_1023128 baseEnd_1023128 := by
    simpa [prefixWord, tailWord_1023128, baseEnd_1023128] using wordTrace_append hprefix tailTrace_1023128
  have hstable : (prefixWord ++ tailWord_1023128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023128).length < 2 ^ (prefixWord ++ tailWord_1023128).sum := by decide
  have hdescent : baseEnd_1023128 < baseStart_1023128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023207 : List Nat := [1, 1, 5, 3, 3, 1, 7]
def baseStart_1023207 : Nat := 118140960795 + 1023207 * 2 ^ 59
def prefixEnd_1023207 : Nat := 4983230072969 + 3 ^ 40 * 1023207 * 2
def baseEnd_1023207 : Nat := 25945530866423873165771

theorem tailTrace_1023207 : CollatzResearch.WordTrace tailWord_1023207 prefixEnd_1023207 25945530866423873165771 := by
  unfold tailWord_1023207
  simp only [CollatzResearch.WordTrace]
  refine ⟨37319425204103263688163875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24879616802735509125442583 37319425204103263688163875)
  ·
    refine ⟨55979137806154895532245813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37319425204103263688163875 55979137806154895532245813)
    ·
      refine ⟨5248044169327021456148045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55979137806154895532245813 5248044169327021456148045)
      ·
        refine ⟨1968016563497633046055517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5248044169327021456148045 1968016563497633046055517)
        ·
          refine ⟨738006211311612392270819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1968016563497633046055517 738006211311612392270819)
          ·
            refine ⟨1107009316967418588406229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738006211311612392270819 1107009316967418588406229)
            ·
              refine ⟨25945530866423873165771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1107009316967418588406229 25945530866423873165771)
              ·
                rfl

theorem cell21_1023207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 7].length) (baseStart_1023207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1023207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1023207 prefixEnd_1023207 := by exact prefixLift 1023207
  have htrace : WordTrace (prefixWord ++ tailWord_1023207) baseStart_1023207 baseEnd_1023207 := by
    simpa [prefixWord, tailWord_1023207, baseEnd_1023207] using wordTrace_append hprefix tailTrace_1023207
  have hstable : (prefixWord ++ tailWord_1023207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023207).length < 2 ^ (prefixWord ++ tailWord_1023207).sum := by decide
  have hdescent : baseEnd_1023207 < baseStart_1023207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023235 : List Nat := [1, 1, 1, 3, 2, 5, 1, 3, 4]
def baseStart_1023235 : Nat := 118140960795 + 1023235 * 2 ^ 59
def prefixEnd_1023235 : Nat := 4983230072969 + 3 ^ 40 * 1023235 * 2
def baseEnd_1023235 : Nat := 233516167779293032025215

theorem tailTrace_1023235 : CollatzResearch.WordTrace tailWord_1023235 prefixEnd_1023235 233516167779293032025215 := by
  unfold tailWord_1023235
  simp only [CollatzResearch.WordTrace]
  refine ⟨37320446448001824470183159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24880297632001216313455439 37320446448001824470183159)
  ·
    refine ⟨55980669672002736705274739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37320446448001824470183159 55980669672002736705274739)
    ·
      refine ⟨83971004508004105057912109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55980669672002736705274739 83971004508004105057912109)
      ·
        refine ⟨31489126690501539396717041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83971004508004105057912109 31489126690501539396717041)
        ·
          refine ⟨23616845017876154547537781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31489126690501539396717041 23616845017876154547537781)
          ·
            refine ⟨2214079220425889488831667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23616845017876154547537781 2214079220425889488831667)
            ·
              refine ⟨3321118830638834233247501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2214079220425889488831667 3321118830638834233247501)
              ·
                refine ⟨1245419561489562837467813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3321118830638834233247501 1245419561489562837467813)
                ·
                  refine ⟨233516167779293032025215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1245419561489562837467813 233516167779293032025215)
                  ·
                    rfl

theorem cell21_1023235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 4].length) (baseStart_1023235 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1023235 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1023235 prefixEnd_1023235 := by exact prefixLift 1023235
  have htrace : WordTrace (prefixWord ++ tailWord_1023235) baseStart_1023235 baseEnd_1023235 := by
    simpa [prefixWord, tailWord_1023235, baseEnd_1023235] using wordTrace_append hprefix tailTrace_1023235
  have hstable : (prefixWord ++ tailWord_1023235).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023235).length < 2 ^ (prefixWord ++ tailWord_1023235).sum := by decide
  have hdescent : baseEnd_1023235 < baseStart_1023235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023266 : List Nat := [3, 3, 1, 1, 5, 8]
def baseStart_1023266 : Nat := 118140960795 + 1023266 * 2 ^ 59
def prefixEnd_1023266 : Nat := 4983230072969 + 3 ^ 40 * 1023266 * 2
def baseEnd_1023266 : Nat := 8649008977838661741055

theorem tailTrace_1023266 : CollatzResearch.WordTrace tailWord_1023266 prefixEnd_1023266 8649008977838661741055 := by
  unfold tailWord_1023266
  simp only [CollatzResearch.WordTrace]
  refine ⟨9330394277722379191140413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24881051407259677843041101 9330394277722379191140413)
  ·
    refine ⟨3498897854145892196677655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9330394277722379191140413 3498897854145892196677655)
    ·
      refine ⟨5248346781218838295016483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3498897854145892196677655 5248346781218838295016483)
      ·
        refine ⟨7872520171828257442524725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5248346781218838295016483 7872520171828257442524725)
        ·
          refine ⟨738048766108899135236693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7872520171828257442524725 738048766108899135236693)
          ·
            refine ⟨8649008977838661741055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 738048766108899135236693 8649008977838661741055)
            ·
              rfl

theorem cell21_1023266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 8].length) (baseStart_1023266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1023266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1023266 prefixEnd_1023266 := by exact prefixLift 1023266
  have htrace : WordTrace (prefixWord ++ tailWord_1023266) baseStart_1023266 baseEnd_1023266 := by
    simpa [prefixWord, tailWord_1023266, baseEnd_1023266] using wordTrace_append hprefix tailTrace_1023266
  have hstable : (prefixWord ++ tailWord_1023266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023266).length < 2 ^ (prefixWord ++ tailWord_1023266).sum := by decide
  have hdescent : baseEnd_1023266 < baseStart_1023266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023297 : List Nat := [1, 2, 5, 2, 1, 2, 1, 2, 5]
def baseStart_1023297 : Nat := 118140960795 + 1023297 * 2 ^ 59
def prefixEnd_1023297 : Nat := 4983230072969 + 3 ^ 40 * 1023297 * 2
def baseEnd_1023297 : Nat := 233530317023994701991755

theorem tailTrace_1023297 : CollatzResearch.WordTrace tailWord_1023297 prefixEnd_1023297 233530317023994701991755 := by
  unfold tailWord_1023297
  simp only [CollatzResearch.WordTrace]
  refine ⟨37322707773777209058940145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24881805182518139372626763 37322707773777209058940145)
  ·
    refine ⟨27992030830332906794205109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37322707773777209058940145 27992030830332906794205109)
    ·
      refine ⟨2624252890343710011956729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27992030830332906794205109 2624252890343710011956729)
      ·
        refine ⟨1968189667757782508967547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2624252890343710011956729 1968189667757782508967547)
        ·
          refine ⟨2952284501636673763451321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1968189667757782508967547 2952284501636673763451321)
          ·
            refine ⟨2214213376227505322588491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2952284501636673763451321 2214213376227505322588491)
            ·
              refine ⟨3321320064341257983882737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2214213376227505322588491 3321320064341257983882737)
              ·
                refine ⟨2490990048255943487912053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3321320064341257983882737 2490990048255943487912053)
                ·
                  refine ⟨233530317023994701991755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2490990048255943487912053 233530317023994701991755)
                  ·
                    rfl

theorem cell21_1023297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 5].length) (baseStart_1023297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1023297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1023297 prefixEnd_1023297 := by exact prefixLift 1023297
  have htrace : WordTrace (prefixWord ++ tailWord_1023297) baseStart_1023297 baseEnd_1023297 := by
    simpa [prefixWord, tailWord_1023297, baseEnd_1023297] using wordTrace_append hprefix tailTrace_1023297
  have hstable : (prefixWord ++ tailWord_1023297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023297).length < 2 ^ (prefixWord ++ tailWord_1023297).sum := by decide
  have hdescent : baseEnd_1023297 < baseStart_1023297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023328 : List Nat := [2, 1, 1, 3, 4, 3, 1, 2, 4]
def baseStart_1023328 : Nat := 118140960795 + 1023328 * 2 ^ 59
def prefixEnd_1023328 : Nat := 4983230072969 + 3 ^ 40 * 1023328 * 2
def baseEnd_1023328 : Nat := 233537391646345536975025

theorem tailTrace_1023328 : CollatzResearch.WordTrace tailWord_1023328 prefixEnd_1023328 233537391646345536975025 := by
  unfold tailWord_1023328
  simp only [CollatzResearch.WordTrace]
  refine ⟨18661919218332450676659319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24882558957776600902212425 18661919218332450676659319)
  ·
    refine ⟨27992878827498676014988979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18661919218332450676659319 27992878827498676014988979)
    ·
      refine ⟨41989318241248014022483469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27992878827498676014988979 41989318241248014022483469)
      ·
        refine ⟨15745994340468005258431301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41989318241248014022483469 15745994340468005258431301)
        ·
          refine ⟨2952373938837750985955869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15745994340468005258431301 2952373938837750985955869)
          ·
            refine ⟨1107140227064156619733451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2952373938837750985955869 1107140227064156619733451)
            ·
              refine ⟨1660710340596234929600177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107140227064156619733451 1660710340596234929600177)
              ·
                refine ⟨1245532755447176197200133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1660710340596234929600177 1245532755447176197200133)
                ·
                  refine ⟨233537391646345536975025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1245532755447176197200133 233537391646345536975025)
                  ·
                    rfl

theorem cell21_1023328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 4].length) (baseStart_1023328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1023328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1023328 prefixEnd_1023328 := by exact prefixLift 1023328
  have htrace : WordTrace (prefixWord ++ tailWord_1023328) baseStart_1023328 baseEnd_1023328 := by
    simpa [prefixWord, tailWord_1023328, baseEnd_1023328] using wordTrace_append hprefix tailTrace_1023328
  have hstable : (prefixWord ++ tailWord_1023328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023328).length < 2 ^ (prefixWord ++ tailWord_1023328).sum := by decide
  have hdescent : baseEnd_1023328 < baseStart_1023328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023415 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 7]
def baseStart_1023415 : Nat := 118140960795 + 1023415 * 2 ^ 59
def prefixEnd_1023415 : Nat := 4983230072969 + 3 ^ 40 * 1023415 * 2
def baseEnd_1023415 : Nat := 233557246231652719024847

theorem tailTrace_1023415 : CollatzResearch.WordTrace tailWord_1023415 prefixEnd_1023415 233557246231652719024847 := by
  unfold tailWord_1023415
  simp only [CollatzResearch.WordTrace]
  refine ⟨37327011587349715211735699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24884674391566476807823799 37327011587349715211735699)
  ·
    refine ⟨55990517381024572817603549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37327011587349715211735699 55990517381024572817603549)
    ·
      refine ⟨20996444017884214806601331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55990517381024572817603549 20996444017884214806601331)
      ·
        refine ⟨31494666026826322209901997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20996444017884214806601331 31494666026826322209901997)
        ·
          refine ⟨11810499760059870828713249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31494666026826322209901997 11810499760059870828713249)
          ·
            refine ⟨8857874820044903121534937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11810499760059870828713249 8857874820044903121534937)
            ·
              refine ⟨6643406115033677341151203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8857874820044903121534937 6643406115033677341151203)
              ·
                refine ⟨9965109172550516011726805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6643406115033677341151203 9965109172550516011726805)
                ·
                  refine ⟨233557246231652719024847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9965109172550516011726805 233557246231652719024847)
                  ·
                    rfl

theorem cell21_1023415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 7].length) (baseStart_1023415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1023415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1023415 prefixEnd_1023415 := by exact prefixLift 1023415
  have htrace : WordTrace (prefixWord ++ tailWord_1023415) baseStart_1023415 baseEnd_1023415 := by
    simpa [prefixWord, tailWord_1023415, baseEnd_1023415] using wordTrace_append hprefix tailTrace_1023415
  have hstable : (prefixWord ++ tailWord_1023415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023415).length < 2 ^ (prefixWord ++ tailWord_1023415).sum := by decide
  have hdescent : baseEnd_1023415 < baseStart_1023415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023449 : List Nat := [1, 2, 1, 2, 4, 3, 1, 4, 3]
def baseStart_1023449 : Nat := 118140960795 + 1023449 * 2 ^ 59
def prefixEnd_1023449 : Nat := 4983230072969 + 3 ^ 40 * 1023449 * 2
def baseEnd_1023449 : Nat := 233565005494876215458111

theorem tailTrace_1023449 : CollatzResearch.WordTrace tailWord_1023449 prefixEnd_1023449 233565005494876215458111 := by
  unfold tailWord_1023449
  simp only [CollatzResearch.WordTrace]
  refine ⟨37328251669226539018473401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24885501112817692678982267 37328251669226539018473401)
  ·
    refine ⟨27996188751919904263855051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37328251669226539018473401 27996188751919904263855051)
    ·
      refine ⟨41994283127879856395782577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27996188751919904263855051 41994283127879856395782577)
      ·
        refine ⟨31495712345909892296836933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41994283127879856395782577 31495712345909892296836933)
        ·
          refine ⟨5905446064858104805656925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31495712345909892296836933 5905446064858104805656925)
          ·
            refine ⟨2214542274321789302121347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5905446064858104805656925 2214542274321789302121347)
            ·
              refine ⟨3321813411482683953182021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2214542274321789302121347 3321813411482683953182021)
              ·
                refine ⟨622840014653003241221629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3321813411482683953182021 622840014653003241221629)
                ·
                  refine ⟨233565005494876215458111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 622840014653003241221629 233565005494876215458111)
                  ·
                    rfl

theorem cell21_1023449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 4, 3].length) (baseStart_1023449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1023449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1023449 prefixEnd_1023449 := by exact prefixLift 1023449
  have htrace : WordTrace (prefixWord ++ tailWord_1023449) baseStart_1023449 baseEnd_1023449 := by
    simpa [prefixWord, tailWord_1023449, baseEnd_1023449] using wordTrace_append hprefix tailTrace_1023449
  have hstable : (prefixWord ++ tailWord_1023449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023449).length < 2 ^ (prefixWord ++ tailWord_1023449).sum := by decide
  have hdescent : baseEnd_1023449 < baseStart_1023449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023463 : List Nat := [1, 1, 5, 2, 1, 2, 2, 3, 4]
def baseStart_1023463 : Nat := 118140960795 + 1023463 * 2 ^ 59
def prefixEnd_1023463 : Nat := 4983230072969 + 3 ^ 40 * 1023463 * 2
def baseEnd_1023463 : Nat := 233568200485615302224749

theorem tailTrace_1023463 : CollatzResearch.WordTrace tailWord_1023463 prefixEnd_1023463 233568200485615302224749 := by
  unfold tailWord_1023463
  simp only [CollatzResearch.WordTrace]
  refine ⟨37328762291175819409483043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24885841527450546272988695 37328762291175819409483043)
  ·
    refine ⟨55993143436763729114224565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37328762291175819409483043 55993143436763729114224565)
    ·
      refine ⟨5249357197196599604458553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55993143436763729114224565 5249357197196599604458553)
      ·
        refine ⟨3937017897897449703343915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5249357197196599604458553 3937017897897449703343915)
        ·
          refine ⟨5905526846846174555015873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3937017897897449703343915 5905526846846174555015873)
          ·
            refine ⟨4429145135134630916261905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5905526846846174555015873 4429145135134630916261905)
            ·
              refine ⟨3321858851350973187196429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4429145135134630916261905 3321858851350973187196429)
              ·
                refine ⟨1245697069256614945198661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3321858851350973187196429 1245697069256614945198661)
                ·
                  refine ⟨233568200485615302224749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1245697069256614945198661 233568200485615302224749)
                  ·
                    rfl

theorem cell21_1023463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 4].length) (baseStart_1023463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1023463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1023463 prefixEnd_1023463 := by exact prefixLift 1023463
  have htrace : WordTrace (prefixWord ++ tailWord_1023463) baseStart_1023463 baseEnd_1023463 := by
    simpa [prefixWord, tailWord_1023463, baseEnd_1023463] using wordTrace_append hprefix tailTrace_1023463
  have hstable : (prefixWord ++ tailWord_1023463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023463).length < 2 ^ (prefixWord ++ tailWord_1023463).sum := by decide
  have hdescent : baseEnd_1023463 < baseStart_1023463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023528 : List Nat := [2, 1, 5, 2, 3, 1, 2, 5]
def baseStart_1023528 : Nat := 118140960795 + 1023528 * 2 ^ 59
def prefixEnd_1023528 : Nat := 4983230072969 + 3 ^ 40 * 1023528 * 2
def baseEnd_1023528 : Nat := 77861011457063211213761

theorem tailTrace_1023528 : CollatzResearch.WordTrace tailWord_1023528 prefixEnd_1023528 77861011457063211213761 := by
  unfold tailWord_1023528
  simp only [CollatzResearch.WordTrace]
  refine ⟨18665566517970167755299619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24887422023960223673732825 18665566517970167755299619)
  ·
    refine ⟨27998349776955251632949429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18665566517970167755299619 27998349776955251632949429)
    ·
      refine ⟨2624845291589554840589009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27998349776955251632949429 2624845291589554840589009)
      ·
        refine ⟨1968633968692166130441757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2624845291589554840589009 1968633968692166130441757)
        ·
          refine ⟨738237738259562298915659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1968633968692166130441757 738237738259562298915659)
          ·
            refine ⟨1107356607389343448373489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738237738259562298915659 1107356607389343448373489)
            ·
              refine ⟨830517455542007586280117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1107356607389343448373489 830517455542007586280117)
              ·
                refine ⟨77861011457063211213761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 830517455542007586280117 77861011457063211213761)
                ·
                  rfl

theorem cell21_1023528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 5].length) (baseStart_1023528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1023528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1023528 prefixEnd_1023528 := by exact prefixLift 1023528
  have htrace : WordTrace (prefixWord ++ tailWord_1023528) baseStart_1023528 baseEnd_1023528 := by
    simpa [prefixWord, tailWord_1023528, baseEnd_1023528] using wordTrace_append hprefix tailTrace_1023528
  have hstable : (prefixWord ++ tailWord_1023528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023528).length < 2 ^ (prefixWord ++ tailWord_1023528).sum := by decide
  have hdescent : baseEnd_1023528 < baseStart_1023528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023674 : List Nat := [3, 1, 1, 1, 2, 5, 1, 1, 6]
def baseStart_1023674 : Nat := 118140960795 + 1023674 * 2 ^ 59
def prefixEnd_1023674 : Nat := 4983230072969 + 3 ^ 40 * 1023674 * 2
def baseEnd_1023674 : Nat := 233616353560325824207651

theorem tailTrace_1023674 : CollatzResearch.WordTrace tailWord_1023674 prefixEnd_1023674 233616353560325824207651 := by
  unfold tailWord_1023674
  simp only [CollatzResearch.WordTrace]
  refine ⟨9334114523352850611353519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24890972062274268296942717 9334114523352850611353519)
  ·
    refine ⟨14001171785029275917030279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9334114523352850611353519 14001171785029275917030279)
    ·
      refine ⟨21001757677543913875545419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14001171785029275917030279 21001757677543913875545419)
      ·
        refine ⟨31502636516315870813318129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21001757677543913875545419 31502636516315870813318129)
        ·
          refine ⟨23626977387236903109988597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31502636516315870813318129 23626977387236903109988597)
          ·
            refine ⟨2215029130053459666561431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23626977387236903109988597 2215029130053459666561431)
            ·
              refine ⟨3322543695080189499842147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2215029130053459666561431 3322543695080189499842147)
              ·
                refine ⟨4983815542620284249763221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3322543695080189499842147 4983815542620284249763221)
                ·
                  refine ⟨233616353560325824207651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4983815542620284249763221 233616353560325824207651)
                  ·
                    rfl

theorem cell21_1023674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_1023674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1023674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1023674 prefixEnd_1023674 := by exact prefixLift 1023674
  have htrace : WordTrace (prefixWord ++ tailWord_1023674) baseStart_1023674 baseEnd_1023674 := by
    simpa [prefixWord, tailWord_1023674, baseEnd_1023674] using wordTrace_append hprefix tailTrace_1023674
  have hstable : (prefixWord ++ tailWord_1023674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023674).length < 2 ^ (prefixWord ++ tailWord_1023674).sum := by decide
  have hdescent : baseEnd_1023674 < baseStart_1023674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023688 : List Nat := [2, 1, 3, 1, 2, 2, 2, 8]
def baseStart_1023688 : Nat := 118140960795 + 1023688 * 2 ^ 59
def prefixEnd_1023688 : Nat := 4983230072969 + 3 ^ 40 * 1023688 * 2
def baseEnd_1023688 : Nat := 77873182850354970324763

theorem tailTrace_1023688 : CollatzResearch.WordTrace tailWord_1023688 prefixEnd_1023688 77873182850354970324763 := by
  unfold tailWord_1023688
  simp only [CollatzResearch.WordTrace]
  refine ⟨18668484357680341418211859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24891312476907121890949145 18668484357680341418211859)
  ·
    refine ⟨28002726536520512127317789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18668484357680341418211859 28002726536520512127317789)
    ·
      refine ⟨10501022451195192047744171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28002726536520512127317789 10501022451195192047744171)
      ·
        refine ⟨15751533676792788071616257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10501022451195192047744171 15751533676792788071616257)
        ·
          refine ⟨11813650257594591053712193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15751533676792788071616257 11813650257594591053712193)
          ·
            refine ⟨8860237693195943290284145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11813650257594591053712193 8860237693195943290284145)
            ·
              refine ⟨6645178269896957467713109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8860237693195943290284145 6645178269896957467713109)
              ·
                refine ⟨77873182850354970324763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6645178269896957467713109 77873182850354970324763)
                ·
                  rfl

theorem cell21_1023688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 8].length) (baseStart_1023688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1023688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1023688 prefixEnd_1023688 := by exact prefixLift 1023688
  have htrace : WordTrace (prefixWord ++ tailWord_1023688) baseStart_1023688 baseEnd_1023688 := by
    simpa [prefixWord, tailWord_1023688, baseEnd_1023688] using wordTrace_append hprefix tailTrace_1023688
  have hstable : (prefixWord ++ tailWord_1023688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023688).length < 2 ^ (prefixWord ++ tailWord_1023688).sum := by decide
  have hdescent : baseEnd_1023688 < baseStart_1023688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023705 : List Nat := [1, 2, 1, 2, 3, 3, 4, 5]
def baseStart_1023705 : Nat := 118140960795 + 1023705 * 2 ^ 59
def prefixEnd_1023705 : Nat := 4983230072969 + 3 ^ 40 * 1023705 * 2
def baseEnd_1023705 : Nat := 77874476060892219730307

theorem tailTrace_1023705 : CollatzResearch.WordTrace tailWord_1023705 prefixEnd_1023705 77874476060892219730307 := by
  unfold tailWord_1023705
  simp only [CollatzResearch.WordTrace]
  refine ⟨37337588756299094739792569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24891725837532729826528379 37337588756299094739792569)
  ·
    refine ⟨28003191567224321054844427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37337588756299094739792569 28003191567224321054844427)
    ·
      refine ⟨42004787350836481582266641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28003191567224321054844427 42004787350836481582266641)
      ·
        refine ⟨31503590513127361186699981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42004787350836481582266641 31503590513127361186699981)
        ·
          refine ⟨11813846442422760445012493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31503590513127361186699981 11813846442422760445012493)
          ·
            refine ⟨4430192415908535166879685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11813846442422760445012493 4430192415908535166879685)
            ·
              refine ⟨830661077982850343789941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4430192415908535166879685 830661077982850343789941)
              ·
                refine ⟨77874476060892219730307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 830661077982850343789941 77874476060892219730307)
                ·
                  rfl

theorem cell21_1023705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 5].length) (baseStart_1023705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1023705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1023705 prefixEnd_1023705 := by exact prefixLift 1023705
  have htrace : WordTrace (prefixWord ++ tailWord_1023705) baseStart_1023705 baseEnd_1023705 := by
    simpa [prefixWord, tailWord_1023705, baseEnd_1023705] using wordTrace_append hprefix tailTrace_1023705
  have hstable : (prefixWord ++ tailWord_1023705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023705).length < 2 ^ (prefixWord ++ tailWord_1023705).sum := by decide
  have hdescent : baseEnd_1023705 < baseStart_1023705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023742 : List Nat := [4, 2, 2, 1, 4, 1, 2, 1, 4]
def baseStart_1023742 : Nat := 118140960795 + 1023742 * 2 ^ 59
def prefixEnd_1023742 : Nat := 4983230072969 + 3 ^ 40 * 1023742 * 2
def baseEnd_1023742 : Nat := 233631872086772817074179

theorem tailTrace_1023742 : CollatzResearch.WordTrace tailWord_1023742 prefixEnd_1023742 233631872086772817074179 := by
  unfold tailWord_1023742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4667367282145631257361185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24892625504776700039259653 4667367282145631257361185)
  ·
    refine ⟨3500525461609223443020889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4667367282145631257361185 3500525461609223443020889)
    ·
      refine ⟨2625394096206917582265667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3500525461609223443020889 2625394096206917582265667)
      ·
        refine ⟨3938091144310376373398501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2625394096206917582265667 3938091144310376373398501)
        ·
          refine ⟨738392089558195570012219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3938091144310376373398501 738392089558195570012219)
          ·
            refine ⟨1107588134337293355018329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738392089558195570012219 1107588134337293355018329)
            ·
              refine ⟨830691100752970016263747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1107588134337293355018329 830691100752970016263747)
              ·
                refine ⟨1246036651129455024395621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 830691100752970016263747 1246036651129455024395621)
                ·
                  refine ⟨233631872086772817074179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1246036651129455024395621 233631872086772817074179)
                  ·
                    rfl

theorem cell21_1023742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_1023742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1023742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1023742 prefixEnd_1023742 := by exact prefixLift 1023742
  have htrace : WordTrace (prefixWord ++ tailWord_1023742) baseStart_1023742 baseEnd_1023742 := by
    simpa [prefixWord, tailWord_1023742, baseEnd_1023742] using wordTrace_append hprefix tailTrace_1023742
  have hstable : (prefixWord ++ tailWord_1023742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023742).length < 2 ^ (prefixWord ++ tailWord_1023742).sum := by decide
  have hdescent : baseEnd_1023742 < baseStart_1023742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023798 : List Nat := [5, 1, 2, 2, 1, 1, 3, 6]
def baseStart_1023798 : Nat := 118140960795 + 1023798 * 2 ^ 59
def prefixEnd_1023798 : Nat := 4983230072969 + 3 ^ 40 * 1023798 * 2
def baseEnd_1023798 : Nat := 77881550683243054713577

theorem tailTrace_1023798 : CollatzResearch.WordTrace tailWord_1023798 prefixEnd_1023798 77881550683243054713577 := by
  unfold tailWord_1023798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2333811296560135726433003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24893987163308114415285365 2333811296560135726433003)
  ·
    refine ⟨3500716944840203589649505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2333811296560135726433003 3500716944840203589649505)
    ·
      refine ⟨2625537708630152692237129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3500716944840203589649505 2625537708630152692237129)
      ·
        refine ⟨1969153281472614519177847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2625537708630152692237129 1969153281472614519177847)
        ·
          refine ⟨2953729922208921778766771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1969153281472614519177847 2953729922208921778766771)
          ·
            refine ⟨4430594883313382668150157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2953729922208921778766771 4430594883313382668150157)
            ·
              refine ⟨1661473081242518500556309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4430594883313382668150157 1661473081242518500556309)
              ·
                refine ⟨77881550683243054713577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1661473081242518500556309 77881550683243054713577)
                ·
                  rfl

theorem cell21_1023798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_1023798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1023798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1023798 prefixEnd_1023798 := by exact prefixLift 1023798
  have htrace : WordTrace (prefixWord ++ tailWord_1023798) baseStart_1023798 baseEnd_1023798 := by
    simpa [prefixWord, tailWord_1023798, baseEnd_1023798] using wordTrace_append hprefix tailTrace_1023798
  have hstable : (prefixWord ++ tailWord_1023798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023798).length < 2 ^ (prefixWord ++ tailWord_1023798).sum := by decide
  have hdescent : baseEnd_1023798 < baseStart_1023798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023829 : List Nat := [1, 3, 2, 2, 2, 3, 2, 3, 3]
def baseStart_1023829 : Nat := 118140960795 + 1023829 * 2 ^ 59
def prefixEnd_1023829 : Nat := 4983230072969 + 3 ^ 40 * 1023829 * 2
def baseEnd_1023829 : Nat := 233651726672079999124001

theorem tailTrace_1023829 : CollatzResearch.WordTrace tailWord_1023829 prefixEnd_1023829 233651726672079999124001 := by
  unfold tailWord_1023829
  simp only [CollatzResearch.WordTrace]
  refine ⟨37342111407849863917306541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24894740938566575944871027 37342111407849863917306541)
  ·
    refine ⟨14003291777943698968989953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37342111407849863917306541 14003291777943698968989953)
    ·
      refine ⟨10502468833457774226742465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14003291777943698968989953 10502468833457774226742465)
      ·
        refine ⟨7876851625093330670056849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10502468833457774226742465 7876851625093330670056849)
        ·
          refine ⟨5907638718819998002542637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7876851625093330670056849 5907638718819998002542637)
          ·
            refine ⟨2215364519557499250953489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5907638718819998002542637 2215364519557499250953489)
            ·
              refine ⟨1661523389668124438215117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2215364519557499250953489 1661523389668124438215117)
              ·
                refine ⟨623071271125546664330669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1661523389668124438215117 623071271125546664330669)
                ·
                  refine ⟨233651726672079999124001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 623071271125546664330669 233651726672079999124001)
                  ·
                    rfl

theorem cell21_1023829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 3, 3].length) (baseStart_1023829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1023829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1023829 prefixEnd_1023829 := by exact prefixLift 1023829
  have htrace : WordTrace (prefixWord ++ tailWord_1023829) baseStart_1023829 baseEnd_1023829 := by
    simpa [prefixWord, tailWord_1023829, baseEnd_1023829] using wordTrace_append hprefix tailTrace_1023829
  have hstable : (prefixWord ++ tailWord_1023829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023829).length < 2 ^ (prefixWord ++ tailWord_1023829).sum := by decide
  have hdescent : baseEnd_1023829 < baseStart_1023829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023840 : List Nat := [2, 1, 1, 3, 3, 3, 8]
def baseStart_1023840 : Nat := 118140960795 + 1023840 * 2 ^ 59
def prefixEnd_1023840 : Nat := 4983230072969 + 3 ^ 40 * 1023840 * 2
def baseEnd_1023840 : Nat := 25961581891327380493405

theorem tailTrace_1023840 : CollatzResearch.WordTrace tailWord_1023840 prefixEnd_1023840 25961581891327380493405 := by
  unfold tailWord_1023840
  simp only [CollatzResearch.WordTrace]
  refine ⟨18671256305405006397978487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24895008407206675197304649 18671256305405006397978487)
  ·
    refine ⟨28006884458107509596967731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18671256305405006397978487 28006884458107509596967731)
    ·
      refine ⟨42010326687161264395451597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28006884458107509596967731 42010326687161264395451597)
      ·
        refine ⟨15753872507685474148294349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42010326687161264395451597 15753872507685474148294349)
        ·
          refine ⟨5907702190382052805610381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15753872507685474148294349 5907702190382052805610381)
          ·
            refine ⟨2215388321393269802103893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5907702190382052805610381 2215388321393269802103893)
            ·
              refine ⟨25961581891327380493405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2215388321393269802103893 25961581891327380493405)
              ·
                rfl

theorem cell21_1023840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 8].length) (baseStart_1023840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1023840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1023840 prefixEnd_1023840 := by exact prefixLift 1023840
  have htrace : WordTrace (prefixWord ++ tailWord_1023840) baseStart_1023840 baseEnd_1023840 := by
    simpa [prefixWord, tailWord_1023840, baseEnd_1023840] using wordTrace_append hprefix tailTrace_1023840
  have hstable : (prefixWord ++ tailWord_1023840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023840).length < 2 ^ (prefixWord ++ tailWord_1023840).sum := by decide
  have hdescent : baseEnd_1023840 < baseStart_1023840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023905 : List Nat := [1, 2, 3, 4, 2, 2, 1, 1, 5]
def baseStart_1023905 : Nat := 118140960795 + 1023905 * 2 ^ 59
def prefixEnd_1023905 : Nat := 4983230072969 + 3 ^ 40 * 1023905 * 2
def baseEnd_1023905 : Nat := 233669070907520755857179

theorem tailTrace_1023905 : CollatzResearch.WordTrace tailWord_1023905 prefixEnd_1023905 233669070907520755857179 := by
  unfold tailWord_1023905
  simp only [CollatzResearch.WordTrace]
  refine ⟨37344883355574528897073169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24896588903716352598048779 37344883355574528897073169)
  ·
    refine ⟨28008662516680896672804877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37344883355574528897073169 28008662516680896672804877)
    ·
      refine ⟨10503248443755336252301829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28008662516680896672804877 10503248443755336252301829)
      ·
        refine ⟨1969359083204125547306593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10503248443755336252301829 1969359083204125547306593)
        ·
          refine ⟨1477019312403094160479945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1969359083204125547306593 1477019312403094160479945)
          ·
            refine ⟨1107764484302320620359959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1477019312403094160479945 1107764484302320620359959)
            ·
              refine ⟨1661646726453480930539939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107764484302320620359959 1661646726453480930539939)
              ·
                refine ⟨2492470089680221395809909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1661646726453480930539939 2492470089680221395809909)
                ·
                  refine ⟨233669070907520755857179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2492470089680221395809909 233669070907520755857179)
                  ·
                    rfl

theorem cell21_1023905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 5].length) (baseStart_1023905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1023905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1023905 prefixEnd_1023905 := by exact prefixLift 1023905
  have htrace : WordTrace (prefixWord ++ tailWord_1023905) baseStart_1023905 baseEnd_1023905 := by
    simpa [prefixWord, tailWord_1023905, baseEnd_1023905] using wordTrace_append hprefix tailTrace_1023905
  have hstable : (prefixWord ++ tailWord_1023905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023905).length < 2 ^ (prefixWord ++ tailWord_1023905).sum := by decide
  have hdescent : baseEnd_1023905 < baseStart_1023905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023978 : List Nat := [3, 1, 3, 1, 2, 1, 1, 5, 4]
def baseStart_1023978 : Nat := 118140960795 + 1023978 * 2 ^ 59
def prefixEnd_1023978 : Nat := 4983230072969 + 3 ^ 40 * 1023978 * 2
def baseEnd_1023978 : Nat := 233685730502088851140363

theorem tailTrace_1023978 : CollatzResearch.WordTrace tailWord_1023978 prefixEnd_1023978 233685730502088851140363 := by
  unfold tailWord_1023978
  simp only [CollatzResearch.WordTrace]
  refine ⟨9336886471077515591120147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24898363922873374909653725 9336886471077515591120147)
  ·
    refine ⟨14005329706616273386680221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9336886471077515591120147 14005329706616273386680221)
    ·
      refine ⟨5251998639981102520005083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14005329706616273386680221 5251998639981102520005083)
      ·
        refine ⟨7877997959971653780007625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5251998639981102520005083 7877997959971653780007625)
        ·
          refine ⟨5908498469978740335005719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7877997959971653780007625 5908498469978740335005719)
          ·
            refine ⟨8862747704968110502508579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5908498469978740335005719 8862747704968110502508579)
            ·
              refine ⟨13294121557452165753762869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8862747704968110502508579 13294121557452165753762869)
              ·
                refine ⟨1246323896011140539415269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13294121557452165753762869 1246323896011140539415269)
                ·
                  refine ⟨233685730502088851140363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1246323896011140539415269 233685730502088851140363)
                  ·
                    rfl

theorem cell21_1023978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_1023978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1023978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1023978 prefixEnd_1023978 := by exact prefixLift 1023978
  have htrace : WordTrace (prefixWord ++ tailWord_1023978) baseStart_1023978 baseEnd_1023978 := by
    simpa [prefixWord, tailWord_1023978, baseEnd_1023978] using wordTrace_append hprefix tailTrace_1023978
  have hstable : (prefixWord ++ tailWord_1023978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023978).length < 2 ^ (prefixWord ++ tailWord_1023978).sum := by decide
  have hdescent : baseEnd_1023978 < baseStart_1023978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023981 : List Nat := [1, 5, 1, 4, 1, 1, 1, 2, 5]
def baseStart_1023981 : Nat := 118140960795 + 1023981 * 2 ^ 59
def prefixEnd_1023981 : Nat := 4983230072969 + 3 ^ 40 * 1023981 * 2
def baseEnd_1023981 : Nat := 233686415142961512590357

theorem tailTrace_1023981 : CollatzResearch.WordTrace tailWord_1023981 prefixEnd_1023981 233686415142961512590357 := by
  unfold tailWord_1023981
  simp only [CollatzResearch.WordTrace]
  refine ⟨37347655303299193876839797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24898436868866129251226531 37347655303299193876839797)
  ·
    refine ⟨3501342684684299425953731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37347655303299193876839797 3501342684684299425953731)
    ·
      refine ⟨5252014027026449138930597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3501342684684299425953731 5252014027026449138930597)
      ·
        refine ⟨984752630067459213549487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5252014027026449138930597 984752630067459213549487)
        ·
          refine ⟨1477128945101188820324231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 984752630067459213549487 1477128945101188820324231)
          ·
            refine ⟨2215693417651783230486347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1477128945101188820324231 2215693417651783230486347)
            ·
              refine ⟨3323540126477674845729521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2215693417651783230486347 3323540126477674845729521)
              ·
                refine ⟨2492655094858256134297141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3323540126477674845729521 2492655094858256134297141)
                ·
                  refine ⟨233686415142961512590357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2492655094858256134297141 233686415142961512590357)
                  ·
                    rfl

theorem cell21_1023981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_1023981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1023981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1023981 prefixEnd_1023981 := by exact prefixLift 1023981
  have htrace : WordTrace (prefixWord ++ tailWord_1023981) baseStart_1023981 baseEnd_1023981 := by
    simpa [prefixWord, tailWord_1023981, baseEnd_1023981] using wordTrace_append hprefix tailTrace_1023981
  have hstable : (prefixWord ++ tailWord_1023981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023981).length < 2 ^ (prefixWord ++ tailWord_1023981).sum := by decide
  have hdescent : baseEnd_1023981 < baseStart_1023981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023998 : List Nat := [4, 2, 2, 2, 1, 2, 2, 3, 3]
def baseStart_1023998 : Nat := 118140960795 + 1023998 * 2 ^ 59
def prefixEnd_1023998 : Nat := 4983230072969 + 3 ^ 40 * 1023998 * 2
def baseEnd_1023998 : Nat := 233690294774573260806989

theorem tailTrace_1023998 : CollatzResearch.WordTrace tailWord_1023998 prefixEnd_1023998 233690294774573260806989 := by
  unfold tailWord_1023998
  simp only [CollatzResearch.WordTrace]
  refine ⟨4668534418029700722526081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24898850229491737186805765 4668534418029700722526081)
  ·
    refine ⟨3501400813522275541894561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4668534418029700722526081 3501400813522275541894561)
    ·
      refine ⟨2626050610141706656420921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3501400813522275541894561 2626050610141706656420921)
      ·
        refine ⟨1969537957606279992315691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2626050610141706656420921 1969537957606279992315691)
        ·
          refine ⟨2954306936409419988473537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1969537957606279992315691 2954306936409419988473537)
          ·
            refine ⟨2215730202307064991355153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2954306936409419988473537 2215730202307064991355153)
            ·
              refine ⟨1661797651730298743516365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2215730202307064991355153 1661797651730298743516365)
              ·
                refine ⟨623174119398862028818637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1661797651730298743516365 623174119398862028818637)
                ·
                  refine ⟨233690294774573260806989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 623174119398862028818637 233690294774573260806989)
                  ·
                    rfl

theorem cell21_1023998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_1023998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1023998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1023998 prefixEnd_1023998 := by exact prefixLift 1023998
  have htrace : WordTrace (prefixWord ++ tailWord_1023998) baseStart_1023998 baseEnd_1023998 := by
    simpa [prefixWord, tailWord_1023998, baseEnd_1023998] using wordTrace_append hprefix tailTrace_1023998
  have hstable : (prefixWord ++ tailWord_1023998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023998).length < 2 ^ (prefixWord ++ tailWord_1023998).sum := by decide
  have hdescent : baseEnd_1023998 < baseStart_1023998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024054 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 8]
def baseStart_1024054 : Nat := 118140960795 + 1024054 * 2 ^ 59
def prefixEnd_1024054 : Nat := 4983230072969 + 3 ^ 40 * 1024054 * 2
def baseEnd_1024054 : Nat := 233703074737529607873541

theorem tailTrace_1024054 : CollatzResearch.WordTrace tailWord_1024054 prefixEnd_1024054 233703074737529607873541 := by
  unfold tailWord_1024054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2334394864502170459015451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24900211888023151562831477 2334394864502170459015451)
  ·
    refine ⟨3501592296753255688523177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2334394864502170459015451 3501592296753255688523177)
    ·
      refine ⟨2626194222564941766392383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3501592296753255688523177 2626194222564941766392383)
      ·
        refine ⟨3939291333847412649588575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2626194222564941766392383 3939291333847412649588575)
        ·
          refine ⟨5908937000771118974382863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3939291333847412649588575 5908937000771118974382863)
          ·
            refine ⟨8863405501156678461574295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5908937000771118974382863 8863405501156678461574295)
            ·
              refine ⟨13295108251735017692361443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8863405501156678461574295 13295108251735017692361443)
              ·
                refine ⟨19942662377602526538542165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13295108251735017692361443 19942662377602526538542165)
                ·
                  refine ⟨233703074737529607873541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19942662377602526538542165 233703074737529607873541)
                  ·
                    rfl

theorem cell21_1024054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_1024054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1024054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1024054 prefixEnd_1024054 := by exact prefixLift 1024054
  have htrace : WordTrace (prefixWord ++ tailWord_1024054) baseStart_1024054 baseEnd_1024054 := by
    simpa [prefixWord, tailWord_1024054, baseEnd_1024054] using wordTrace_append hprefix tailTrace_1024054
  have hstable : (prefixWord ++ tailWord_1024054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024054).length < 2 ^ (prefixWord ++ tailWord_1024054).sum := by decide
  have hdescent : baseEnd_1024054 < baseStart_1024054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024133 : List Nat := [1, 3, 1, 1, 5, 1, 4, 2, 3]
def baseStart_1024133 : Nat := 118140960795 + 1024133 * 2 ^ 59
def prefixEnd_1024133 : Nat := 4983230072969 + 3 ^ 40 * 1024133 * 2
def baseEnd_1024133 : Nat := 233721103613843026056713

theorem tailTrace_1024133 : CollatzResearch.WordTrace tailWord_1024133 prefixEnd_1024133 233721103613843026056713 := by
  unfold tailWord_1024133
  simp only [CollatzResearch.WordTrace]
  refine ⟨37353199198748523836373053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24902132799165682557582035 37353199198748523836373053)
  ·
    refine ⟨14007449699530696438639895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37353199198748523836373053 14007449699530696438639895)
    ·
      refine ⟨21011174549296044657959843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14007449699530696438639895 21011174549296044657959843)
      ·
        refine ⟨31516761823944066986939765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21011174549296044657959843 31516761823944066986939765)
        ·
          refine ⟨2954696420994756280025603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31516761823944066986939765 2954696420994756280025603)
          ·
            refine ⟨4432044631492134420038405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2954696420994756280025603 4432044631492134420038405)
            ·
              refine ⟨831008368404775203757201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4432044631492134420038405 831008368404775203757201)
              ·
                refine ⟨623256276303581402817901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 831008368404775203757201 623256276303581402817901)
                ·
                  refine ⟨233721103613843026056713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 623256276303581402817901 233721103613843026056713)
                  ·
                    rfl

theorem cell21_1024133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 2, 3].length) (baseStart_1024133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1024133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1024133 prefixEnd_1024133 := by exact prefixLift 1024133
  have htrace : WordTrace (prefixWord ++ tailWord_1024133) baseStart_1024133 baseEnd_1024133 := by
    simpa [prefixWord, tailWord_1024133, baseEnd_1024133] using wordTrace_append hprefix tailTrace_1024133
  have hstable : (prefixWord ++ tailWord_1024133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024133).length < 2 ^ (prefixWord ++ tailWord_1024133).sum := by decide
  have hdescent : baseEnd_1024133 < baseStart_1024133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024161 : List Nat := [1, 2, 3, 3, 1, 3, 3, 5]
def baseStart_1024161 : Nat := 118140960795 + 1024161 * 2 ^ 59
def prefixEnd_1024161 : Nat := 4983230072969 + 3 ^ 40 * 1024161 * 2
def baseEnd_1024161 : Nat := 77909164531773733196663

theorem tailTrace_1024161 : CollatzResearch.WordTrace tailWord_1024161 prefixEnd_1024161 77909164531773733196663 := by
  unfold tailWord_1024161
  simp only [CollatzResearch.WordTrace]
  refine ⟨37354220442647084618392337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24902813628431389745594891 37354220442647084618392337)
  ·
    refine ⟨28015665331985313463794253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37354220442647084618392337 28015665331985313463794253)
    ·
      refine ⟨10505874499494492548922845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28015665331985313463794253 10505874499494492548922845)
      ·
        refine ⟨3939702937310434705846067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10505874499494492548922845 3939702937310434705846067)
        ·
          refine ⟨5909554405965652058769101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3939702937310434705846067 5909554405965652058769101)
          ·
            refine ⟨2216082902237119522038413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5909554405965652058769101 2216082902237119522038413)
            ·
              refine ⟨831031088338919820764405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2216082902237119522038413 831031088338919820764405)
              ·
                refine ⟨77909164531773733196663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 831031088338919820764405 77909164531773733196663)
                ·
                  rfl

theorem cell21_1024161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 5].length) (baseStart_1024161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1024161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1024161 prefixEnd_1024161 := by exact prefixLift 1024161
  have htrace : WordTrace (prefixWord ++ tailWord_1024161) baseStart_1024161 baseEnd_1024161 := by
    simpa [prefixWord, tailWord_1024161, baseEnd_1024161] using wordTrace_append hprefix tailTrace_1024161
  have hstable : (prefixWord ++ tailWord_1024161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024161).length < 2 ^ (prefixWord ++ tailWord_1024161).sum := by decide
  have hdescent : baseEnd_1024161 < baseStart_1024161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024181 : List Nat := [1, 3, 3, 4, 2, 1, 1, 2, 4]
def baseStart_1024181 : Nat := 118140960795 + 1024181 * 2 ^ 59
def prefixEnd_1024181 : Nat := 4983230072969 + 3 ^ 40 * 1024181 * 2
def baseEnd_1024181 : Nat := 233732057867805609256615

theorem tailTrace_1024181 : CollatzResearch.WordTrace tailWord_1024181 prefixEnd_1024181 233732057867805609256615 := by
  unfold tailWord_1024181
  simp only [CollatzResearch.WordTrace]
  refine ⟨37354949902574628034120397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24903299935049752022746931 37354949902574628034120397)
  ·
    refine ⟨14008106213465485512795149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37354949902574628034120397 14008106213465485512795149)
    ·
      refine ⟨5253039830049557067298181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14008106213465485512795149 5253039830049557067298181)
      ·
        refine ⟨984944968134291950118409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5253039830049557067298181 984944968134291950118409)
        ·
          refine ⟨738708726100718962588807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 984944968134291950118409 738708726100718962588807)
          ·
            refine ⟨1108063089151078443883211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738708726100718962588807 1108063089151078443883211)
            ·
              refine ⟨1662094633726617665824817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1108063089151078443883211 1662094633726617665824817)
              ·
                refine ⟨1246570975294963249368613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1662094633726617665824817 1246570975294963249368613)
                ·
                  refine ⟨233732057867805609256615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1246570975294963249368613 233732057867805609256615)
                  ·
                    rfl

theorem cell21_1024181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 4].length) (baseStart_1024181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1024181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1024181 prefixEnd_1024181 := by exact prefixLift 1024181
  have htrace : WordTrace (prefixWord ++ tailWord_1024181) baseStart_1024181 baseEnd_1024181 := by
    simpa [prefixWord, tailWord_1024181, baseEnd_1024181] using wordTrace_append hprefix tailTrace_1024181
  have hstable : (prefixWord ++ tailWord_1024181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024181).length < 2 ^ (prefixWord ++ tailWord_1024181).sum := by decide
  have hdescent : baseEnd_1024181 < baseStart_1024181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024192 : List Nat := [2, 1, 1, 2, 5, 1, 2, 4, 3]
def baseStart_1024192 : Nat := 118140960795 + 1024192 * 2 ^ 59
def prefixEnd_1024192 : Nat := 4983230072969 + 3 ^ 40 * 1024192 * 2
def baseEnd_1024192 : Nat := 233734568217672034573259

theorem tailTrace_1024192 : CollatzResearch.WordTrace tailWord_1024192 prefixEnd_1024192 233734568217672034573259 := by
  unfold tailWord_1024192
  simp only [CollatzResearch.WordTrace]
  refine ⟨18677675552767388456385415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24903567403689851275180553 18677675552767388456385415)
  ·
    refine ⟨28016513329151082684578123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18677675552767388456385415 28016513329151082684578123)
    ·
      refine ⟨42024769993726624026867185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28016513329151082684578123 42024769993726624026867185)
      ·
        refine ⟨31518577495294968020150389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42024769993726624026867185 31518577495294968020150389)
        ·
          refine ⟨2954866640183903251889099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31518577495294968020150389 2954866640183903251889099)
          ·
            refine ⟨4432299960275854877833649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2954866640183903251889099 4432299960275854877833649)
            ·
              refine ⟨3324224970206891158375237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4432299960275854877833649 3324224970206891158375237)
              ·
                refine ⟨623292181913792092195357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3324224970206891158375237 623292181913792092195357)
                ·
                  refine ⟨233734568217672034573259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 623292181913792092195357 233734568217672034573259)
                  ·
                    rfl

theorem cell21_1024192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 4, 3].length) (baseStart_1024192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1024192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1024192 prefixEnd_1024192 := by exact prefixLift 1024192
  have htrace : WordTrace (prefixWord ++ tailWord_1024192) baseStart_1024192 baseEnd_1024192 := by
    simpa [prefixWord, tailWord_1024192, baseEnd_1024192] using wordTrace_append hprefix tailTrace_1024192
  have hstable : (prefixWord ++ tailWord_1024192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024192).length < 2 ^ (prefixWord ++ tailWord_1024192).sum := by decide
  have hdescent : baseEnd_1024192 < baseStart_1024192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024203 : List Nat := [1, 1, 1, 1, 3, 2, 4, 8]
def baseStart_1024203 : Nat := 118140960795 + 1024203 * 2 ^ 59
def prefixEnd_1024203 : Nat := 4983230072969 + 3 ^ 40 * 1024203 * 2
def baseEnd_1024203 : Nat := 77912359522512819963301

theorem tailTrace_1024203 : CollatzResearch.WordTrace tailWord_1024203 prefixEnd_1024203 77912359522512819963301 := by
  unfold tailWord_1024203
  simp only [CollatzResearch.WordTrace]
  refine ⟨37355752308494925791421263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24903834872329950527614175 37355752308494925791421263)
  ·
    refine ⟨56033628462742388687131895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37355752308494925791421263 56033628462742388687131895)
    ·
      refine ⟨84050442694113583030697843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56033628462742388687131895 84050442694113583030697843)
      ·
        refine ⟨126075664041170374546046765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84050442694113583030697843 126075664041170374546046765)
        ·
          refine ⟨47278374015438890454767537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126075664041170374546046765 47278374015438890454767537)
          ·
            refine ⟨35458780511579167841075653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47278374015438890454767537 35458780511579167841075653)
            ·
              refine ⟨6648521345921093970201685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35458780511579167841075653 6648521345921093970201685)
              ·
                refine ⟨77912359522512819963301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6648521345921093970201685 77912359522512819963301)
                ·
                  rfl

theorem cell21_1024203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 8].length) (baseStart_1024203 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1024203 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1024203 prefixEnd_1024203 := by exact prefixLift 1024203
  have htrace : WordTrace (prefixWord ++ tailWord_1024203) baseStart_1024203 baseEnd_1024203 := by
    simpa [prefixWord, tailWord_1024203, baseEnd_1024203] using wordTrace_append hprefix tailTrace_1024203
  have hstable : (prefixWord ++ tailWord_1024203).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024203).length < 2 ^ (prefixWord ++ tailWord_1024203).sum := by decide
  have hdescent : baseEnd_1024203 < baseStart_1024203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024237 : List Nat := [1, 5, 1, 2, 3, 2, 7]
def baseStart_1024237 : Nat := 118140960795 + 1024237 * 2 ^ 59
def prefixEnd_1024237 : Nat := 4983230072969 + 3 ^ 40 * 1024237 * 2
def baseEnd_1024237 : Nat := 25971648647862439591463

theorem tailTrace_1024237 : CollatzResearch.WordTrace tailWord_1024237 prefixEnd_1024237 25971648647862439591463 := by
  unfold tailWord_1024237
  simp only [CollatzResearch.WordTrace]
  refine ⟨37356992390371749598158965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24904661593581166398772643 37356992390371749598158965)
  ·
    refine ⟨3502218036597351524827403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37356992390371749598158965 3502218036597351524827403)
    ·
      refine ⟨5253327054896027287241105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3502218036597351524827403 5253327054896027287241105)
      ·
        refine ⟨3939995291172020465430829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5253327054896027287241105 3939995291172020465430829)
        ·
          refine ⟨1477498234189507674536561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3939995291172020465430829 1477498234189507674536561)
          ·
            refine ⟨1108123675642130755902421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1477498234189507674536561 1108123675642130755902421)
            ·
              refine ⟨25971648647862439591463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1108123675642130755902421 25971648647862439591463)
              ·
                rfl

theorem cell21_1024237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 7].length) (baseStart_1024237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1024237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1024237 prefixEnd_1024237 := by exact prefixLift 1024237
  have htrace : WordTrace (prefixWord ++ tailWord_1024237) baseStart_1024237 baseEnd_1024237 := by
    simpa [prefixWord, tailWord_1024237, baseEnd_1024237] using wordTrace_append hprefix tailTrace_1024237
  have hstable : (prefixWord ++ tailWord_1024237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024237).length < 2 ^ (prefixWord ++ tailWord_1024237).sum := by decide
  have hdescent : baseEnd_1024237 < baseStart_1024237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024296 : List Nat := [2, 1, 5, 1, 3, 9]
def baseStart_1024296 : Nat := 118140960795 + 1024296 * 2 ^ 59
def prefixEnd_1024296 : Nat := 4983230072969 + 3 ^ 40 * 1024296 * 2
def baseEnd_1024296 : Nat := 8657714904984850549619

theorem tailTrace_1024296 : CollatzResearch.WordTrace tailWord_1024296 prefixEnd_1024296 8657714904984850549619 := by
  unfold tailWord_1024296
  simp only [CollatzResearch.WordTrace]
  refine ⟨18679572148579001337278371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24906096198105335116371161 18679572148579001337278371)
  ·
    refine ⟨28019358222868502005917557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18679572148579001337278371 28019358222868502005917557)
    ·
      refine ⟨2626814833393922063054771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28019358222868502005917557 2626814833393922063054771)
      ·
        refine ⟨3940222250090883094582157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2626814833393922063054771 3940222250090883094582157)
        ·
          refine ⟨1477583343784081160468309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3940222250090883094582157 1477583343784081160468309)
          ·
            refine ⟨8657714904984850549619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1477583343784081160468309 8657714904984850549619)
            ·
              rfl

theorem cell21_1024296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 9].length) (baseStart_1024296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1024296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1024296 prefixEnd_1024296 := by exact prefixLift 1024296
  have htrace : WordTrace (prefixWord ++ tailWord_1024296) baseStart_1024296 baseEnd_1024296 := by
    simpa [prefixWord, tailWord_1024296, baseEnd_1024296] using wordTrace_append hprefix tailTrace_1024296
  have hstable : (prefixWord ++ tailWord_1024296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024296).length < 2 ^ (prefixWord ++ tailWord_1024296).sum := by decide
  have hdescent : baseEnd_1024296 < baseStart_1024296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024302 : List Nat := [4, 1, 3, 3, 1, 1, 1, 4, 3]
def baseStart_1024302 : Nat := 118140960795 + 1024302 * 2 ^ 59
def prefixEnd_1024302 : Nat := 4983230072969 + 3 ^ 40 * 1024302 * 2
def baseEnd_1024302 : Nat := 233759671716336287739701

theorem tailTrace_1024302 : CollatzResearch.WordTrace tailWord_1024302 prefixEnd_1024302 233759671716336287739701 := by
  unfold tailWord_1024302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4669920391892033212409395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24906242090090843799516773 4669920391892033212409395)
  ·
    refine ⟨7004880587838049818614093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4669920391892033212409395 7004880587838049818614093)
    ·
      refine ⟨2626830220439268681980285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7004880587838049818614093 2626830220439268681980285)
      ·
        refine ⟨985061332664725755742607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2626830220439268681980285 985061332664725755742607)
        ·
          refine ⟨1477591998997088633613911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985061332664725755742607 1477591998997088633613911)
          ·
            refine ⟨2216387998495632950420867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1477591998997088633613911 2216387998495632950420867)
            ·
              refine ⟨3324581997743449425631301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2216387998495632950420867 3324581997743449425631301)
              ·
                refine ⟨623359124576896767305869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3324581997743449425631301 623359124576896767305869)
                ·
                  refine ⟨233759671716336287739701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 623359124576896767305869 233759671716336287739701)
                  ·
                    rfl

theorem cell21_1024302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_1024302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1024302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1024302 prefixEnd_1024302 := by exact prefixLift 1024302
  have htrace : WordTrace (prefixWord ++ tailWord_1024302) baseStart_1024302 baseEnd_1024302 := by
    simpa [prefixWord, tailWord_1024302, baseEnd_1024302] using wordTrace_append hprefix tailTrace_1024302
  have hstable : (prefixWord ++ tailWord_1024302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024302).length < 2 ^ (prefixWord ++ tailWord_1024302).sum := by decide
  have hdescent : baseEnd_1024302 < baseStart_1024302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024313 : List Nat := [1, 2, 1, 6, 1, 3, 1, 6]
def baseStart_1024313 : Nat := 118140960795 + 1024313 * 2 ^ 59
def prefixEnd_1024313 : Nat := 4983230072969 + 3 ^ 40 * 1024313 * 2
def baseEnd_1024313 : Nat := 77920727355400904352115

theorem tailTrace_1024313 : CollatzResearch.WordTrace tailWord_1024313 prefixEnd_1024313 77920727355400904352115 := by
  unfold tailWord_1024313
  simp only [CollatzResearch.WordTrace]
  refine ⟨37359764338096414577925593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24906509558730943051950395 37359764338096414577925593)
  ·
    refine ⟨28019823253572310933444195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37359764338096414577925593 28019823253572310933444195)
    ·
      refine ⟨42029734880358466400166293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28019823253572310933444195 42029734880358466400166293)
      ·
        refine ⟨1970143822516803112507795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42029734880358466400166293 1970143822516803112507795)
        ·
          refine ⟨2955215733775204668761693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1970143822516803112507795 2955215733775204668761693)
          ·
            refine ⟨1108205900165701750785635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2955215733775204668761693 1108205900165701750785635)
            ·
              refine ⟨1662308850248552626178453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1108205900165701750785635 1662308850248552626178453)
              ·
                refine ⟨77920727355400904352115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1662308850248552626178453 77920727355400904352115)
                ·
                  rfl

theorem cell21_1024313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 6].length) (baseStart_1024313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1024313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1024313 prefixEnd_1024313 := by exact prefixLift 1024313
  have htrace : WordTrace (prefixWord ++ tailWord_1024313) baseStart_1024313 baseEnd_1024313 := by
    simpa [prefixWord, tailWord_1024313, baseEnd_1024313] using wordTrace_append hprefix tailTrace_1024313
  have hstable : (prefixWord ++ tailWord_1024313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024313).length < 2 ^ (prefixWord ++ tailWord_1024313).sum := by decide
  have hdescent : baseEnd_1024313 < baseStart_1024313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024355 : List Nat := [1, 1, 1, 5, 2, 1, 10]
def baseStart_1024355 : Nat := 118140960795 + 1024355 * 2 ^ 59
def prefixEnd_1024355 : Nat := 4983230072969 + 3 ^ 40 * 1024355 * 2
def baseEnd_1024355 : Nat := 25974640782046663706251

theorem tailTrace_1024355 : CollatzResearch.WordTrace tailWord_1024355 prefixEnd_1024355 25974640782046663706251 := by
  unfold tailWord_1024355
  simp only [CollatzResearch.WordTrace]
  refine ⟨37361296203944255750954519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24907530802629503833969679 37361296203944255750954519)
  ·
    refine ⟨56041944305916383626431779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37361296203944255750954519 56041944305916383626431779)
    ·
      refine ⟨84062916458874575439647669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56041944305916383626431779 84062916458874575439647669)
      ·
        refine ⟨7880898418019491447466969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84062916458874575439647669 7880898418019491447466969)
        ·
          refine ⟨5910673813514618585600227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7880898418019491447466969 5910673813514618585600227)
          ·
            refine ⟨8866010720271927878400341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5910673813514618585600227 8866010720271927878400341)
            ·
              refine ⟨25974640782046663706251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8866010720271927878400341 25974640782046663706251)
              ·
                rfl

theorem cell21_1024355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 10].length) (baseStart_1024355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1024355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1024355 prefixEnd_1024355 := by exact prefixLift 1024355
  have htrace : WordTrace (prefixWord ++ tailWord_1024355) baseStart_1024355 baseEnd_1024355 := by
    simpa [prefixWord, tailWord_1024355, baseEnd_1024355] using wordTrace_append hprefix tailTrace_1024355
  have hstable : (prefixWord ++ tailWord_1024355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024355).length < 2 ^ (prefixWord ++ tailWord_1024355).sum := by decide
  have hdescent : baseEnd_1024355 < baseStart_1024355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024426 : List Nat := [3, 1, 6, 1, 1, 2, 2, 1, 4]
def baseStart_1024426 : Nat := 118140960795 + 1024426 * 2 ^ 59
def prefixEnd_1024426 : Nat := 4983230072969 + 3 ^ 40 * 1024426 * 2
def baseEnd_1024426 : Nat := 233787970205739627672781

theorem tailTrace_1024426 : CollatzResearch.WordTrace tailWord_1024426 prefixEnd_1024426 233787970205739627672781 := by
  unfold tailWord_1024426
  simp only [CollatzResearch.WordTrace]
  refine ⟨9340971446671758719197283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24909257191124689917859421 9340971446671758719197283)
  ·
    refine ⟨14011457170007638078795925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9340971446671758719197283 14011457170007638078795925)
    ·
      refine ⟨656787054844108034943559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14011457170007638078795925 656787054844108034943559)
      ·
        refine ⟨985180582266162052415339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656787054844108034943559 985180582266162052415339)
        ·
          refine ⟨1477770873399243078623009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985180582266162052415339 1477770873399243078623009)
          ·
            refine ⟨1108328155049432308967257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1477770873399243078623009 1108328155049432308967257)
            ·
              refine ⟨831246116287074231725443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1108328155049432308967257 831246116287074231725443)
              ·
                refine ⟨1246869174430611347588165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 831246116287074231725443 1246869174430611347588165)
                ·
                  refine ⟨233787970205739627672781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1246869174430611347588165 233787970205739627672781)
                  ·
                    rfl

theorem cell21_1024426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 4].length) (baseStart_1024426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1024426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1024426 prefixEnd_1024426 := by exact prefixLift 1024426
  have htrace : WordTrace (prefixWord ++ tailWord_1024426) baseStart_1024426 baseEnd_1024426 := by
    simpa [prefixWord, tailWord_1024426, baseEnd_1024426] using wordTrace_append hprefix tailTrace_1024426
  have hstable : (prefixWord ++ tailWord_1024426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024426).length < 2 ^ (prefixWord ++ tailWord_1024426).sum := by decide
  have hdescent : baseEnd_1024426 < baseStart_1024426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024538 : List Nat := [3, 1, 1, 3, 1, 1, 3, 3, 5]
def baseStart_1024538 : Nat := 118140960795 + 1024538 * 2 ^ 59
def prefixEnd_1024538 : Nat := 4983230072969 + 3 ^ 40 * 1024538 * 2
def baseEnd_1024538 : Nat := 233813530131652321805885

theorem tailTrace_1024538 : CollatzResearch.WordTrace tailWord_1024538 prefixEnd_1024538 233813530131652321805885 := by
  unfold tailWord_1024538
  simp only [CollatzResearch.WordTrace]
  refine ⟨9341992690570319501216567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24911980508187518669910845 9341992690570319501216567)
  ·
    refine ⟨14012989035855479251824851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9341992690570319501216567 14012989035855479251824851)
    ·
      refine ⟨21019483553783218877737277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14012989035855479251824851 21019483553783218877737277)
      ·
        refine ⟨7882306332668707079151479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21019483553783218877737277 7882306332668707079151479)
        ·
          refine ⟨11823459499003060618727219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7882306332668707079151479 11823459499003060618727219)
          ·
            refine ⟨17735189248504590928090829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11823459499003060618727219 17735189248504590928090829)
            ·
              refine ⟨6650695968189221598034061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17735189248504590928090829 6650695968189221598034061)
              ·
                refine ⟨2494010988070958099262773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6650695968189221598034061 2494010988070958099262773)
                ·
                  refine ⟨233813530131652321805885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2494010988070958099262773 233813530131652321805885)
                  ·
                    rfl

theorem cell21_1024538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_1024538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1024538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1024538 prefixEnd_1024538 := by exact prefixLift 1024538
  have htrace : WordTrace (prefixWord ++ tailWord_1024538) baseStart_1024538 baseEnd_1024538 := by
    simpa [prefixWord, tailWord_1024538, baseEnd_1024538] using wordTrace_append hprefix tailTrace_1024538
  have hstable : (prefixWord ++ tailWord_1024538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024538).length < 2 ^ (prefixWord ++ tailWord_1024538).sum := by decide
  have hdescent : baseEnd_1024538 < baseStart_1024538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024558 : List Nat := [4, 1, 3, 1, 3, 2, 2, 5]
def baseStart_1024558 : Nat := 118140960795 + 1024558 * 2 ^ 59
def prefixEnd_1024558 : Nat := 4983230072969 + 3 ^ 40 * 1024558 * 2
def baseEnd_1024558 : Nat := 77939364801378910490837

theorem tailTrace_1024558 : CollatzResearch.WordTrace tailWord_1024558 prefixEnd_1024558 77939364801378910490837 := by
  unfold tailWord_1024558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4671087527776102677574291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24912466814805880947062885 4671087527776102677574291)
  ·
    refine ⟨7006631291664154016361437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4671087527776102677574291 7006631291664154016361437)
    ·
      refine ⟨2627486734374057756135539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7006631291664154016361437 2627486734374057756135539)
      ·
        refine ⟨3941230101561086634203309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2627486734374057756135539 3941230101561086634203309)
        ·
          refine ⟨1477961288085407487826241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3941230101561086634203309 1477961288085407487826241)
          ·
            refine ⟨1108470966064055615869681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1477961288085407487826241 1108470966064055615869681)
            ·
              refine ⟨831353224548041711902261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1108470966064055615869681 831353224548041711902261)
              ·
                refine ⟨77939364801378910490837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 831353224548041711902261 77939364801378910490837)
                ·
                  rfl

theorem cell21_1024558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_1024558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1024558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1024558 prefixEnd_1024558 := by exact prefixLift 1024558
  have htrace : WordTrace (prefixWord ++ tailWord_1024558) baseStart_1024558 baseEnd_1024558 := by
    simpa [prefixWord, tailWord_1024558, baseEnd_1024558] using wordTrace_append hprefix tailTrace_1024558
  have hstable : (prefixWord ++ tailWord_1024558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024558).length < 2 ^ (prefixWord ++ tailWord_1024558).sum := by decide
  have hdescent : baseEnd_1024558 < baseStart_1024558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024572 : List Nat := [2, 2, 2, 2, 3, 1, 3, 3, 3]
def baseStart_1024572 : Nat := 118140960795 + 1024572 * 2 ^ 59
def prefixEnd_1024572 : Nat := 4983230072969 + 3 ^ 40 * 1024572 * 2
def baseEnd_1024572 : Nat := 233821289394875818239149

theorem tailTrace_1024572 : CollatzResearch.WordTrace tailWord_1024572 prefixEnd_1024572 233821289394875818239149 := by
  unfold tailWord_1024572
  simp only [CollatzResearch.WordTrace]
  refine ⟨18684605422079050905801985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24912807229438734541069313 18684605422079050905801985)
  ·
    refine ⟨14013454066559288179351489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18684605422079050905801985 14013454066559288179351489)
    ·
      refine ⟨10510090549919466134513617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14013454066559288179351489 10510090549919466134513617)
      ·
        refine ⟨7882567912439599600885213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10510090549919466134513617 7882567912439599600885213)
        ·
          refine ⟨2955962967164849850331955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7882567912439599600885213 2955962967164849850331955)
          ·
            refine ⟨4433944450747274775497933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2955962967164849850331955 4433944450747274775497933)
            ·
              refine ⟨1662729169030228040811725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4433944450747274775497933 1662729169030228040811725)
              ·
                refine ⟨623523438386335515304397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1662729169030228040811725 623523438386335515304397)
                ·
                  refine ⟨233821289394875818239149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 623523438386335515304397 233821289394875818239149)
                  ·
                    rfl

theorem cell21_1024572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 3, 3].length) (baseStart_1024572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1024572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1024572 prefixEnd_1024572 := by exact prefixLift 1024572
  have htrace : WordTrace (prefixWord ++ tailWord_1024572) baseStart_1024572 baseEnd_1024572 := by
    simpa [prefixWord, tailWord_1024572, baseEnd_1024572] using wordTrace_append hprefix tailTrace_1024572
  have hstable : (prefixWord ++ tailWord_1024572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024572).length < 2 ^ (prefixWord ++ tailWord_1024572).sum := by decide
  have hdescent : baseEnd_1024572 < baseStart_1024572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024583 : List Nat := [1, 1, 4, 1, 4, 1, 9]
def baseStart_1024583 : Nat := 118140960795 + 1024583 * 2 ^ 59
def prefixEnd_1024583 : Nat := 4983230072969 + 3 ^ 40 * 1024583 * 2
def baseEnd_1024583 : Nat := 25980422193860249283977

theorem tailTrace_1024583 : CollatzResearch.WordTrace tailWord_1024583 prefixEnd_1024583 25980422193860249283977 := by
  unfold tailWord_1024583
  simp only [CollatzResearch.WordTrace]
  refine ⟨37369612047118250690254403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24913074698078833793502935 37369612047118250690254403)
  ·
    refine ⟨56054418070677376035381605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37369612047118250690254403 56054418070677376035381605)
    ·
      refine ⟨10510203388252008006634051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56054418070677376035381605 10510203388252008006634051)
      ·
        refine ⟨15765305082378012009951077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10510203388252008006634051 15765305082378012009951077)
        ·
          refine ⟨2955994702945877251865827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15765305082378012009951077 2955994702945877251865827)
          ·
            refine ⟨4433992054418815877798741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2955994702945877251865827 4433992054418815877798741)
            ·
              refine ⟨25980422193860249283977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4433992054418815877798741 25980422193860249283977)
              ·
                rfl

theorem cell21_1024583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 9].length) (baseStart_1024583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1024583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1024583 prefixEnd_1024583 := by exact prefixLift 1024583
  have htrace : WordTrace (prefixWord ++ tailWord_1024583) baseStart_1024583 baseEnd_1024583 := by
    simpa [prefixWord, tailWord_1024583, baseEnd_1024583] using wordTrace_append hprefix tailTrace_1024583
  have hstable : (prefixWord ++ tailWord_1024583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024583).length < 2 ^ (prefixWord ++ tailWord_1024583).sum := by decide
  have hdescent : baseEnd_1024583 < baseStart_1024583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024645 : List Nat := [1, 3, 1, 1, 4, 2, 1, 4, 4]
def baseStart_1024645 : Nat := 118140960795 + 1024645 * 2 ^ 59
def prefixEnd_1024645 : Nat := 4983230072969 + 3 ^ 40 * 1024645 * 2
def baseEnd_1024645 : Nat := 233837948989443913522333

theorem tailTrace_1024645 : CollatzResearch.WordTrace tailWord_1024645 prefixEnd_1024645 233837948989443913522333 := by
  unfold tailWord_1024645
  simp only [CollatzResearch.WordTrace]
  refine ⟨37371873372893635279011389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24914582248595756852674259 37371873372893635279011389)
  ·
    refine ⟨14014452514835113229629271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37371873372893635279011389 14014452514835113229629271)
    ·
      refine ⟨21021678772252669844443907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14014452514835113229629271 21021678772252669844443907)
      ·
        refine ⟨31532518158379004766665861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21021678772252669844443907 31532518158379004766665861)
        ·
          refine ⟨5912347154696063393749849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31532518158379004766665861 5912347154696063393749849)
          ·
            refine ⟨4434260366022047545312387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5912347154696063393749849 4434260366022047545312387)
            ·
              refine ⟨6651390549033071317968581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4434260366022047545312387 6651390549033071317968581)
              ·
                refine ⟨1247135727943700872119109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6651390549033071317968581 1247135727943700872119109)
                ·
                  refine ⟨233837948989443913522333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1247135727943700872119109 233837948989443913522333)
                  ·
                    rfl

theorem cell21_1024645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_1024645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1024645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1024645 prefixEnd_1024645 := by exact prefixLift 1024645
  have htrace : WordTrace (prefixWord ++ tailWord_1024645) baseStart_1024645 baseEnd_1024645 := by
    simpa [prefixWord, tailWord_1024645, baseEnd_1024645] using wordTrace_append hprefix tailTrace_1024645
  have hstable : (prefixWord ++ tailWord_1024645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024645).length < 2 ^ (prefixWord ++ tailWord_1024645).sum := by decide
  have hdescent : baseEnd_1024645 < baseStart_1024645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024676 : List Nat := [2, 3, 1, 2, 2, 1, 5, 5]
def baseStart_1024676 : Nat := 118140960795 + 1024676 * 2 ^ 59
def prefixEnd_1024676 : Nat := 4983230072969 + 3 ^ 40 * 1024676 * 2
def baseEnd_1024676 : Nat := 77948341203931582835201

theorem tailTrace_1024676 : CollatzResearch.WordTrace tailWord_1024676 prefixEnd_1024676 77948341203931582835201 := by
  unfold tailWord_1024676
  simp only [CollatzResearch.WordTrace]
  refine ⟨18686502017890663786694941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24915336023854218382259921 18686502017890663786694941)
  ·
    refine ⟨7007438256708998920010603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18686502017890663786694941 7007438256708998920010603)
    ·
      refine ⟨10511157385063498380015905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7007438256708998920010603 10511157385063498380015905)
      ·
        refine ⟨7883368038797623785011929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10511157385063498380015905 7883368038797623785011929)
        ·
          refine ⟨5912526029098217838758947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7883368038797623785011929 5912526029098217838758947)
          ·
            refine ⟨8868789043647326758138421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5912526029098217838758947 8868789043647326758138421)
            ·
              refine ⟨831448972841936883575477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8868789043647326758138421 831448972841936883575477)
              ·
                refine ⟨77948341203931582835201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 831448972841936883575477 77948341203931582835201)
                ·
                  rfl

theorem cell21_1024676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 5].length) (baseStart_1024676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1024676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1024676 prefixEnd_1024676 := by exact prefixLift 1024676
  have htrace : WordTrace (prefixWord ++ tailWord_1024676) baseStart_1024676 baseEnd_1024676 := by
    simpa [prefixWord, tailWord_1024676, baseEnd_1024676] using wordTrace_append hprefix tailTrace_1024676
  have hstable : (prefixWord ++ tailWord_1024676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024676).length < 2 ^ (prefixWord ++ tailWord_1024676).sum := by decide
  have hdescent : baseEnd_1024676 < baseStart_1024676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024682 : List Nat := [3, 1, 5, 2, 1, 1, 2, 3, 3]
def baseStart_1024682 : Nat := 118140960795 + 1024682 * 2 ^ 59
def prefixEnd_1024682 : Nat := 4983230072969 + 3 ^ 40 * 1024682 * 2
def baseEnd_1024682 : Nat := 233846392893540071405591

theorem tailTrace_1024682 : CollatzResearch.WordTrace tailWord_1024682 prefixEnd_1024682 233846392893540071405591 := by
  unfold tailWord_1024682
  simp only [CollatzResearch.WordTrace]
  refine ⟨9343305718439897649527075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24915481915839727065405533 9343305718439897649527075)
  ·
    refine ⟨14014958577659846474290613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9343305718439897649527075 14014958577659846474290613)
    ·
      refine ⟨1313902366655610606964745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14014958577659846474290613 1313902366655610606964745)
      ·
        refine ⟨985426774991707955223559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1313902366655610606964745 985426774991707955223559)
        ·
          refine ⟨1478140162487561932835339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985426774991707955223559 1478140162487561932835339)
          ·
            refine ⟨2217210243731342899253009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1478140162487561932835339 2217210243731342899253009)
            ·
              refine ⟨1662907682798507174439757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2217210243731342899253009 1662907682798507174439757)
              ·
                refine ⟨623590381049440190414909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1662907682798507174439757 623590381049440190414909)
                ·
                  refine ⟨233846392893540071405591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 623590381049440190414909 233846392893540071405591)
                  ·
                    rfl

theorem cell21_1024682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 3, 3].length) (baseStart_1024682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1024682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1024682 prefixEnd_1024682 := by exact prefixLift 1024682
  have htrace : WordTrace (prefixWord ++ tailWord_1024682) baseStart_1024682 baseEnd_1024682 := by
    simpa [prefixWord, tailWord_1024682, baseEnd_1024682] using wordTrace_append hprefix tailTrace_1024682
  have hstable : (prefixWord ++ tailWord_1024682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024682).length < 2 ^ (prefixWord ++ tailWord_1024682).sum := by decide
  have hdescent : baseEnd_1024682 < baseStart_1024682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024735 : List Nat := [1, 1, 2, 3, 2, 4, 1, 7]
def baseStart_1024735 : Nat := 118140960795 + 1024735 * 2 ^ 59
def prefixEnd_1024735 : Nat := 4983230072969 + 3 ^ 40 * 1024735 * 2
def baseEnd_1024735 : Nat := 77952829405207919007383

theorem tailTrace_1024735 : CollatzResearch.WordTrace tailWord_1024735 prefixEnd_1024735 77952829405207919007383 := by
  unfold tailWord_1024735
  simp only [CollatzResearch.WordTrace]
  refine ⟨37375155942567580649787659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24916770628378387099858439 37375155942567580649787659)
  ·
    refine ⟨56062733913851370974681489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37375155942567580649787659 56062733913851370974681489)
    ·
      refine ⟨42047050435388528231011117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56062733913851370974681489 42047050435388528231011117)
      ·
        refine ⟨15767643913270698086629169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42047050435388528231011117 15767643913270698086629169)
        ·
          refine ⟨11825732934953023564971877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15767643913270698086629169 11825732934953023564971877)
          ·
            refine ⟨2217324925303691918432227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11825732934953023564971877 2217324925303691918432227)
            ·
              refine ⟨3325987387955537877648341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2217324925303691918432227 3325987387955537877648341)
              ·
                refine ⟨77952829405207919007383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3325987387955537877648341 77952829405207919007383)
                ·
                  rfl

theorem cell21_1024735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 7].length) (baseStart_1024735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1024735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1024735 prefixEnd_1024735 := by exact prefixLift 1024735
  have htrace : WordTrace (prefixWord ++ tailWord_1024735) baseStart_1024735 baseEnd_1024735 := by
    simpa [prefixWord, tailWord_1024735, baseEnd_1024735] using wordTrace_append hprefix tailTrace_1024735
  have hstable : (prefixWord ++ tailWord_1024735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024735).length < 2 ^ (prefixWord ++ tailWord_1024735).sum := by decide
  have hdescent : baseEnd_1024735 < baseStart_1024735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024814 : List Nat := [4, 1, 3, 2, 1, 1, 1, 4, 4]
def baseStart_1024814 : Nat := 118140960795 + 1024814 * 2 ^ 59
def prefixEnd_1024814 : Nat := 4983230072969 + 3 ^ 40 * 1024814 * 2
def baseEnd_1024814 : Nat := 233876517091937175205321

theorem tailTrace_1024814 : CollatzResearch.WordTrace tailWord_1024814 prefixEnd_1024814 233876517091937175205321 := by
  unfold tailWord_1024814
  simp only [CollatzResearch.WordTrace]
  refine ⟨4672254663660172142739187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24918691539520918094608997 4672254663660172142739187)
  ·
    refine ⟨7008381995490258214108781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4672254663660172142739187 7008381995490258214108781)
    ·
      refine ⟨2628143248308846830290793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7008381995490258214108781 2628143248308846830290793)
      ·
        refine ⟨1971107436231635122718095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2628143248308846830290793 1971107436231635122718095)
        ·
          refine ⟨2956661154347452684077143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1971107436231635122718095 2956661154347452684077143)
          ·
            refine ⟨4434991731521179026115715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2956661154347452684077143 4434991731521179026115715)
            ·
              refine ⟨6652487597281768539173573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4434991731521179026115715 6652487597281768539173573)
              ·
                refine ⟨1247341424490331601095045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6652487597281768539173573 1247341424490331601095045)
                ·
                  refine ⟨233876517091937175205321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1247341424490331601095045 233876517091937175205321)
                  ·
                    rfl

theorem cell21_1024814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_1024814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1024814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1024814 prefixEnd_1024814 := by exact prefixLift 1024814
  have htrace : WordTrace (prefixWord ++ tailWord_1024814) baseStart_1024814 baseEnd_1024814 := by
    simpa [prefixWord, tailWord_1024814, baseEnd_1024814] using wordTrace_append hprefix tailTrace_1024814
  have hstable : (prefixWord ++ tailWord_1024814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024814).length < 2 ^ (prefixWord ++ tailWord_1024814).sum := by decide
  have hdescent : baseEnd_1024814 < baseStart_1024814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024904 : List Nat := [2, 1, 3, 3, 2, 1, 4, 5]
def baseStart_1024904 : Nat := 118140960795 + 1024904 * 2 ^ 59
def prefixEnd_1024904 : Nat := 4983230072969 + 3 ^ 40 * 1024904 * 2
def baseEnd_1024904 : Nat := 77965685439372339568379

theorem tailTrace_1024904 : CollatzResearch.WordTrace tailWord_1024904 prefixEnd_1024904 77965685439372339568379 := by
  unfold tailWord_1024904
  simp only [CollatzResearch.WordTrace]
  refine ⟨18690659939477661256344883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24920879919303548341793177 18690659939477661256344883)
  ·
    refine ⟨28035989909216491884517325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18690659939477661256344883 28035989909216491884517325)
    ·
      refine ⟨10513496215956184456693997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28035989909216491884517325 10513496215956184456693997)
      ·
        refine ⟨3942561080983569171260249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10513496215956184456693997 3942561080983569171260249)
        ·
          refine ⟨2956920810737676878445187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3942561080983569171260249 2956920810737676878445187)
          ·
            refine ⟨4435381216106515317667781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2956920810737676878445187 4435381216106515317667781)
            ·
              refine ⟨831633978019971622062709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4435381216106515317667781 831633978019971622062709)
              ·
                refine ⟨77965685439372339568379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 831633978019971622062709 77965685439372339568379)
                ·
                  rfl

theorem cell21_1024904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 5].length) (baseStart_1024904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1024904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1024904 prefixEnd_1024904 := by exact prefixLift 1024904
  have htrace : WordTrace (prefixWord ++ tailWord_1024904) baseStart_1024904 baseEnd_1024904 := by
    simpa [prefixWord, tailWord_1024904, baseEnd_1024904] using wordTrace_append hprefix tailTrace_1024904
  have hstable : (prefixWord ++ tailWord_1024904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024904).length < 2 ^ (prefixWord ++ tailWord_1024904).sum := by decide
  have hdescent : baseEnd_1024904 < baseStart_1024904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024932 : List Nat := [2, 3, 1, 2, 1, 2, 1, 3, 6]
def baseStart_1024932 : Nat := 118140960795 + 1024932 * 2 ^ 59
def prefixEnd_1024932 : Nat := 4983230072969 + 3 ^ 40 * 1024932 * 2
def baseEnd_1024932 : Nat := 233903446299595192238413

theorem tailTrace_1024932 : CollatzResearch.WordTrace tailWord_1024932 prefixEnd_1024932 233903446299595192238413 := by
  unfold tailWord_1024932
  simp only [CollatzResearch.WordTrace]
  refine ⟨18691170561426941647354525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24921560748569255529806033 18691170561426941647354525)
  ·
    refine ⟨7009188960535103117757947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18691170561426941647354525 7009188960535103117757947)
    ·
      refine ⟨10513783440802654676636921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7009188960535103117757947 10513783440802654676636921)
      ·
        refine ⟨7885337580601991007477691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10513783440802654676636921 7885337580601991007477691)
        ·
          refine ⟨11828006370902986511216537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7885337580601991007477691 11828006370902986511216537)
          ·
            refine ⟨8871004778177239883412403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11828006370902986511216537 8871004778177239883412403)
            ·
              refine ⟨13306507167265859825118605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8871004778177239883412403 13306507167265859825118605)
              ·
                refine ⟨4989940187724697434419477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13306507167265859825118605 4989940187724697434419477)
                ·
                  refine ⟨233903446299595192238413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4989940187724697434419477 233903446299595192238413)
                  ·
                    rfl

theorem cell21_1024932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_1024932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1024932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1024932 prefixEnd_1024932 := by exact prefixLift 1024932
  have htrace : WordTrace (prefixWord ++ tailWord_1024932) baseStart_1024932 baseEnd_1024932 := by
    simpa [prefixWord, tailWord_1024932, baseEnd_1024932] using wordTrace_append hprefix tailTrace_1024932
  have hstable : (prefixWord ++ tailWord_1024932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024932).length < 2 ^ (prefixWord ++ tailWord_1024932).sum := by decide
  have hdescent : baseEnd_1024932 < baseStart_1024932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024941 : List Nat := [1, 5, 2, 3, 2, 1, 2, 1, 4]
def baseStart_1024941 : Nat := 118140960795 + 1024941 * 2 ^ 59
def prefixEnd_1024941 : Nat := 4983230072969 + 3 ^ 40 * 1024941 * 2
def baseEnd_1024941 : Nat := 233905500222213176588395

theorem tailTrace_1024941 : CollatzResearch.WordTrace tailWord_1024941 prefixEnd_1024941 233905500222213176588395 := by
  unfold tailWord_1024941
  simp only [CollatzResearch.WordTrace]
  refine ⟨37382669379821277831786677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24921779586547518554524451 37382669379821277831786677)
  ·
    refine ⟨3504625254358244796730001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37382669379821277831786677 3504625254358244796730001)
    ·
      refine ⟨2628468940768683597547501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3504625254358244796730001 2628468940768683597547501)
      ·
        refine ⟨985675852788256349080313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2628468940768683597547501 985675852788256349080313)
        ·
          refine ⟨739256889591192261810235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 985675852788256349080313 739256889591192261810235)
          ·
            refine ⟨1108885334386788392715353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 739256889591192261810235 1108885334386788392715353)
            ·
              refine ⟨831664000790091294536515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1108885334386788392715353 831664000790091294536515)
              ·
                refine ⟨1247496001185136941804773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 831664000790091294536515 1247496001185136941804773)
                ·
                  refine ⟨233905500222213176588395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1247496001185136941804773 233905500222213176588395)
                  ·
                    rfl

theorem cell21_1024941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_1024941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1024941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1024941 prefixEnd_1024941 := by exact prefixLift 1024941
  have htrace : WordTrace (prefixWord ++ tailWord_1024941) baseStart_1024941 baseEnd_1024941 := by
    simpa [prefixWord, tailWord_1024941, baseEnd_1024941] using wordTrace_append hprefix tailTrace_1024941
  have hstable : (prefixWord ++ tailWord_1024941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024941).length < 2 ^ (prefixWord ++ tailWord_1024941).sum := by decide
  have hdescent : baseEnd_1024941 < baseStart_1024941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024949 : List Nat := [1, 3, 3, 2, 1, 1, 3, 3, 4]
def baseStart_1024949 : Nat := 118140960795 + 1024949 * 2 ^ 59
def prefixEnd_1024949 : Nat := 4983230072969 + 3 ^ 40 * 1024949 * 2
def baseEnd_1024949 : Nat := 233907325931206940455045

theorem tailTrace_1024949 : CollatzResearch.WordTrace tailWord_1024949 prefixEnd_1024949 233907325931206940455045 := by
  unfold tailWord_1024949
  simp only [CollatzResearch.WordTrace]
  refine ⟨37382961163792295198077901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24921974109194863465385267 37382961163792295198077901)
  ·
    refine ⟨14018610436422110699279213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37382961163792295198077901 14018610436422110699279213)
    ·
      refine ⟨5256978913658291512229705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14018610436422110699279213 5256978913658291512229705)
      ·
        refine ⟨3942734185243718634172279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5256978913658291512229705 3942734185243718634172279)
        ·
          refine ⟨5914101277865577951258419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3942734185243718634172279 5914101277865577951258419)
          ·
            refine ⟨8871151916798366926887629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5914101277865577951258419 8871151916798366926887629)
            ·
              refine ⟨3326681968799387597582861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8871151916798366926887629 3326681968799387597582861)
              ·
                refine ⟨1247505738299770349093573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3326681968799387597582861 1247505738299770349093573)
                ·
                  refine ⟨233907325931206940455045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1247505738299770349093573 233907325931206940455045)
                  ·
                    rfl

theorem cell21_1024949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_1024949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1024949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1024949 prefixEnd_1024949 := by exact prefixLift 1024949
  have htrace : WordTrace (prefixWord ++ tailWord_1024949) baseStart_1024949 baseEnd_1024949 := by
    simpa [prefixWord, tailWord_1024949, baseEnd_1024949] using wordTrace_append hprefix tailTrace_1024949
  have hstable : (prefixWord ++ tailWord_1024949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024949).length < 2 ^ (prefixWord ++ tailWord_1024949).sum := by decide
  have hdescent : baseEnd_1024949 < baseStart_1024949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024997 : List Nat := [1, 3, 1, 6, 1, 2, 1, 6]
def baseStart_1024997 : Nat := 118140960795 + 1024997 * 2 ^ 59
def prefixEnd_1024997 : Nat := 4983230072969 + 3 ^ 40 * 1024997 * 2
def baseEnd_1024997 : Nat := 77972760061723174551649

theorem tailTrace_1024997 : CollatzResearch.WordTrace tailWord_1024997 prefixEnd_1024997 77972760061723174551649 := by
  unfold tailWord_1024997
  simp only [CollatzResearch.WordTrace]
  refine ⟨37384711867618399395825245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24923141245078932930550163 37384711867618399395825245)
  ·
    refine ⟨14019266950356899773434467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37384711867618399395825245 14019266950356899773434467)
    ·
      refine ⟨21028900425535349660151701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14019266950356899773434467 21028900425535349660151701)
      ·
        refine ⟨985729707446969515319611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 21028900425535349660151701 985729707446969515319611)
        ·
          refine ⟨1478594561170454272979417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985729707446969515319611 1478594561170454272979417)
          ·
            refine ⟨1108945920877840704734563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1478594561170454272979417 1108945920877840704734563)
            ·
              refine ⟨1663418881316761057101845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1108945920877840704734563 1663418881316761057101845)
              ·
                refine ⟨77972760061723174551649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1663418881316761057101845 77972760061723174551649)
                ·
                  rfl

theorem cell21_1024997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 6].length) (baseStart_1024997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1024997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1024997 prefixEnd_1024997 := by exact prefixLift 1024997
  have htrace : WordTrace (prefixWord ++ tailWord_1024997) baseStart_1024997 baseEnd_1024997 := by
    simpa [prefixWord, tailWord_1024997, baseEnd_1024997] using wordTrace_append hprefix tailTrace_1024997
  have hstable : (prefixWord ++ tailWord_1024997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024997).length < 2 ^ (prefixWord ++ tailWord_1024997).sum := by decide
  have hdescent : baseEnd_1024997 < baseStart_1024997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025070 : List Nat := [4, 1, 3, 1, 1, 1, 1, 4, 5]
def baseStart_1025070 : Nat := 118140960795 + 1025070 * 2 ^ 59
def prefixEnd_1025070 : Nat := 4983230072969 + 3 ^ 40 * 1025070 * 2
def baseEnd_1025070 : Nat := 233934939779737618938131

theorem tailTrace_1025070 : CollatzResearch.WordTrace tailWord_1025070 prefixEnd_1025070 233934939779737618938131 := by
  unfold tailWord_1025070
  simp only [CollatzResearch.WordTrace]
  refine ⟨4673421799544241607904083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24924916264235955242155109 4673421799544241607904083)
  ·
    refine ⟨7010132699316362411856125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4673421799544241607904083 7010132699316362411856125)
    ·
      refine ⟨2628799762243635904446047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7010132699316362411856125 2628799762243635904446047)
      ·
        refine ⟨3943199643365453856669071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2628799762243635904446047 3943199643365453856669071)
        ·
          refine ⟨5914799465048180785003607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3943199643365453856669071 5914799465048180785003607)
          ·
            refine ⟨8872199197572271177505411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5914799465048180785003607 8872199197572271177505411)
            ·
              refine ⟨13308298796358406766258117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8872199197572271177505411 13308298796358406766258117)
              ·
                refine ⟨2495306024317201268673397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13308298796358406766258117 2495306024317201268673397)
                ·
                  refine ⟨233934939779737618938131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2495306024317201268673397 233934939779737618938131)
                  ·
                    rfl

theorem cell21_1025070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_1025070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1025070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1025070 prefixEnd_1025070 := by exact prefixLift 1025070
  have htrace : WordTrace (prefixWord ++ tailWord_1025070) baseStart_1025070 baseEnd_1025070 := by
    simpa [prefixWord, tailWord_1025070, baseEnd_1025070] using wordTrace_append hprefix tailTrace_1025070
  have hstable : (prefixWord ++ tailWord_1025070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025070).length < 2 ^ (prefixWord ++ tailWord_1025070).sum := by decide
  have hdescent : baseEnd_1025070 < baseStart_1025070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025084 : List Nat := [2, 2, 2, 2, 2, 2, 1, 2, 6]
def baseStart_1025084 : Nat := 118140960795 + 1025084 * 2 ^ 59
def prefixEnd_1025084 : Nat := 4983230072969 + 3 ^ 40 * 1025084 * 2
def baseEnd_1025084 : Nat := 233938134770476705704769

theorem tailTrace_1025084 : CollatzResearch.WordTrace tailWord_1025084 prefixEnd_1025084 233938134770476705704769 := by
  unfold tailWord_1025084
  simp only [CollatzResearch.WordTrace]
  refine ⟨18693942509151606627121153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24925256678868808836161537 18693942509151606627121153)
  ·
    refine ⟨14020456881863704970340865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18693942509151606627121153 14020456881863704970340865)
    ·
      refine ⟨10515342661397778727755649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14020456881863704970340865 10515342661397778727755649)
      ·
        refine ⟨7886506996048334045816737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10515342661397778727755649 7886506996048334045816737)
        ·
          refine ⟨5914880247036250534362553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7886506996048334045816737 5914880247036250534362553)
          ·
            refine ⟨4436160185277187900771915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5914880247036250534362553 4436160185277187900771915)
            ·
              refine ⟨6654240277915781851157873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4436160185277187900771915 6654240277915781851157873)
              ·
                refine ⟨4990680208436836388368405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6654240277915781851157873 4990680208436836388368405)
                ·
                  refine ⟨233938134770476705704769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4990680208436836388368405 233938134770476705704769)
                  ·
                    rfl

theorem cell21_1025084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_1025084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1025084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1025084 prefixEnd_1025084 := by exact prefixLift 1025084
  have htrace : WordTrace (prefixWord ++ tailWord_1025084) baseStart_1025084 baseEnd_1025084 := by
    simpa [prefixWord, tailWord_1025084, baseEnd_1025084] using wordTrace_append hprefix tailTrace_1025084
  have hstable : (prefixWord ++ tailWord_1025084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025084).length < 2 ^ (prefixWord ++ tailWord_1025084).sum := by decide
  have hdescent : baseEnd_1025084 < baseStart_1025084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025098 : List Nat := [3, 1, 2, 1, 1, 2, 11]
def baseStart_1025098 : Nat := 118140960795 + 1025098 * 2 ^ 59
def prefixEnd_1025098 : Nat := 4983230072969 + 3 ^ 40 * 1025098 * 2
def baseEnd_1025098 : Nat := 25993481084579532496823

theorem tailTrace_1025098 : CollatzResearch.WordTrace tailWord_1025098 prefixEnd_1025098 25993481084579532496823 := by
  unfold tailWord_1025098
  simp only [CollatzResearch.WordTrace]
  refine ⟨9347098910063123411312987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24925597093501662430167965 9347098910063123411312987)
  ·
    refine ⟨14020648365094685116969481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9347098910063123411312987 14020648365094685116969481)
    ·
      refine ⟨10515486273821013837727111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14020648365094685116969481 10515486273821013837727111)
      ·
        refine ⟨15773229410731520756590667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10515486273821013837727111 15773229410731520756590667)
        ·
          refine ⟨23659844116097281134886001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15773229410731520756590667 23659844116097281134886001)
          ·
            refine ⟨17744883087072960851164501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23659844116097281134886001 17744883087072960851164501)
            ·
              refine ⟨25993481084579532496823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 17744883087072960851164501 25993481084579532496823)
              ·
                rfl

theorem cell21_1025098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 11].length) (baseStart_1025098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1025098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1025098 prefixEnd_1025098 := by exact prefixLift 1025098
  have htrace : WordTrace (prefixWord ++ tailWord_1025098) baseStart_1025098 baseEnd_1025098 := by
    simpa [prefixWord, tailWord_1025098, baseEnd_1025098] using wordTrace_append hprefix tailTrace_1025098
  have hstable : (prefixWord ++ tailWord_1025098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025098).length < 2 ^ (prefixWord ++ tailWord_1025098).sum := by decide
  have hdescent : baseEnd_1025098 < baseStart_1025098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025101 : List Nat := [1, 6, 1, 1, 1, 2, 2, 1, 6]
def baseStart_1025101 : Nat := 118140960795 + 1025101 * 2 ^ 59
def prefixEnd_1025101 : Nat := 4983230072969 + 3 ^ 40 * 1025101 * 2
def baseEnd_1025101 : Nat := 233942014402088453921401

theorem tailTrace_1025101 : CollatzResearch.WordTrace tailWord_1025101 prefixEnd_1025101 233942014402088453921401 := by
  unfold tailWord_1025101
  simp only [CollatzResearch.WordTrace]
  refine ⟨37388505059241625157611157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24925670039494416771740771 37388505059241625157611157)
  ·
    refine ⟨1752586174651951179263023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37388505059241625157611157 1752586174651951179263023)
    ·
      refine ⟨2628879261977926768894535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1752586174651951179263023 2628879261977926768894535)
      ·
        refine ⟨3943318892966890153341803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2628879261977926768894535 3943318892966890153341803)
        ·
          refine ⟨5914978339450335230012705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3943318892966890153341803 5914978339450335230012705)
          ·
            refine ⟨4436233754587751422509529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5914978339450335230012705 4436233754587751422509529)
            ·
              refine ⟨3327175315940813566882147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4436233754587751422509529 3327175315940813566882147)
              ·
                refine ⟨4990762973911220350323221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3327175315940813566882147 4990762973911220350323221)
                ·
                  refine ⟨233942014402088453921401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4990762973911220350323221 233942014402088453921401)
                  ·
                    rfl

theorem cell21_1025101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_1025101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1025101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1025101 prefixEnd_1025101 := by exact prefixLift 1025101
  have htrace : WordTrace (prefixWord ++ tailWord_1025101) baseStart_1025101 baseEnd_1025101 := by
    simpa [prefixWord, tailWord_1025101, baseEnd_1025101] using wordTrace_append hprefix tailTrace_1025101
  have hstable : (prefixWord ++ tailWord_1025101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025101).length < 2 ^ (prefixWord ++ tailWord_1025101).sum := by decide
  have hdescent : baseEnd_1025101 < baseStart_1025101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025326 : List Nat := [4, 1, 3, 13]
def baseStart_1025326 : Nat := 118140960795 + 1025326 * 2 ^ 59
def prefixEnd_1025326 : Nat := 4983230072969 + 3 ^ 40 * 1025326 * 2
def baseEnd_1025326 : Nat := 962935648014559928687

theorem tailTrace_1025326 : CollatzResearch.WordTrace tailWord_1025326 prefixEnd_1025326 962935648014559928687 := by
  unfold tailWord_1025326
  simp only [CollatzResearch.WordTrace]
  refine ⟨4674588935428311073068979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24931140988950992389701221 4674588935428311073068979)
  ·
    refine ⟨7011883403142466609603469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4674588935428311073068979 7011883403142466609603469)
    ·
      refine ⟨2629456276178424978601301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7011883403142466609603469 2629456276178424978601301)
      ·
        refine ⟨962935648014559928687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 2629456276178424978601301 962935648014559928687)
        ·
          rfl

theorem cell21_1025326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 13].length) (baseStart_1025326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1025326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1025326 prefixEnd_1025326 := by exact prefixLift 1025326
  have htrace : WordTrace (prefixWord ++ tailWord_1025326) baseStart_1025326 baseEnd_1025326 := by
    simpa [prefixWord, tailWord_1025326, baseEnd_1025326] using wordTrace_append hprefix tailTrace_1025326
  have hstable : (prefixWord ++ tailWord_1025326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025326).length < 2 ^ (prefixWord ++ tailWord_1025326).sum := by decide
  have hdescent : baseEnd_1025326 < baseStart_1025326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025329 : List Nat := [1, 2, 2, 3, 3, 2, 2, 2, 4]
def baseStart_1025329 : Nat := 118140960795 + 1025329 * 2 ^ 59
def prefixEnd_1025329 : Nat := 4983230072969 + 3 ^ 40 * 1025329 * 2
def baseEnd_1025329 : Nat := 233994047108410724120935

theorem tailTrace_1025329 : CollatzResearch.WordTrace tailWord_1025329 prefixEnd_1025329 233994047108410724120935 := by
  unfold tailWord_1025329
  simp only [CollatzResearch.WordTrace]
  refine ⟨37396820902415620096911041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24931213934943746731274027 37396820902415620096911041)
  ·
    refine ⟨28047615676811715072683281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37396820902415620096911041 28047615676811715072683281)
    ·
      refine ⟨21035711757608786304512461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28047615676811715072683281 21035711757608786304512461)
      ·
        refine ⟨7888391909103294864192173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21035711757608786304512461 7888391909103294864192173)
        ·
          refine ⟨2958146965913735574072065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7888391909103294864192173 2958146965913735574072065)
          ·
            refine ⟨2218610224435301680554049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2958146965913735574072065 2218610224435301680554049)
            ·
              refine ⟨1663957668326476260415537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2218610224435301680554049 1663957668326476260415537)
              ·
                refine ⟨1247968251244857195311653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1663957668326476260415537 1247968251244857195311653)
                ·
                  refine ⟨233994047108410724120935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1247968251244857195311653 233994047108410724120935)
                  ·
                    rfl

theorem cell21_1025329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 4].length) (baseStart_1025329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1025329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1025329 prefixEnd_1025329 := by exact prefixLift 1025329
  have htrace : WordTrace (prefixWord ++ tailWord_1025329) baseStart_1025329 baseEnd_1025329 := by
    simpa [prefixWord, tailWord_1025329, baseEnd_1025329] using wordTrace_append hprefix tailTrace_1025329
  have hstable : (prefixWord ++ tailWord_1025329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025329).length < 2 ^ (prefixWord ++ tailWord_1025329).sum := by decide
  have hdescent : baseEnd_1025329 < baseStart_1025329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025343 : List Nat := [1, 1, 2, 2, 4, 4, 1, 6]
def baseStart_1025343 : Nat := 118140960795 + 1025343 * 2 ^ 59
def prefixEnd_1025343 : Nat := 4983230072969 + 3 ^ 40 * 1025343 * 2
def baseEnd_1025343 : Nat := 77999080699716603629191

theorem tailTrace_1025343 : CollatzResearch.WordTrace tailWord_1025343 prefixEnd_1025343 77999080699716603629191 := by
  unfold tailWord_1025343
  simp only [CollatzResearch.WordTrace]
  refine ⟨37397331524364900487920683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24931554349576600325280455 37397331524364900487920683)
  ·
    refine ⟨56095997286547350731881025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37397331524364900487920683 56095997286547350731881025)
    ·
      refine ⟨42071997964910513048910769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56095997286547350731881025 42071997964910513048910769)
      ·
        refine ⟨31553998473682884786683077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42071997964910513048910769 31553998473682884786683077)
        ·
          refine ⟨5916374713815540897503077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31553998473682884786683077 5916374713815540897503077)
          ·
            refine ⟨1109320258840413918281827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5916374713815540897503077 1109320258840413918281827)
            ·
              refine ⟨1663980388260620877422741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1109320258840413918281827 1663980388260620877422741)
              ·
                refine ⟨77999080699716603629191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1663980388260620877422741 77999080699716603629191)
                ·
                  rfl

theorem cell21_1025343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 6].length) (baseStart_1025343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1025343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1025343 prefixEnd_1025343 := by exact prefixLift 1025343
  have htrace : WordTrace (prefixWord ++ tailWord_1025343) baseStart_1025343 baseEnd_1025343 := by
    simpa [prefixWord, tailWord_1025343, baseEnd_1025343] using wordTrace_append hprefix tailTrace_1025343
  have hstable : (prefixWord ++ tailWord_1025343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025343).length < 2 ^ (prefixWord ++ tailWord_1025343).sum := by decide
  have hdescent : baseEnd_1025343 < baseStart_1025343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025388 : List Nat := [2, 2, 1, 1, 5, 2, 1, 1, 6]
def baseStart_1025388 : Nat := 118140960795 + 1025388 * 2 ^ 59
def prefixEnd_1025388 : Nat := 4983230072969 + 3 ^ 40 * 1025388 * 2
def baseEnd_1025388 : Nat := 234007511712239732637481

theorem tailTrace_1025388 : CollatzResearch.WordTrace tailWord_1025388 prefixEnd_1025388 234007511712239732637481 := by
  unfold tailWord_1025388
  simp only [CollatzResearch.WordTrace]
  refine ⟨18699486404600936586654409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24932648539467915448872545 18699486404600936586654409)
  ·
    refine ⟨14024614803450702439990807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18699486404600936586654409 14024614803450702439990807)
    ·
      refine ⟨21036922205176053659986211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14024614803450702439990807 21036922205176053659986211)
      ·
        refine ⟨31555383307764080489979317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21036922205176053659986211 31555383307764080489979317)
        ·
          refine ⟨2958317185102882545935561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31555383307764080489979317 2958317185102882545935561)
          ·
            refine ⟨2218737888827161909451671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2958317185102882545935561 2218737888827161909451671)
            ·
              refine ⟨3328106833240742864177507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2218737888827161909451671 3328106833240742864177507)
              ·
                refine ⟨4992160249861114296266261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3328106833240742864177507 4992160249861114296266261)
                ·
                  refine ⟨234007511712239732637481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4992160249861114296266261 234007511712239732637481)
                  ·
                    rfl

theorem cell21_1025388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_1025388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1025388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1025388 prefixEnd_1025388 := by exact prefixLift 1025388
  have htrace : WordTrace (prefixWord ++ tailWord_1025388) baseStart_1025388 baseEnd_1025388 := by
    simpa [prefixWord, tailWord_1025388, baseEnd_1025388] using wordTrace_append hprefix tailTrace_1025388
  have hstable : (prefixWord ++ tailWord_1025388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025388).length < 2 ^ (prefixWord ++ tailWord_1025388).sum := by decide
  have hdescent : baseEnd_1025388 < baseStart_1025388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025405 : List Nat := [1, 4, 1, 1, 2, 2, 5, 1, 4]
def baseStart_1025405 : Nat := 118140960795 + 1025405 * 2 ^ 59
def prefixEnd_1025405 : Nat := 4983230072969 + 3 ^ 40 * 1025405 * 2
def baseEnd_1025405 : Nat := 234011391343851480854113

theorem tailTrace_1025405 : CollatzResearch.WordTrace tailWord_1025405 prefixEnd_1025405 234011391343851480854113 := by
  unfold tailWord_1025405
  simp only [CollatzResearch.WordTrace]
  refine ⟨37399592850140285076677669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24933061900093523384451779 37399592850140285076677669)
  ·
    refine ⟨7012423659401303451877063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37399592850140285076677669 7012423659401303451877063)
    ·
      refine ⟨10518635489101955177815595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7012423659401303451877063 10518635489101955177815595)
      ·
        refine ⟨15777953233652932766723393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10518635489101955177815595 15777953233652932766723393)
        ·
          refine ⟨11833464925239699575042545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15777953233652932766723393 11833464925239699575042545)
          ·
            refine ⟨8875098693929774681281909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11833464925239699575042545 8875098693929774681281909)
            ·
              refine ⟨832040502555916376370179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8875098693929774681281909 832040502555916376370179)
              ·
                refine ⟨1248060753833874564555269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 832040502555916376370179 1248060753833874564555269)
                ·
                  refine ⟨234011391343851480854113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1248060753833874564555269 234011391343851480854113)
                  ·
                    rfl

theorem cell21_1025405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_1025405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1025405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1025405 prefixEnd_1025405 := by exact prefixLift 1025405
  have htrace : WordTrace (prefixWord ++ tailWord_1025405) baseStart_1025405 baseEnd_1025405 := by
    simpa [prefixWord, tailWord_1025405, baseEnd_1025405] using wordTrace_append hprefix tailTrace_1025405
  have hstable : (prefixWord ++ tailWord_1025405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025405).length < 2 ^ (prefixWord ++ tailWord_1025405).sum := by decide
  have hdescent : baseEnd_1025405 < baseStart_1025405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025436 : List Nat := [2, 2, 3, 4, 1, 2, 7]
def baseStart_1025436 : Nat := 118140960795 + 1025436 * 2 ^ 59
def prefixEnd_1025436 : Nat := 4983230072969 + 3 ^ 40 * 1025436 * 2
def baseEnd_1025436 : Nat := 26002051774022479537487

theorem tailTrace_1025436 : CollatzResearch.WordTrace tailWord_1025436 prefixEnd_1025436 26002051774022479537487 := by
  unfold tailWord_1025436
  simp only [CollatzResearch.WordTrace]
  refine ⟨18700361756513988685528081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24933815675351984914037441 18700361756513988685528081)
  ·
    refine ⟨14025271317385491514146061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18700361756513988685528081 14025271317385491514146061)
    ·
      refine ⟨5259476744019559317804773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14025271317385491514146061 5259476744019559317804773)
      ·
        refine ⟨986151889503667372088395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5259476744019559317804773 986151889503667372088395)
        ·
          refine ⟨1479227834255501058132593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 986151889503667372088395 1479227834255501058132593)
          ·
            refine ⟨1109420875691625793599445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1479227834255501058132593 1109420875691625793599445)
            ·
              refine ⟨26002051774022479537487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1109420875691625793599445 26002051774022479537487)
              ·
                rfl

theorem cell21_1025436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 7].length) (baseStart_1025436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1025436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1025436 prefixEnd_1025436 := by exact prefixLift 1025436
  have htrace : WordTrace (prefixWord ++ tailWord_1025436) baseStart_1025436 baseEnd_1025436 := by
    simpa [prefixWord, tailWord_1025436, baseEnd_1025436] using wordTrace_append hprefix tailTrace_1025436
  have hstable : (prefixWord ++ tailWord_1025436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025436).length < 2 ^ (prefixWord ++ tailWord_1025436).sum := by decide
  have hdescent : baseEnd_1025436 < baseStart_1025436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025526 : List Nat := [5, 1, 1, 1, 2, 3, 1, 2, 5]
def baseStart_1025526 : Nat := 118140960795 + 1025526 * 2 ^ 59
def prefixEnd_1025526 : Nat := 4983230072969 + 3 ^ 40 * 1025526 * 2
def baseEnd_1025526 : Nat := 234039005192382159337199

theorem tailTrace_1025526 : CollatzResearch.WordTrace tailWord_1025526 prefixEnd_1025526 234039005192382159337199 := by
  unfold tailWord_1025526
  simp only [CollatzResearch.WordTrace]
  refine ⟨2337750380168870171364527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24936004055134615161221621 2337750380168870171364527)
  ·
    refine ⟨3506625570253305257046791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2337750380168870171364527 3506625570253305257046791)
    ·
      refine ⟨5259938355379957885570187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3506625570253305257046791 5259938355379957885570187)
      ·
        refine ⟨7889907533069936828355281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5259938355379957885570187 7889907533069936828355281)
        ·
          refine ⟨5917430649802452621266461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7889907533069936828355281 5917430649802452621266461)
          ·
            refine ⟨2219036493675919732974923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5917430649802452621266461 2219036493675919732974923)
            ·
              refine ⟨3328554740513879599462385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2219036493675919732974923 3328554740513879599462385)
              ·
                refine ⟨2496416055385409699596789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3328554740513879599462385 2496416055385409699596789)
                ·
                  refine ⟨234039005192382159337199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2496416055385409699596789 234039005192382159337199)
                  ·
                    rfl

theorem cell21_1025526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_1025526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1025526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1025526 prefixEnd_1025526 := by exact prefixLift 1025526
  have htrace : WordTrace (prefixWord ++ tailWord_1025526) baseStart_1025526 baseEnd_1025526 := by
    simpa [prefixWord, tailWord_1025526, baseEnd_1025526] using wordTrace_append hprefix tailTrace_1025526
  have hstable : (prefixWord ++ tailWord_1025526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025526).length < 2 ^ (prefixWord ++ tailWord_1025526).sum := by decide
  have hdescent : baseEnd_1025526 < baseStart_1025526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025543 : List Nat := [1, 1, 4, 3, 2, 2, 2, 3, 3]
def baseStart_1025543 : Nat := 118140960795 + 1025543 * 2 ^ 59
def prefixEnd_1025543 : Nat := 4983230072969 + 3 ^ 40 * 1025543 * 2
def baseEnd_1025543 : Nat := 234042884823993907553831

theorem tailTrace_1025543 : CollatzResearch.WordTrace tailWord_1025543 prefixEnd_1025543 234042884823993907553831 := by
  unfold tailWord_1025543
  simp only [CollatzResearch.WordTrace]
  refine ⟨37404626123640334645201283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24936417415760223096800855 37404626123640334645201283)
  ·
    refine ⟨56106939185460501967801925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37404626123640334645201283 56106939185460501967801925)
    ·
      refine ⟨10520051097273844118962861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56106939185460501967801925 10520051097273844118962861)
      ·
        refine ⟨3945019161477691544611073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10520051097273844118962861 3945019161477691544611073)
        ·
          refine ⟨2958764371108268658458305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3945019161477691544611073 2958764371108268658458305)
          ·
            refine ⟨2219073278331201493843729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2958764371108268658458305 2219073278331201493843729)
            ·
              refine ⟨1664304958748401120382797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2219073278331201493843729 1664304958748401120382797)
              ·
                refine ⟨624114359530650420143549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1664304958748401120382797 624114359530650420143549)
                ·
                  refine ⟨234042884823993907553831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 624114359530650420143549 234042884823993907553831)
                  ·
                    rfl

theorem cell21_1025543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 3, 3].length) (baseStart_1025543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1025543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1025543 prefixEnd_1025543 := by exact prefixLift 1025543
  have htrace : WordTrace (prefixWord ++ tailWord_1025543) baseStart_1025543 baseEnd_1025543 := by
    simpa [prefixWord, tailWord_1025543, baseEnd_1025543] using wordTrace_append hprefix tailTrace_1025543
  have hstable : (prefixWord ++ tailWord_1025543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025543).length < 2 ^ (prefixWord ++ tailWord_1025543).sum := by decide
  have hdescent : baseEnd_1025543 < baseStart_1025543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025557 : List Nat := [1, 3, 2, 1, 3, 4, 1, 2, 4]
def baseStart_1025557 : Nat := 118140960795 + 1025557 * 2 ^ 59
def prefixEnd_1025557 : Nat := 4983230072969 + 3 ^ 40 * 1025557 * 2
def baseEnd_1025557 : Nat := 234046079814732994320469

theorem tailTrace_1025557 : CollatzResearch.WordTrace tailWord_1025557 prefixEnd_1025557 234046079814732994320469 := by
  unfold tailWord_1025557
  simp only [CollatzResearch.WordTrace]
  refine ⟨37405136745589615036210925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24936757830393076690807283 37405136745589615036210925)
  ·
    refine ⟨14026926279596105638579097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37405136745589615036210925 14026926279596105638579097)
    ·
      refine ⟨10520194709697079228934323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14026926279596105638579097 10520194709697079228934323)
      ·
        refine ⟨15780292064545618843401485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10520194709697079228934323 15780292064545618843401485)
        ·
          refine ⟨5917609524204607066275557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15780292064545618843401485 5917609524204607066275557)
          ·
            refine ⟨1109551785788363824926667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5917609524204607066275557 1109551785788363824926667)
            ·
              refine ⟨1664327678682545737390001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1109551785788363824926667 1664327678682545737390001)
              ·
                refine ⟨1248245759011909303042501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1664327678682545737390001 1248245759011909303042501)
                ·
                  refine ⟨234046079814732994320469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1248245759011909303042501 234046079814732994320469)
                  ·
                    rfl

theorem cell21_1025557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_1025557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1025557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1025557 prefixEnd_1025557 := by exact prefixLift 1025557
  have htrace : WordTrace (prefixWord ++ tailWord_1025557) baseStart_1025557 baseEnd_1025557 := by
    simpa [prefixWord, tailWord_1025557, baseEnd_1025557] using wordTrace_append hprefix tailTrace_1025557
  have hstable : (prefixWord ++ tailWord_1025557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025557).length < 2 ^ (prefixWord ++ tailWord_1025557).sum := by decide
  have hdescent : baseEnd_1025557 < baseStart_1025557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025599 : List Nat := [1, 1, 2, 2, 3, 3, 1, 2, 6]
def baseStart_1025599 : Nat := 118140960795 + 1025599 * 2 ^ 59
def prefixEnd_1025599 : Nat := 4983230072969 + 3 ^ 40 * 1025599 * 2
def baseEnd_1025599 : Nat := 234055664786950254620383

theorem tailTrace_1025599 : CollatzResearch.WordTrace tailWord_1025599 prefixEnd_1025599 234055664786950254620383 := by
  unfold tailWord_1025599
  simp only [CollatzResearch.WordTrace]
  refine ⟨37406668611437456209239851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24937779074291637472826567 37406668611437456209239851)
  ·
    refine ⟨56110002917156184313859777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37406668611437456209239851 56110002917156184313859777)
    ·
      refine ⟨42082502187867138235394833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56110002917156184313859777 42082502187867138235394833)
      ·
        refine ⟨31561876640900353676546125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42082502187867138235394833 31561876640900353676546125)
        ·
          refine ⟨11835703740337632628704797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31561876640900353676546125 11835703740337632628704797)
          ·
            refine ⟨4438388902626612235764299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11835703740337632628704797 4438388902626612235764299)
            ·
              refine ⟨6657583353939918353646449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4438388902626612235764299 6657583353939918353646449)
              ·
                refine ⟨4993187515454938765234837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6657583353939918353646449 4993187515454938765234837)
                ·
                  refine ⟨234055664786950254620383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4993187515454938765234837 234055664786950254620383)
                  ·
                    rfl

theorem cell21_1025599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 6].length) (baseStart_1025599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1025599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1025599 prefixEnd_1025599 := by exact prefixLift 1025599
  have htrace : WordTrace (prefixWord ++ tailWord_1025599) baseStart_1025599 baseEnd_1025599 := by
    simpa [prefixWord, tailWord_1025599, baseEnd_1025599] using wordTrace_append hprefix tailTrace_1025599
  have hstable : (prefixWord ++ tailWord_1025599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025599).length < 2 ^ (prefixWord ++ tailWord_1025599).sum := by decide
  have hdescent : baseEnd_1025599 < baseStart_1025599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025644 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 7]
def baseStart_1025644 : Nat := 118140960795 + 1025644 * 2 ^ 59
def prefixEnd_1025644 : Nat := 4983230072969 + 3 ^ 40 * 1025644 * 2
def baseEnd_1025644 : Nat := 234065934400040176370291

theorem tailTrace_1025644 : CollatzResearch.WordTrace tailWord_1025644 prefixEnd_1025644 234065934400040176370291 := by
  unfold tailWord_1025644
  simp only [CollatzResearch.WordTrace]
  refine ⟨18704154948137214447313993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24938873264182952596418657 18704154948137214447313993)
  ·
    refine ⟨14028116211102910835485495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18704154948137214447313993 14028116211102910835485495)
    ·
      refine ⟨21042174316654366253228243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14028116211102910835485495 21042174316654366253228243)
      ·
        refine ⟨31563261474981549379842365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21042174316654366253228243 31563261474981549379842365)
        ·
          refine ⟨11836223053118081017440887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31563261474981549379842365 11836223053118081017440887)
          ·
            refine ⟨17754334579677121526161331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11836223053118081017440887 17754334579677121526161331)
            ·
              refine ⟨26631501869515682289241997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17754334579677121526161331 26631501869515682289241997)
              ·
                refine ⟨9986813201068380858465749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26631501869515682289241997 9986813201068380858465749)
                ·
                  refine ⟨234065934400040176370291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9986813201068380858465749 234065934400040176370291)
                  ·
                    rfl

theorem cell21_1025644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_1025644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1025644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1025644 prefixEnd_1025644 := by exact prefixLift 1025644
  have htrace : WordTrace (prefixWord ++ tailWord_1025644) baseStart_1025644 baseEnd_1025644 := by
    simpa [prefixWord, tailWord_1025644, baseEnd_1025644] using wordTrace_append hprefix tailTrace_1025644
  have hstable : (prefixWord ++ tailWord_1025644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025644).length < 2 ^ (prefixWord ++ tailWord_1025644).sum := by decide
  have hdescent : baseEnd_1025644 < baseStart_1025644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025689 : List Nat := [1, 2, 1, 2, 1, 2, 2, 10]
def baseStart_1025689 : Nat := 118140960795 + 1025689 * 2 ^ 59
def prefixEnd_1025689 : Nat := 4983230072969 + 3 ^ 40 * 1025689 * 2
def baseEnd_1025689 : Nat := 78025401337710032706733

theorem tailTrace_1025689 : CollatzResearch.WordTrace tailWord_1025689 prefixEnd_1025689 78025401337710032706733 := by
  unfold tailWord_1025689
  simp only [CollatzResearch.WordTrace]
  refine ⟨37409951181111401580016121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24939967454074267720010747 37409951181111401580016121)
  ·
    refine ⟨28057463385833551185012091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37409951181111401580016121 28057463385833551185012091)
    ·
      refine ⟨42086195078750326777518137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28057463385833551185012091 42086195078750326777518137)
      ·
        refine ⟨31564646309062745083138603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42086195078750326777518137 31564646309062745083138603)
        ·
          refine ⟨47346969463594117624707905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31564646309062745083138603 47346969463594117624707905)
          ·
            refine ⟨35510227097695588218530929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47346969463594117624707905 35510227097695588218530929)
            ·
              refine ⟨26632670323271691163898197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35510227097695588218530929 26632670323271691163898197)
              ·
                refine ⟨78025401337710032706733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26632670323271691163898197 78025401337710032706733)
                ·
                  rfl

theorem cell21_1025689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 10].length) (baseStart_1025689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1025689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1025689 prefixEnd_1025689 := by exact prefixLift 1025689
  have htrace : WordTrace (prefixWord ++ tailWord_1025689) baseStart_1025689 baseEnd_1025689 := by
    simpa [prefixWord, tailWord_1025689, baseEnd_1025689] using wordTrace_append hprefix tailTrace_1025689
  have hstable : (prefixWord ++ tailWord_1025689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025689).length < 2 ^ (prefixWord ++ tailWord_1025689).sum := by decide
  have hdescent : baseEnd_1025689 < baseStart_1025689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025757 : List Nat := [1, 4, 3, 3, 1, 2, 2, 5]
def baseStart_1025757 : Nat := 118140960795 + 1025757 * 2 ^ 59
def prefixEnd_1025757 : Nat := 4983230072969 + 3 ^ 40 * 1025757 * 2
def baseEnd_1025757 : Nat := 78030574179859030328909

theorem tailTrace_1025757 : CollatzResearch.WordTrace tailWord_1025757 prefixEnd_1025757 78030574179859030328909 := by
  unfold tailWord_1025757
  simp only [CollatzResearch.WordTrace]
  refine ⟨37412431344865049193491525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24941620896576699462327683 37412431344865049193491525)
  ·
    refine ⟨7014830877162196723779661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37412431344865049193491525 7014830877162196723779661)
    ·
      refine ⟨2630561578935823771417373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7014830877162196723779661 2630561578935823771417373)
      ·
        refine ⟨986460592100933914281515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2630561578935823771417373 986460592100933914281515)
        ·
          refine ⟨1479690888151400871422273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 986460592100933914281515 1479690888151400871422273)
          ·
            refine ⟨1109768166113550653566705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1479690888151400871422273 1109768166113550653566705)
            ·
              refine ⟨832326124585162990175029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1109768166113550653566705 832326124585162990175029)
              ·
                refine ⟨78030574179859030328909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 832326124585162990175029 78030574179859030328909)
                ·
                  rfl

theorem cell21_1025757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 5].length) (baseStart_1025757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1025757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1025757 prefixEnd_1025757 := by exact prefixLift 1025757
  have htrace : WordTrace (prefixWord ++ tailWord_1025757) baseStart_1025757 baseEnd_1025757 := by
    simpa [prefixWord, tailWord_1025757, baseEnd_1025757] using wordTrace_append hprefix tailTrace_1025757
  have hstable : (prefixWord ++ tailWord_1025757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025757).length < 2 ^ (prefixWord ++ tailWord_1025757).sum := by decide
  have hdescent : baseEnd_1025757 < baseStart_1025757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025782 : List Nat := [5, 1, 1, 1, 1, 3, 9]
def baseStart_1025782 : Nat := 118140960795 + 1025782 * 2 ^ 59
def prefixEnd_1025782 : Nat := 4983230072969 + 3 ^ 40 * 1025782 * 2
def baseEnd_1025782 : Nat := 26010825320020289230001

theorem tailTrace_1025782 : CollatzResearch.WordTrace tailWord_1025782 prefixEnd_1025782 26010825320020289230001 := by
  unfold tailWord_1025782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2338333948110904903946975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24942228779849652308767733 2338333948110904903946975)
  ·
    refine ⟨3507500922166357355920463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2338333948110904903946975 3507500922166357355920463)
    ·
      refine ⟨5261251383249536033880695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3507500922166357355920463 5261251383249536033880695)
      ·
        refine ⟨7891877074874304050821043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5261251383249536033880695 7891877074874304050821043)
        ·
          refine ⟨11837815612311456076231565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7891877074874304050821043 11837815612311456076231565)
          ·
            refine ⟨4439180854616796028586837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11837815612311456076231565 4439180854616796028586837)
            ·
              refine ⟨26010825320020289230001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4439180854616796028586837 26010825320020289230001)
              ·
                rfl

theorem cell21_1025782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 9].length) (baseStart_1025782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1025782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1025782 prefixEnd_1025782 := by exact prefixLift 1025782
  have htrace : WordTrace (prefixWord ++ tailWord_1025782) baseStart_1025782 baseEnd_1025782 := by
    simpa [prefixWord, tailWord_1025782, baseEnd_1025782] using wordTrace_append hprefix tailTrace_1025782
  have hstable : (prefixWord ++ tailWord_1025782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025782).length < 2 ^ (prefixWord ++ tailWord_1025782).sum := by decide
  have hdescent : baseEnd_1025782 < baseStart_1025782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025799 : List Nat := [1, 1, 4, 4, 2, 1, 2, 6]
def baseStart_1025799 : Nat := 118140960795 + 1025799 * 2 ^ 59
def prefixEnd_1025799 : Nat := 4983230072969 + 3 ^ 40 * 1025799 * 2
def baseEnd_1025799 : Nat := 78033769170598117095547

theorem tailTrace_1025799 : CollatzResearch.WordTrace tailWord_1025799 prefixEnd_1025799 78033769170598117095547 := by
  unfold tailWord_1025799
  simp only [CollatzResearch.WordTrace]
  refine ⟨37413963210712890366520451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24942642140475260244346967 37413963210712890366520451)
  ·
    refine ⟨56120944816069335549780677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37413963210712890366520451 56120944816069335549780677)
    ·
      refine ⟨10522677153013000415583877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56120944816069335549780677 10522677153013000415583877)
      ·
        refine ⟨1973001966189937577921977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10522677153013000415583877 1973001966189937577921977)
        ·
          refine ⟨1479751474642453183441483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1973001966189937577921977 1479751474642453183441483)
          ·
            refine ⟨2219627211963679775162225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1479751474642453183441483 2219627211963679775162225)
            ·
              refine ⟨1664720408972759831371669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2219627211963679775162225 1664720408972759831371669)
              ·
                refine ⟨78033769170598117095547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1664720408972759831371669 78033769170598117095547)
                ·
                  rfl

theorem cell21_1025799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 6].length) (baseStart_1025799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1025799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1025799 prefixEnd_1025799 := by exact prefixLift 1025799
  have htrace : WordTrace (prefixWord ++ tailWord_1025799) baseStart_1025799 baseEnd_1025799 := by
    simpa [prefixWord, tailWord_1025799, baseEnd_1025799] using wordTrace_append hprefix tailTrace_1025799
  have hstable : (prefixWord ++ tailWord_1025799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025799).length < 2 ^ (prefixWord ++ tailWord_1025799).sum := by decide
  have hdescent : baseEnd_1025799 < baseStart_1025799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025841 : List Nat := [1, 2, 2, 3, 2, 11]
def baseStart_1025841 : Nat := 118140960795 + 1025841 * 2 ^ 59
def prefixEnd_1025841 : Nat := 4983230072969 + 3 ^ 40 * 1025841 * 2
def baseEnd_1025841 : Nat := 8670773795704133762465

theorem tailTrace_1025841 : CollatzResearch.WordTrace tailWord_1025841 prefixEnd_1025841 8670773795704133762465 := by
  unfold tailWord_1025841
  simp only [CollatzResearch.WordTrace]
  refine ⟨37415495076560731539549377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24943663384373821026366251 37415495076560731539549377)
  ·
    refine ⟨28061621307420548654662033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37415495076560731539549377 28061621307420548654662033)
    ·
      refine ⟨21046215980565411490996525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28061621307420548654662033 21046215980565411490996525)
      ·
        refine ⟨7892330992712029309123697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21046215980565411490996525 7892330992712029309123697)
        ·
          refine ⟨5919248244534021981842773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7892330992712029309123697 5919248244534021981842773)
          ·
            refine ⟨8670773795704133762465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5919248244534021981842773 8670773795704133762465)
            ·
              rfl

theorem cell21_1025841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 11].length) (baseStart_1025841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1025841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1025841 prefixEnd_1025841 := by exact prefixLift 1025841
  have htrace : WordTrace (prefixWord ++ tailWord_1025841) baseStart_1025841 baseEnd_1025841 := by
    simpa [prefixWord, tailWord_1025841, baseEnd_1025841] using wordTrace_append hprefix tailTrace_1025841
  have hstable : (prefixWord ++ tailWord_1025841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025841).length < 2 ^ (prefixWord ++ tailWord_1025841).sum := by decide
  have hdescent : baseEnd_1025841 < baseStart_1025841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025917 : List Nat := [1, 4, 1, 1, 2, 1, 1, 10]
def baseStart_1025917 : Nat := 118140960795 + 1025917 * 2 ^ 59
def prefixEnd_1025917 : Nat := 4983230072969 + 3 ^ 40 * 1025917 * 2
def baseEnd_1025917 : Nat := 78042745573150789439911

theorem tailTrace_1025917 : CollatzResearch.WordTrace tailWord_1025917 prefixEnd_1025917 78042745573150789439911 := by
  unfold tailWord_1025917
  simp only [CollatzResearch.WordTrace]
  refine ⟨37418267024285396519316005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24945511349523597679544003 37418267024285396519316005)
  ·
    refine ⟨7015925067053511847371751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37418267024285396519316005 7015925067053511847371751)
    ·
      refine ⟨10523887600580267771057627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7015925067053511847371751 10523887600580267771057627)
      ·
        refine ⟨15785831400870401656586441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10523887600580267771057627 15785831400870401656586441)
        ·
          refine ⟨11839373550652801242439831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15785831400870401656586441 11839373550652801242439831)
          ·
            refine ⟨17759060325979201863659747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11839373550652801242439831 17759060325979201863659747)
            ·
              refine ⟨26638590488968802795489621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17759060325979201863659747 26638590488968802795489621)
              ·
                refine ⟨78042745573150789439911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26638590488968802795489621 78042745573150789439911)
                ·
                  rfl

theorem cell21_1025917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 10].length) (baseStart_1025917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1025917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1025917 prefixEnd_1025917 := by exact prefixLift 1025917
  have htrace : WordTrace (prefixWord ++ tailWord_1025917) baseStart_1025917 baseEnd_1025917 := by
    simpa [prefixWord, tailWord_1025917, baseEnd_1025917] using wordTrace_append hprefix tailTrace_1025917
  have hstable : (prefixWord ++ tailWord_1025917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025917).length < 2 ^ (prefixWord ++ tailWord_1025917).sum := by decide
  have hdescent : baseEnd_1025917 < baseStart_1025917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025920 : List Nat := [2, 1, 1, 2, 1, 2, 7, 1, 4]
def baseStart_1025920 : Nat := 118140960795 + 1025920 * 2 ^ 59
def prefixEnd_1025920 : Nat := 4983230072969 + 3 ^ 40 * 1025920 * 2
def baseEnd_1025920 : Nat := 234128921360325029769727

theorem tailTrace_1025920 : CollatzResearch.WordTrace tailWord_1025920 prefixEnd_1025920 234128921360325029769727 := by
  unfold tailWord_1025920
  simp only [CollatzResearch.WordTrace]
  refine ⟨18709188221637264015837607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24945584295516352021116809 18709188221637264015837607)
  ·
    refine ⟨28063782332455896023756411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18709188221637264015837607 28063782332455896023756411)
    ·
      refine ⟨42095673498683844035634617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28063782332455896023756411 42095673498683844035634617)
      ·
        refine ⟨31571755124012883026725963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42095673498683844035634617 31571755124012883026725963)
        ·
          refine ⟨47357632686019324540088945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31571755124012883026725963 47357632686019324540088945)
          ·
            refine ⟨35518224514514493405066709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47357632686019324540088945 35518224514514493405066709)
            ·
              refine ⟨832458387058933439181251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 35518224514514493405066709 832458387058933439181251)
              ·
                refine ⟨1248687580588400158771877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 832458387058933439181251 1248687580588400158771877)
                ·
                  refine ⟨234128921360325029769727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1248687580588400158771877 234128921360325029769727)
                  ·
                    rfl

theorem cell21_1025920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 4].length) (baseStart_1025920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1025920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1025920 prefixEnd_1025920 := by exact prefixLift 1025920
  have htrace : WordTrace (prefixWord ++ tailWord_1025920) baseStart_1025920 baseEnd_1025920 := by
    simpa [prefixWord, tailWord_1025920, baseEnd_1025920] using wordTrace_append hprefix tailTrace_1025920
  have hstable : (prefixWord ++ tailWord_1025920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025920).length < 2 ^ (prefixWord ++ tailWord_1025920).sum := by decide
  have hdescent : baseEnd_1025920 < baseStart_1025920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025951 : List Nat := [1, 1, 2, 5, 4, 1, 7]
def baseStart_1025951 : Nat := 118140960795 + 1025951 * 2 ^ 59
def prefixEnd_1025951 : Nat := 4983230072969 + 3 ^ 40 * 1025951 * 2
def baseEnd_1025951 : Nat := 26015110664741762750333

theorem tailTrace_1025951 : CollatzResearch.WordTrace tailWord_1025951 prefixEnd_1025951 26015110664741762750333 := by
  unfold tailWord_1025951
  simp only [CollatzResearch.WordTrace]
  refine ⟨37419507106162220326053707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24946338070774813550702471 37419507106162220326053707)
  ·
    refine ⟨56129260659243330489080561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37419507106162220326053707 56129260659243330489080561)
    ·
      refine ⟨42096945494432497866810421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56129260659243330489080561 42096945494432497866810421)
      ·
        refine ⟨3946588640103046675013477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42096945494432497866810421 3946588640103046675013477)
        ·
          refine ⟨739985370019321251565027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3946588640103046675013477 739985370019321251565027)
          ·
            refine ⟨1109978055028981877347541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 739985370019321251565027 1109978055028981877347541)
            ·
              refine ⟨26015110664741762750333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1109978055028981877347541 26015110664741762750333)
              ·
                rfl

theorem cell21_1025951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 7].length) (baseStart_1025951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1025951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1025951 prefixEnd_1025951 := by exact prefixLift 1025951
  have htrace : WordTrace (prefixWord ++ tailWord_1025951) baseStart_1025951 baseEnd_1025951 := by
    simpa [prefixWord, tailWord_1025951, baseEnd_1025951] using wordTrace_append hprefix tailTrace_1025951
  have hstable : (prefixWord ++ tailWord_1025951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025951).length < 2 ^ (prefixWord ++ tailWord_1025951).sum := by decide
  have hdescent : baseEnd_1025951 < baseStart_1025951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026010 : List Nat := [3, 1, 1, 2, 6, 8]
def baseStart_1026010 : Nat := 118140960795 + 1026010 * 2 ^ 59
def prefixEnd_1026010 : Nat := 4983230072969 + 3 ^ 40 * 1026010 * 2
def baseEnd_1026010 : Nat := 8672202243944624935909

theorem tailTrace_1026010 : CollatzResearch.WordTrace tailWord_1026010 prefixEnd_1026010 8672202243944624935909 := by
  unfold tailWord_1026010
  simp only [CollatzResearch.WordTrace]
  refine ⟨9355414753237118350612871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24947772675298982268300989 9355414753237118350612871)
  ·
    refine ⟨14033122129855677525919307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9355414753237118350612871 14033122129855677525919307)
    ·
      refine ⟨21049683194783516288878961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14033122129855677525919307 21049683194783516288878961)
      ·
        refine ⟨15787262396087637216659221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21049683194783516288878961 15787262396087637216659221)
        ·
          refine ⟨740027924816607994530901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15787262396087637216659221 740027924816607994530901)
          ·
            refine ⟨8672202243944624935909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 740027924816607994530901 8672202243944624935909)
            ·
              rfl

theorem cell21_1026010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 8].length) (baseStart_1026010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1026010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1026010 prefixEnd_1026010 := by exact prefixLift 1026010
  have htrace : WordTrace (prefixWord ++ tailWord_1026010) baseStart_1026010 baseEnd_1026010 := by
    simpa [prefixWord, tailWord_1026010, baseEnd_1026010] using wordTrace_append hprefix tailTrace_1026010
  have hstable : (prefixWord ++ tailWord_1026010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026010).length < 2 ^ (prefixWord ++ tailWord_1026010).sum := by decide
  have hdescent : baseEnd_1026010 < baseStart_1026010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026013 : List Nat := [1, 4, 3, 1, 3, 1, 2, 2, 4]
def baseStart_1026013 : Nat := 118140960795 + 1026013 * 2 ^ 59
def prefixEnd_1026013 : Nat := 4983230072969 + 3 ^ 40 * 1026013 * 2
def baseEnd_1026013 : Nat := 234150145227377534719537

theorem tailTrace_1026013 : CollatzResearch.WordTrace tailWord_1026013 prefixEnd_1026013 234150145227377534719537 := by
  unfold tailWord_1026013
  simp only [CollatzResearch.WordTrace]
  refine ⟨37421768431937604914810693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24947845621291736609873795 37421768431937604914810693)
  ·
    refine ⟨7016581580988300921527005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37421768431937604914810693 7016581580988300921527005)
    ·
      refine ⟨2631218092870612845572627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7016581580988300921527005 2631218092870612845572627)
      ·
        refine ⟨3946827139305919268358941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2631218092870612845572627 3946827139305919268358941)
        ·
          refine ⟨1480060177239719725634603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3946827139305919268358941 1480060177239719725634603)
          ·
            refine ⟨2220090265859579588451905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1480060177239719725634603 2220090265859579588451905)
            ·
              refine ⟨1665067699394684691338929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2220090265859579588451905 1665067699394684691338929)
              ·
                refine ⟨1248800774546013518504197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1665067699394684691338929 1248800774546013518504197)
                ·
                  refine ⟨234150145227377534719537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1248800774546013518504197 234150145227377534719537)
                  ·
                    rfl

theorem cell21_1026013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_1026013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1026013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1026013 prefixEnd_1026013 := by exact prefixLift 1026013
  have htrace : WordTrace (prefixWord ++ tailWord_1026013) baseStart_1026013 baseEnd_1026013 := by
    simpa [prefixWord, tailWord_1026013, baseEnd_1026013] using wordTrace_append hprefix tailTrace_1026013
  have hstable : (prefixWord ++ tailWord_1026013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026013).length < 2 ^ (prefixWord ++ tailWord_1026013).sum := by decide
  have hdescent : baseEnd_1026013 < baseStart_1026013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026024 : List Nat := [2, 1, 4, 1, 1, 1, 1, 5, 5]
def baseStart_1026024 : Nat := 118140960795 + 1026024 * 2 ^ 59
def prefixEnd_1026024 : Nat := 4983230072969 + 3 ^ 40 * 1026024 * 2
def baseEnd_1026024 : Nat := 234152655577243960036181

theorem tailTrace_1026024 : CollatzResearch.WordTrace tailWord_1026024 prefixEnd_1026024 234152655577243960036181 := by
  unfold tailWord_1026024
  simp only [CollatzResearch.WordTrace]
  refine ⟨18711084817448876896730563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24948113089931835862307417 18711084817448876896730563)
  ·
    refine ⟨28066627226173315345095845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18711084817448876896730563 28066627226173315345095845)
    ·
      refine ⟨5262492604907496627205471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28066627226173315345095845 5262492604907496627205471)
      ·
        refine ⟨7893738907361244940808207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5262492604907496627205471 7893738907361244940808207)
        ·
          refine ⟨11840608361041867411212311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7893738907361244940808207 11840608361041867411212311)
          ·
            refine ⟨17760912541562801116818467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11840608361041867411212311 17760912541562801116818467)
            ·
              refine ⟨26641368812344201675227701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17760912541562801116818467 26641368812344201675227701)
              ·
                refine ⟨2497628326157268907052597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26641368812344201675227701 2497628326157268907052597)
                ·
                  refine ⟨234152655577243960036181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2497628326157268907052597 234152655577243960036181)
                  ·
                    rfl

theorem cell21_1026024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 5].length) (baseStart_1026024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1026024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1026024 prefixEnd_1026024 := by exact prefixLift 1026024
  have htrace : WordTrace (prefixWord ++ tailWord_1026024) baseStart_1026024 baseEnd_1026024 := by
    simpa [prefixWord, tailWord_1026024, baseEnd_1026024] using wordTrace_append hprefix tailTrace_1026024
  have hstable : (prefixWord ++ tailWord_1026024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026024).length < 2 ^ (prefixWord ++ tailWord_1026024).sum := by decide
  have hdescent : baseEnd_1026024 < baseStart_1026024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026148 : List Nat := [2, 3, 1, 1, 2, 1, 6, 1, 4]
def baseStart_1026148 : Nat := 118140960795 + 1026148 * 2 ^ 59
def prefixEnd_1026148 : Nat := 4983230072969 + 3 ^ 40 * 1026148 * 2
def baseEnd_1026148 : Nat := 234180954066647299969261

theorem tailTrace_1026148 : CollatzResearch.WordTrace tailWord_1026148 prefixEnd_1026148 234180954066647299969261 := by
  unfold tailWord_1026148
  simp only [CollatzResearch.WordTrace]
  refine ⟨18713346143224261485487549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24951128190965681980650065 18713346143224261485487549)
  ·
    refine ⟨7017504803709098057057831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18713346143224261485487549 7017504803709098057057831)
    ·
      refine ⟨10526257205563647085586747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7017504803709098057057831 10526257205563647085586747)
      ·
        refine ⟨15789385808345470628380121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10526257205563647085586747 15789385808345470628380121)
        ·
          refine ⟨11842039356259102971285091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15789385808345470628380121 11842039356259102971285091)
          ·
            refine ⟨17763059034388654456927637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11842039356259102971285091 17763059034388654456927637)
            ·
              refine ⟨832643392236968177668483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17763059034388654456927637 832643392236968177668483)
              ·
                refine ⟨1248965088355452266502725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 832643392236968177668483 1248965088355452266502725)
                ·
                  refine ⟨234180954066647299969261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1248965088355452266502725 234180954066647299969261)
                  ·
                    rfl

theorem cell21_1026148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_1026148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1026148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1026148 prefixEnd_1026148 := by exact prefixLift 1026148
  have htrace : WordTrace (prefixWord ++ tailWord_1026148) baseStart_1026148 baseEnd_1026148 := by
    simpa [prefixWord, tailWord_1026148, baseEnd_1026148] using wordTrace_append hprefix tailTrace_1026148
  have hstable : (prefixWord ++ tailWord_1026148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026148).length < 2 ^ (prefixWord ++ tailWord_1026148).sum := by decide
  have hdescent : baseEnd_1026148 < baseStart_1026148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026196 : List Nat := [2, 4, 2, 3, 1, 2, 1, 6]
def baseStart_1026196 : Nat := 118140960795 + 1026196 * 2 ^ 59
def prefixEnd_1026196 : Nat := 4983230072969 + 3 ^ 40 * 1026196 * 2
def baseEnd_1026196 : Nat := 78063969440203294389721

theorem tailTrace_1026196 : CollatzResearch.WordTrace tailWord_1026196 prefixEnd_1026196 78063969440203294389721 := by
  unfold tailWord_1026196
  simp only [CollatzResearch.WordTrace]
  refine ⟨18714221495137313584361221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24952295326849751445814961 18714221495137313584361221)
  ·
    refine ⟨3508916530338246297067729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18714221495137313584361221 3508916530338246297067729)
    ·
      refine ⟨2631687397753684722800797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3508916530338246297067729 2631687397753684722800797)
      ·
        refine ⟨986882774157631771050299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2631687397753684722800797 986882774157631771050299)
        ·
          refine ⟨1480324161236447656575449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 986882774157631771050299 1480324161236447656575449)
          ·
            refine ⟨1110243120927335742431587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1480324161236447656575449 1110243120927335742431587)
            ·
              refine ⟨1665364681391003613647381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1110243120927335742431587 1665364681391003613647381)
              ·
                refine ⟨78063969440203294389721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1665364681391003613647381 78063969440203294389721)
                ·
                  rfl

theorem cell21_1026196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 6].length) (baseStart_1026196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1026196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1026196 prefixEnd_1026196 := by exact prefixLift 1026196
  have htrace : WordTrace (prefixWord ++ tailWord_1026196) baseStart_1026196 baseEnd_1026196 := by
    simpa [prefixWord, tailWord_1026196, baseEnd_1026196] using wordTrace_append hprefix tailTrace_1026196
  have hstable : (prefixWord ++ tailWord_1026196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026196).length < 2 ^ (prefixWord ++ tailWord_1026196).sum := by decide
  have hdescent : baseEnd_1026196 < baseStart_1026196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026235 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 7]
def baseStart_1026235 : Nat := 118140960795 + 1026235 * 2 ^ 59
def prefixEnd_1026235 : Nat := 4983230072969 + 3 ^ 40 * 1026235 * 2
def baseEnd_1026235 : Nat := 234200808651954482019083

theorem tailTrace_1026235 : CollatzResearch.WordTrace tailWord_1026235 prefixEnd_1026235 234200808651954482019083 := by
  unfold tailWord_1026235
  simp only [CollatzResearch.WordTrace]
  refine ⟨37429865437133336829392159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24953243624755557886261439 37429865437133336829392159)
  ·
    refine ⟨56144798155700005244088239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37429865437133336829392159 56144798155700005244088239)
    ·
      refine ⟨84217197233550007866132359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56144798155700005244088239 84217197233550007866132359)
      ·
        refine ⟨126325795850325011799198539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84217197233550007866132359 126325795850325011799198539)
        ·
          refine ⟨189488693775487517698797809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126325795850325011799198539 189488693775487517698797809)
          ·
            refine ⟨142116520331615638274098357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189488693775487517698797809 142116520331615638274098357)
            ·
              refine ⟨13323423781088966088196721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142116520331615638274098357 13323423781088966088196721)
              ·
                refine ⟨9992567835816724566147541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13323423781088966088196721 9992567835816724566147541)
                ·
                  refine ⟨234200808651954482019083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9992567835816724566147541 234200808651954482019083)
                  ·
                    rfl

theorem cell21_1026235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 7].length) (baseStart_1026235 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1026235 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1026235 prefixEnd_1026235 := by exact prefixLift 1026235
  have htrace : WordTrace (prefixWord ++ tailWord_1026235) baseStart_1026235 baseEnd_1026235 := by
    simpa [prefixWord, tailWord_1026235, baseEnd_1026235] using wordTrace_append hprefix tailTrace_1026235
  have hstable : (prefixWord ++ tailWord_1026235).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026235).length < 2 ^ (prefixWord ++ tailWord_1026235).sum := by decide
  have hdescent : baseEnd_1026235 < baseStart_1026235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026238 : List Nat := [4, 2, 1, 1, 4, 1, 8]
def baseStart_1026238 : Nat := 118140960795 + 1026238 * 2 ^ 59
def prefixEnd_1026238 : Nat := 4983230072969 + 3 ^ 40 * 1026238 * 2
def baseEnd_1026238 : Nat := 26022388143647460385453

theorem tailTrace_1026238 : CollatzResearch.WordTrace tailWord_1026238 prefixEnd_1026238 26022388143647460385453 := by
  unfold tailWord_1026238
  simp only [CollatzResearch.WordTrace]
  refine ⟨4678746857015308542718921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24953316570748312227834245 4678746857015308542718921)
  ·
    refine ⟨3509060142761481407039191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4678746857015308542718921 3509060142761481407039191)
    ·
      refine ⟨5263590214142222110558787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3509060142761481407039191 5263590214142222110558787)
      ·
        refine ⟨7895385321213333165838181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5263590214142222110558787 7895385321213333165838181)
        ·
          refine ⟨1480384747727499968594659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7895385321213333165838181 1480384747727499968594659)
          ·
            refine ⟨2220577121591249952891989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1480384747727499968594659 2220577121591249952891989)
            ·
              refine ⟨26022388143647460385453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2220577121591249952891989 26022388143647460385453)
              ·
                rfl

theorem cell21_1026238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 8].length) (baseStart_1026238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1026238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1026238 prefixEnd_1026238 := by exact prefixLift 1026238
  have htrace : WordTrace (prefixWord ++ tailWord_1026238) baseStart_1026238 baseEnd_1026238 := by
    simpa [prefixWord, tailWord_1026238, baseEnd_1026238] using wordTrace_append hprefix tailTrace_1026238
  have hstable : (prefixWord ++ tailWord_1026238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026238).length < 2 ^ (prefixWord ++ tailWord_1026238).sum := by decide
  have hdescent : baseEnd_1026238 < baseStart_1026238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026269 : List Nat := [1, 4, 3, 2, 1, 1, 2, 2, 5]
def baseStart_1026269 : Nat := 118140960795 + 1026269 * 2 ^ 59
def prefixEnd_1026269 : Nat := 4983230072969 + 3 ^ 40 * 1026269 * 2
def baseEnd_1026269 : Nat := 234208567915177978452347

theorem tailTrace_1026269 : CollatzResearch.WordTrace tailWord_1026269 prefixEnd_1026269 234208567915177978452347 := by
  unfold tailWord_1026269
  simp only [CollatzResearch.WordTrace]
  refine ⟨37431105519010160636129861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24954070346006773757419907 37431105519010160636129861)
  ·
    refine ⟨7018332284814405119274349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37431105519010160636129861 7018332284814405119274349)
    ·
      refine ⟨2631874606805401919727881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7018332284814405119274349 2631874606805401919727881)
      ·
        refine ⟨1973905955104051439795911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2631874606805401919727881 1973905955104051439795911)
        ·
          refine ⟨2960858932656077159693867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1973905955104051439795911 2960858932656077159693867)
          ·
            refine ⟨4441288398984115739540801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2960858932656077159693867 4441288398984115739540801)
            ·
              refine ⟨3330966299238086804655601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4441288398984115739540801 3330966299238086804655601)
              ·
                refine ⟨2498224724428565103491701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3330966299238086804655601 2498224724428565103491701)
                ·
                  refine ⟨234208567915177978452347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2498224724428565103491701 234208567915177978452347)
                  ·
                    rfl

theorem cell21_1026269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_1026269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1026269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1026269 prefixEnd_1026269 := by exact prefixLift 1026269
  have htrace : WordTrace (prefixWord ++ tailWord_1026269) baseStart_1026269 baseEnd_1026269 := by
    simpa [prefixWord, tailWord_1026269, baseEnd_1026269] using wordTrace_append hprefix tailTrace_1026269
  have hstable : (prefixWord ++ tailWord_1026269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026269).length < 2 ^ (prefixWord ++ tailWord_1026269).sum := by decide
  have hdescent : baseEnd_1026269 < baseStart_1026269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026362 : List Nat := [3, 1, 1, 1, 4, 2, 4, 2, 3]
def baseStart_1026362 : Nat := 118140960795 + 1026362 * 2 ^ 59
def prefixEnd_1026362 : Nat := 4983230072969 + 3 ^ 40 * 1026362 * 2
def baseEnd_1026362 : Nat := 234229791782230483402157

theorem tailTrace_1026362 : CollatzResearch.WordTrace tailWord_1026362 prefixEnd_1026362 234229791782230483402157 := by
  unfold tailWord_1026362
  simp only [CollatzResearch.WordTrace]
  refine ⟨9358624376918309379816335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24956331671782158346176893 9358624376918309379816335)
  ·
    refine ⟨14037936565377464069724503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9358624376918309379816335 14037936565377464069724503)
    ·
      refine ⟨21056904848066196104586755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14037936565377464069724503 21056904848066196104586755)
      ·
        refine ⟨31585357272099294156880133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21056904848066196104586755 31585357272099294156880133)
        ·
          refine ⟨5922254488518617654415025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31585357272099294156880133 5922254488518617654415025)
          ·
            refine ⟨4441690866388963240811269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5922254488518617654415025 4441690866388963240811269)
            ·
              refine ⟨832817037447930607652113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4441690866388963240811269 832817037447930607652113)
              ·
                refine ⟨624612778085947955739085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 832817037447930607652113 624612778085947955739085)
                ·
                  refine ⟨234229791782230483402157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 624612778085947955739085 234229791782230483402157)
                  ·
                    rfl

theorem cell21_1026362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 2, 3].length) (baseStart_1026362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1026362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1026362 prefixEnd_1026362 := by exact prefixLift 1026362
  have htrace : WordTrace (prefixWord ++ tailWord_1026362) baseStart_1026362 baseEnd_1026362 := by
    simpa [prefixWord, tailWord_1026362, baseEnd_1026362] using wordTrace_append hprefix tailTrace_1026362
  have hstable : (prefixWord ++ tailWord_1026362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026362).length < 2 ^ (prefixWord ++ tailWord_1026362).sum := by decide
  have hdescent : baseEnd_1026362 < baseStart_1026362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026421 : List Nat := [1, 3, 4, 1, 2, 2, 2, 1, 5]
def baseStart_1026421 : Nat := 118140960795 + 1026421 * 2 ^ 59
def prefixEnd_1026421 : Nat := 4983230072969 + 3 ^ 40 * 1026421 * 2
def baseEnd_1026421 : Nat := 234243256386059491918703

theorem tailTrace_1026421 : CollatzResearch.WordTrace tailWord_1026421 prefixEnd_1026421 234243256386059491918703 := by
  unfold tailWord_1026421
  simp only [CollatzResearch.WordTrace]
  refine ⟨37436649414459490595663117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24957766276306327063775411 37436649414459490595663117)
  ·
    refine ⟨14038743530422308973373669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37436649414459490595663117 14038743530422308973373669)
    ·
      refine ⟨2632264411954182932507563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14038743530422308973373669 2632264411954182932507563)
      ·
        refine ⟨3948396617931274398761345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2632264411954182932507563 3948396617931274398761345)
        ·
          refine ⟨2961297463448455799071009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3948396617931274398761345 2961297463448455799071009)
          ·
            refine ⟨2220973097586341849303257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2961297463448455799071009 2220973097586341849303257)
            ·
              refine ⟨1665729823189756386977443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2220973097586341849303257 1665729823189756386977443)
              ·
                refine ⟨2498594734784634580466165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1665729823189756386977443 2498594734784634580466165)
                ·
                  refine ⟨234243256386059491918703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2498594734784634580466165 234243256386059491918703)
                  ·
                    rfl

theorem cell21_1026421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_1026421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1026421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1026421 prefixEnd_1026421 := by exact prefixLift 1026421
  have htrace : WordTrace (prefixWord ++ tailWord_1026421) baseStart_1026421 baseEnd_1026421 := by
    simpa [prefixWord, tailWord_1026421, baseEnd_1026421] using wordTrace_append hprefix tailTrace_1026421
  have hstable : (prefixWord ++ tailWord_1026421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026421).length < 2 ^ (prefixWord ++ tailWord_1026421).sum := by decide
  have hdescent : baseEnd_1026421 < baseStart_1026421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026531 : List Nat := [1, 1, 1, 6, 3, 2, 2, 2, 3]
def baseStart_1026531 : Nat := 118140960795 + 1026531 * 2 ^ 59
def prefixEnd_1026531 : Nat := 4983230072969 + 3 ^ 40 * 1026531 * 2
def baseEnd_1026531 : Nat := 234268359884723745085145

theorem tailTrace_1026531 : CollatzResearch.WordTrace tailWord_1026531 prefixEnd_1026531 234268359884723745085145 := by
  unfold tailWord_1026531
  simp only [CollatzResearch.WordTrace]
  refine ⟨37440661444060979382167447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24960440962707319588111631 37440661444060979382167447)
  ·
    refine ⟨56160992166091469073251171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37440661444060979382167447 56160992166091469073251171)
    ·
      refine ⟨84241488249137203609876757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56160992166091469073251171 84241488249137203609876757)
      ·
        refine ⟨3948819761678306419212973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 84241488249137203609876757 3948819761678306419212973)
        ·
          refine ⟨1480807410629364907204865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3948819761678306419212973 1480807410629364907204865)
          ·
            refine ⟨1110605557972023680403649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1480807410629364907204865 1110605557972023680403649)
            ·
              refine ⟨832954168479017760302737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1110605557972023680403649 832954168479017760302737)
              ·
                refine ⟨624715626359263320227053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 832954168479017760302737 624715626359263320227053)
                ·
                  refine ⟨234268359884723745085145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 624715626359263320227053 234268359884723745085145)
                  ·
                    rfl

theorem cell21_1026531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 2, 3].length) (baseStart_1026531 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1026531 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1026531 prefixEnd_1026531 := by exact prefixLift 1026531
  have htrace : WordTrace (prefixWord ++ tailWord_1026531) baseStart_1026531 baseEnd_1026531 := by
    simpa [prefixWord, tailWord_1026531, baseEnd_1026531] using wordTrace_append hprefix tailTrace_1026531
  have hstable : (prefixWord ++ tailWord_1026531).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026531).length < 2 ^ (prefixWord ++ tailWord_1026531).sum := by decide
  have hdescent : baseEnd_1026531 < baseStart_1026531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026539 : List Nat := [1, 1, 1, 1, 2, 3, 4, 3, 5]
def baseStart_1026539 : Nat := 118140960795 + 1026539 * 2 ^ 59
def prefixEnd_1026539 : Nat := 4983230072969 + 3 ^ 40 * 1026539 * 2
def baseEnd_1026539 : Nat := 234270185593717508951795

theorem tailTrace_1026539 : CollatzResearch.WordTrace tailWord_1026539 prefixEnd_1026539 234270185593717508951795 := by
  unfold tailWord_1026539
  simp only [CollatzResearch.WordTrace]
  refine ⟨37440953228031996748458671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24960635485354664498972447 37440953228031996748458671)
  ·
    refine ⟨56161429842047995122688007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37440953228031996748458671 56161429842047995122688007)
    ·
      refine ⟨84242144763071992684032011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56161429842047995122688007 84242144763071992684032011)
      ·
        refine ⟨126363217144607989026048017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84242144763071992684032011 126363217144607989026048017)
        ·
          refine ⟨94772412858455991769536013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126363217144607989026048017 94772412858455991769536013)
          ·
            refine ⟨35539654821920996913576005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94772412858455991769536013 35539654821920996913576005)
            ·
              refine ⟨6663685279110186921295501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35539654821920996913576005 6663685279110186921295501)
              ·
                refine ⟨2498881979666320095485813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6663685279110186921295501 2498881979666320095485813)
                ·
                  refine ⟨234270185593717508951795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2498881979666320095485813 234270185593717508951795)
                  ·
                    rfl

theorem cell21_1026539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 5].length) (baseStart_1026539 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1026539 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1026539 prefixEnd_1026539 := by exact prefixLift 1026539
  have htrace : WordTrace (prefixWord ++ tailWord_1026539) baseStart_1026539 baseEnd_1026539 := by
    simpa [prefixWord, tailWord_1026539, baseEnd_1026539] using wordTrace_append hprefix tailTrace_1026539
  have hstable : (prefixWord ++ tailWord_1026539).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026539).length < 2 ^ (prefixWord ++ tailWord_1026539).sum := by decide
  have hdescent : baseEnd_1026539 < baseStart_1026539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026542 : List Nat := [4, 1, 2, 1, 2, 4, 1, 6]
def baseStart_1026542 : Nat := 118140960795 + 1026542 * 2 ^ 59
def prefixEnd_1026542 : Nat := 4983230072969 + 3 ^ 40 * 1026542 * 2
def baseEnd_1026542 : Nat := 78090290078196723467263

theorem tailTrace_1026542 : CollatzResearch.WordTrace tailWord_1026542 prefixEnd_1026542 78090290078196723467263 := by
  unfold tailWord_1026542
  simp only [CollatzResearch.WordTrace]
  refine ⟨4680132830877641032602235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24960708431347418840545253 4680132830877641032602235)
  ·
    refine ⟨7020199246316461548903353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4680132830877641032602235 7020199246316461548903353)
    ·
      refine ⟨5265149434737346161677515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7020199246316461548903353 5265149434737346161677515)
      ·
        refine ⟨7897724152106019242516273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5265149434737346161677515 7897724152106019242516273)
        ·
          refine ⟨5923293114079514431887205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7897724152106019242516273 5923293114079514431887205)
          ·
            refine ⟨1110617458889908955978851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5923293114079514431887205 1110617458889908955978851)
            ·
              refine ⟨1665926188334863433968277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1110617458889908955978851 1665926188334863433968277)
              ·
                refine ⟨78090290078196723467263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1665926188334863433968277 78090290078196723467263)
                ·
                  rfl

theorem cell21_1026542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_1026542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1026542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1026542 prefixEnd_1026542 := by exact prefixLift 1026542
  have htrace : WordTrace (prefixWord ++ tailWord_1026542) baseStart_1026542 baseEnd_1026542 := by
    simpa [prefixWord, tailWord_1026542, baseEnd_1026542] using wordTrace_append hprefix tailTrace_1026542
  have hstable : (prefixWord ++ tailWord_1026542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026542).length < 2 ^ (prefixWord ++ tailWord_1026542).sum := by decide
  have hdescent : baseEnd_1026542 < baseStart_1026542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026570 : List Nat := [3, 1, 2, 2, 2, 1, 2, 2, 6]
def baseStart_1026570 : Nat := 118140960795 + 1026570 * 2 ^ 59
def prefixEnd_1026570 : Nat := 4983230072969 + 3 ^ 40 * 1026570 * 2
def baseEnd_1026570 : Nat := 234277260216068343935065

theorem tailTrace_1026570 : CollatzResearch.WordTrace tailWord_1026570 prefixEnd_1026570 234277260216068343935065 := by
  unfold tailWord_1026570
  simp only [CollatzResearch.WordTrace]
  refine ⟨9360520972729922260709291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24961389260613126028558109 9360520972729922260709291)
  ·
    refine ⟨14040781459094883391063937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9360520972729922260709291 14040781459094883391063937)
    ·
      refine ⟨10530586094321162543297953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14040781459094883391063937 10530586094321162543297953)
      ·
        refine ⟨7897939570740871907473465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10530586094321162543297953 7897939570740871907473465)
        ·
          refine ⟨5923454678055653930605099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7897939570740871907473465 5923454678055653930605099)
          ·
            refine ⟨8885182017083480895907649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5923454678055653930605099 8885182017083480895907649)
            ·
              refine ⟨6663886512812610671930737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8885182017083480895907649 6663886512812610671930737)
              ·
                refine ⟨4997914884609458003948053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6663886512812610671930737 4997914884609458003948053)
                ·
                  refine ⟨234277260216068343935065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4997914884609458003948053 234277260216068343935065)
                  ·
                    rfl

theorem cell21_1026570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_1026570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1026570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1026570 prefixEnd_1026570 := by exact prefixLift 1026570
  have htrace : WordTrace (prefixWord ++ tailWord_1026570) baseStart_1026570 baseEnd_1026570 := by
    simpa [prefixWord, tailWord_1026570, baseEnd_1026570] using wordTrace_append hprefix tailTrace_1026570
  have hstable : (prefixWord ++ tailWord_1026570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026570).length < 2 ^ (prefixWord ++ tailWord_1026570).sum := by decide
  have hdescent : baseEnd_1026570 < baseStart_1026570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026615 : List Nat := [1, 1, 3, 1, 2, 3, 1, 4, 5]
def baseStart_1026615 : Nat := 118140960795 + 1026615 * 2 ^ 59
def prefixEnd_1026615 : Nat := 4983230072969 + 3 ^ 40 * 1026615 * 2
def baseEnd_1026615 : Nat := 234287529829158265684973

theorem tailTrace_1026615 : CollatzResearch.WordTrace tailWord_1026615 prefixEnd_1026615 234287529829158265684973 := by
  unfold tailWord_1026615
  simp only [CollatzResearch.WordTrace]
  refine ⟨37443725175756661728225299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24962483450504441152150199 37443725175756661728225299)
  ·
    refine ⟨56165587763634992592337949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37443725175756661728225299 56165587763634992592337949)
    ·
      refine ⟨21062095411363122222126731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56165587763634992592337949 21062095411363122222126731)
      ·
        refine ⟨31593143117044683333190097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21062095411363122222126731 31593143117044683333190097)
        ·
          refine ⟨23694857337783512499892573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31593143117044683333190097 23694857337783512499892573)
          ·
            refine ⟨8885571501668817187459715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23694857337783512499892573 8885571501668817187459715)
            ·
              refine ⟨13328357252503225781189573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8885571501668817187459715 13328357252503225781189573)
              ·
                refine ⟨2499066984844354833973045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13328357252503225781189573 2499066984844354833973045)
                ·
                  refine ⟨234287529829158265684973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2499066984844354833973045 234287529829158265684973)
                  ·
                    rfl

theorem cell21_1026615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 5].length) (baseStart_1026615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1026615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1026615 prefixEnd_1026615 := by exact prefixLift 1026615
  have htrace : WordTrace (prefixWord ++ tailWord_1026615) baseStart_1026615 baseEnd_1026615 := by
    simpa [prefixWord, tailWord_1026615, baseEnd_1026615] using wordTrace_append hprefix tailTrace_1026615
  have hstable : (prefixWord ++ tailWord_1026615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026615).length < 2 ^ (prefixWord ++ tailWord_1026615).sum := by decide
  have hdescent : baseEnd_1026615 < baseStart_1026615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026618 : List Nat := [3, 1, 1, 1, 3, 5, 2, 5]
def baseStart_1026618 : Nat := 118140960795 + 1026618 * 2 ^ 59
def prefixEnd_1026618 : Nat := 4983230072969 + 3 ^ 40 * 1026618 * 2
def baseEnd_1026618 : Nat := 78096071490010309044989

theorem tailTrace_1026618 : CollatzResearch.WordTrace tailWord_1026618 prefixEnd_1026618 78096071490010309044989 := by
  unfold tailWord_1026618
  simp only [CollatzResearch.WordTrace]
  refine ⟨9360958648686448310146127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24962556396497195493723005 9360958648686448310146127)
  ·
    refine ⟨14041437973029672465219191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9360958648686448310146127 14041437973029672465219191)
    ·
      refine ⟨21062156959544508697828787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14041437973029672465219191 21062156959544508697828787)
      ·
        refine ⟨31593235439316763046743181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21062156959544508697828787 31593235439316763046743181)
        ·
          refine ⟨11847463289743786142528693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31593235439316763046743181 11847463289743786142528693)
          ·
            refine ⟨1110699683413479950862065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11847463289743786142528693 1110699683413479950862065)
            ·
              refine ⟨833024762560109963146549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1110699683413479950862065 833024762560109963146549)
              ·
                refine ⟨78096071490010309044989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 833024762560109963146549 78096071490010309044989)
                ·
                  rfl

theorem cell21_1026618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 5].length) (baseStart_1026618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1026618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1026618 prefixEnd_1026618 := by exact prefixLift 1026618
  have htrace : WordTrace (prefixWord ++ tailWord_1026618) baseStart_1026618 baseEnd_1026618 := by
    simpa [prefixWord, tailWord_1026618, baseEnd_1026618] using wordTrace_append hprefix tailTrace_1026618
  have hstable : (prefixWord ++ tailWord_1026618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026618).length < 2 ^ (prefixWord ++ tailWord_1026618).sum := by decide
  have hdescent : baseEnd_1026618 < baseStart_1026618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026705 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 10]
def baseStart_1026705 : Nat := 118140960795 + 1026705 * 2 ^ 59
def prefixEnd_1026705 : Nat := 4983230072969 + 3 ^ 40 * 1026705 * 2
def baseEnd_1026705 : Nat := 234308069055338109184789

theorem tailTrace_1026705 : CollatzResearch.WordTrace tailWord_1026705 prefixEnd_1026705 234308069055338109184789 := by
  unfold tailWord_1026705
  simp only [CollatzResearch.WordTrace]
  refine ⟨37447007745430607099001569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24964671830287071399334379 37447007745430607099001569)
  ·
    refine ⟨28085255809072955324251177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37447007745430607099001569 28085255809072955324251177)
    ·
      refine ⟨21063941856804716493188383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28085255809072955324251177 21063941856804716493188383)
      ·
        refine ⟨31595912785207074739782575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21063941856804716493188383 31595912785207074739782575)
        ·
          refine ⟨47393869177810612109673863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31595912785207074739782575 47393869177810612109673863)
          ·
            refine ⟨71090803766715918164510795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47393869177810612109673863 71090803766715918164510795)
            ·
              refine ⟨106636205650073877246766193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71090803766715918164510795 106636205650073877246766193)
              ·
                refine ⟨79977154237555407935074645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106636205650073877246766193 79977154237555407935074645)
                ·
                  refine ⟨234308069055338109184789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 79977154237555407935074645 234308069055338109184789)
                  ·
                    rfl

theorem cell21_1026705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 10].length) (baseStart_1026705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1026705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1026705 prefixEnd_1026705 := by exact prefixLift 1026705
  have htrace : WordTrace (prefixWord ++ tailWord_1026705) baseStart_1026705 baseEnd_1026705 := by
    simpa [prefixWord, tailWord_1026705, baseEnd_1026705] using wordTrace_append hprefix tailTrace_1026705
  have hstable : (prefixWord ++ tailWord_1026705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026705).length < 2 ^ (prefixWord ++ tailWord_1026705).sum := by decide
  have hdescent : baseEnd_1026705 < baseStart_1026705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026756 : List Nat := [2, 3, 3, 1, 1, 4, 1, 2, 4]
def baseStart_1026756 : Nat := 118140960795 + 1026756 * 2 ^ 59
def prefixEnd_1026756 : Nat := 4983230072969 + 3 ^ 40 * 1026756 * 2
def baseEnd_1026756 : Nat := 234319707950173353834685

theorem tailTrace_1026756 : CollatzResearch.WordTrace tailWord_1026756 prefixEnd_1026756 234319707950173353834685 := by
  unfold tailWord_1026756
  simp only [CollatzResearch.WordTrace]
  refine ⟨18724433934122921404554061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24965911912163895206072081 18724433934122921404554061)
  ·
    refine ⟨7021662725296095526707773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18724433934122921404554061 7021662725296095526707773)
    ·
      refine ⟨2633123521986035822515415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7021662725296095526707773 2633123521986035822515415)
      ·
        refine ⟨3949685282979053733773123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2633123521986035822515415 3949685282979053733773123)
        ·
          refine ⟨5924527924468580600659685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3949685282979053733773123 5924527924468580600659685)
          ·
            refine ⟨1110848985837858862623691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5924527924468580600659685 1110848985837858862623691)
            ·
              refine ⟨1666273478756788293935537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1110848985837858862623691 1666273478756788293935537)
              ·
                refine ⟨1249705109067591220451653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1666273478756788293935537 1249705109067591220451653)
                ·
                  refine ⟨234319707950173353834685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1249705109067591220451653 234319707950173353834685)
                  ·
                    rfl

theorem cell21_1026756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_1026756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1026756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1026756 prefixEnd_1026756 := by exact prefixLift 1026756
  have htrace : WordTrace (prefixWord ++ tailWord_1026756) baseStart_1026756 baseEnd_1026756 := by
    simpa [prefixWord, tailWord_1026756, baseEnd_1026756] using wordTrace_append hprefix tailTrace_1026756
  have hstable : (prefixWord ++ tailWord_1026756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026756).length < 2 ^ (prefixWord ++ tailWord_1026756).sum := by decide
  have hdescent : baseEnd_1026756 < baseStart_1026756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026773 : List Nat := [1, 3, 2, 5, 1, 1, 3, 1, 4]
def baseStart_1026773 : Nat := 118140960795 + 1026773 * 2 ^ 59
def prefixEnd_1026773 : Nat := 4983230072969 + 3 ^ 40 * 1026773 * 2
def baseEnd_1026773 : Nat := 234323587581785102051317

theorem tailTrace_1026773 : CollatzResearch.WordTrace tailWord_1026773 prefixEnd_1026773 234323587581785102051317 := by
  unfold tailWord_1026773
  simp only [CollatzResearch.WordTrace]
  refine ⟨37449487909184254712476973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24966325272789503141651315 37449487909184254712476973)
  ·
    refine ⟨14043557965944095517178865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37449487909184254712476973 14043557965944095517178865)
    ·
      refine ⟨10532668474458071637884149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14043557965944095517178865 10532668474458071637884149)
      ·
        refine ⟨987437669480444216051639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10532668474458071637884149 987437669480444216051639)
        ·
          refine ⟨1481156504220666324077459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 987437669480444216051639 1481156504220666324077459)
          ·
            refine ⟨2221734756330999486116189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1481156504220666324077459 2221734756330999486116189)
            ·
              refine ⟨833150533624124807293571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2221734756330999486116189 833150533624124807293571)
              ·
                refine ⟨1249725800436187210940357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 833150533624124807293571 1249725800436187210940357)
                ·
                  refine ⟨234323587581785102051317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1249725800436187210940357 234323587581785102051317)
                  ·
                    rfl

theorem cell21_1026773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_1026773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1026773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1026773 prefixEnd_1026773 := by exact prefixLift 1026773
  have htrace : WordTrace (prefixWord ++ tailWord_1026773) baseStart_1026773 baseEnd_1026773 := by
    simpa [prefixWord, tailWord_1026773, baseEnd_1026773] using wordTrace_append hprefix tailTrace_1026773
  have hstable : (prefixWord ++ tailWord_1026773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026773).length < 2 ^ (prefixWord ++ tailWord_1026773).sum := by decide
  have hdescent : baseEnd_1026773 < baseStart_1026773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026798 : List Nat := [4, 1, 2, 1, 1, 3, 1, 2, 6]
def baseStart_1026798 : Nat := 118140960795 + 1026798 * 2 ^ 59
def prefixEnd_1026798 : Nat := 4983230072969 + 3 ^ 40 * 1026798 * 2
def baseEnd_1026798 : Nat := 234329292922390614134599

theorem tailTrace_1026798 : CollatzResearch.WordTrace tailWord_1026798 prefixEnd_1026798 234329292922390614134599 := by
  unfold tailWord_1026798
  simp only [CollatzResearch.WordTrace]
  refine ⟨4681299966761710497767131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24966933156062455988091365 4681299966761710497767131)
  ·
    refine ⟨7021949950142565746650697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4681299966761710497767131 7021949950142565746650697)
    ·
      refine ⟨5266462462606924309988023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7021949950142565746650697 5266462462606924309988023)
      ·
        refine ⟨7899693693910386464982035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5266462462606924309988023 7899693693910386464982035)
        ·
          refine ⟨11849540540865579697473053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7899693693910386464982035 11849540540865579697473053)
          ·
            refine ⟨4443577702824592386552395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11849540540865579697473053 4443577702824592386552395)
            ·
              refine ⟨6665366554236888579828593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4443577702824592386552395 6665366554236888579828593)
              ·
                refine ⟨4999024915677666434871445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6665366554236888579828593 4999024915677666434871445)
                ·
                  refine ⟨234329292922390614134599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4999024915677666434871445 234329292922390614134599)
                  ·
                    rfl

theorem cell21_1026798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_1026798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1026798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1026798 prefixEnd_1026798 := by exact prefixLift 1026798
  have htrace : WordTrace (prefixWord ++ tailWord_1026798) baseStart_1026798 baseEnd_1026798 := by
    simpa [prefixWord, tailWord_1026798, baseEnd_1026798] using wordTrace_append hprefix tailTrace_1026798
  have hstable : (prefixWord ++ tailWord_1026798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026798).length < 2 ^ (prefixWord ++ tailWord_1026798).sum := by decide
  have hdescent : baseEnd_1026798 < baseStart_1026798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026804 : List Nat := [2, 6, 1, 1, 3, 1, 7]
def baseStart_1026804 : Nat := 118140960795 + 1026804 * 2 ^ 59
def prefixEnd_1026804 : Nat := 4983230072969 + 3 ^ 40 * 1026804 * 2
def baseEnd_1026804 : Nat := 26036740244903993003843

theorem tailTrace_1026804 : CollatzResearch.WordTrace tailWord_1026804 prefixEnd_1026804 26036740244903993003843 := by
  unfold tailWord_1026804
  simp only [CollatzResearch.WordTrace]
  refine ⟨18725309286035973503427733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24967079048047964671236977 18725309286035973503427733)
  ·
    refine ⟨877748872782936257973175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18725309286035973503427733 877748872782936257973175)
    ·
      refine ⟨1316623309174404386959763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 877748872782936257973175 1316623309174404386959763)
      ·
        refine ⟨1974934963761606580439645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1316623309174404386959763 1974934963761606580439645)
        ·
          refine ⟨740600611410602467664867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1974934963761606580439645 740600611410602467664867)
          ·
            refine ⟨1110900917115903701497301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740600611410602467664867 1110900917115903701497301)
            ·
              refine ⟨26036740244903993003843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1110900917115903701497301 26036740244903993003843)
              ·
                rfl

theorem cell21_1026804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 7].length) (baseStart_1026804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1026804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1026804 prefixEnd_1026804 := by exact prefixLift 1026804
  have htrace : WordTrace (prefixWord ++ tailWord_1026804) baseStart_1026804 baseEnd_1026804 := by
    simpa [prefixWord, tailWord_1026804, baseEnd_1026804] using wordTrace_append hprefix tailTrace_1026804
  have hstable : (prefixWord ++ tailWord_1026804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026804).length < 2 ^ (prefixWord ++ tailWord_1026804).sum := by decide
  have hdescent : baseEnd_1026804 < baseStart_1026804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026812 : List Nat := [2, 2, 2, 1, 3, 2, 9]
def baseStart_1026812 : Nat := 118140960795 + 1026812 * 2 ^ 59
def prefixEnd_1026812 : Nat := 4983230072969 + 3 ^ 40 * 1026812 * 2
def baseEnd_1026812 : Nat := 26036943101458855655693

theorem tailTrace_1026812 : CollatzResearch.WordTrace tailWord_1026812 prefixEnd_1026812 26036943101458855655693 := by
  unfold tailWord_1026812
  simp only [CollatzResearch.WordTrace]
  refine ⟨18725455178021482186573345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24967273570695309582097793 18725455178021482186573345)
  ·
    refine ⟨14044091383516111639930009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18725455178021482186573345 14044091383516111639930009)
    ·
      refine ⟨10533068537637083729947507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14044091383516111639930009 10533068537637083729947507)
      ·
        refine ⟨15799602806455625594921261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10533068537637083729947507 15799602806455625594921261)
        ·
          refine ⟨5924851052420859598095473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15799602806455625594921261 5924851052420859598095473)
          ·
            refine ⟨4443638289315644698571605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5924851052420859598095473 4443638289315644698571605)
            ·
              refine ⟨26036943101458855655693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4443638289315644698571605 26036943101458855655693)
              ·
                rfl

theorem cell21_1026812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 9].length) (baseStart_1026812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1026812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1026812 prefixEnd_1026812 := by exact prefixLift 1026812
  have htrace : WordTrace (prefixWord ++ tailWord_1026812) baseStart_1026812 baseEnd_1026812 := by
    simpa [prefixWord, tailWord_1026812, baseEnd_1026812] using wordTrace_append hprefix tailTrace_1026812
  have hstable : (prefixWord ++ tailWord_1026812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026812).length < 2 ^ (prefixWord ++ tailWord_1026812).sum := by decide
  have hdescent : baseEnd_1026812 < baseStart_1026812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026860 : List Nat := [2, 2, 1, 1, 1, 4, 2, 5, 3]
def baseStart_1026860 : Nat := 118140960795 + 1026860 * 2 ^ 59
def prefixEnd_1026860 : Nat := 4983230072969 + 3 ^ 40 * 1026860 * 2
def baseEnd_1026860 : Nat := 234343442167092284101139

theorem tailTrace_1026860 : CollatzResearch.WordTrace tailWord_1026860 prefixEnd_1026860 234343442167092284101139 := by
  unfold tailWord_1026860
  simp only [CollatzResearch.WordTrace]
  refine ⟨18726330529934534285447017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24968440706579379047262689 18726330529934534285447017)
  ·
    refine ⟨14044747897450900714085263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18726330529934534285447017 14044747897450900714085263)
    ·
      refine ⟨21067121846176351071127895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14044747897450900714085263 21067121846176351071127895)
      ·
        refine ⟨31600682769264526606691843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21067121846176351071127895 31600682769264526606691843)
        ·
          refine ⟨47401024153896789910037765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31600682769264526606691843 47401024153896789910037765)
          ·
            refine ⟨8887692028855648108132081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47401024153896789910037765 8887692028855648108132081)
            ·
              refine ⟨6665769021641736081099061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8887692028855648108132081 6665769021641736081099061)
              ·
                refine ⟨624915845778912757603037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6665769021641736081099061 624915845778912757603037)
                ·
                  refine ⟨234343442167092284101139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 624915845778912757603037 234343442167092284101139)
                  ·
                    rfl

theorem cell21_1026860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5, 3].length) (baseStart_1026860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1026860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1026860 prefixEnd_1026860 := by exact prefixLift 1026860
  have htrace : WordTrace (prefixWord ++ tailWord_1026860) baseStart_1026860 baseEnd_1026860 := by
    simpa [prefixWord, tailWord_1026860, baseEnd_1026860] using wordTrace_append hprefix tailTrace_1026860
  have hstable : (prefixWord ++ tailWord_1026860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026860).length < 2 ^ (prefixWord ++ tailWord_1026860).sum := by decide
  have hdescent : baseEnd_1026860 < baseStart_1026860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026905 : List Nat := [1, 2, 1, 2, 2, 5, 3, 5]
def baseStart_1026905 : Nat := 118140960795 + 1026905 * 2 ^ 59
def prefixEnd_1026905 : Nat := 4983230072969 + 3 ^ 40 * 1026905 * 2
def baseEnd_1026905 : Nat := 78117903926727401950349

theorem tailTrace_1026905 : CollatzResearch.WordTrace tailWord_1026905 prefixEnd_1026905 78117903926727401950349 := by
  unfold tailWord_1026905
  simp only [CollatzResearch.WordTrace]
  refine ⟨37454302344706041256282169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24969534896470694170854779 37454302344706041256282169)
  ·
    refine ⟨28090726758529530942211627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37454302344706041256282169 28090726758529530942211627)
    ·
      refine ⟨42136090137794296413317441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28090726758529530942211627 42136090137794296413317441)
      ·
        refine ⟨31602067603345722309988081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42136090137794296413317441 31602067603345722309988081)
        ·
          refine ⟨23701550702509291732491061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31602067603345722309988081 23701550702509291732491061)
          ·
            refine ⟨2222020378360246099921037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23701550702509291732491061 2222020378360246099921037)
            ·
              refine ⟨833257641885092287470389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2222020378360246099921037 833257641885092287470389)
              ·
                refine ⟨78117903926727401950349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 833257641885092287470389 78117903926727401950349)
                ·
                  rfl

theorem cell21_1026905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 5].length) (baseStart_1026905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1026905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1026905 prefixEnd_1026905 := by exact prefixLift 1026905
  have htrace : WordTrace (prefixWord ++ tailWord_1026905) baseStart_1026905 baseEnd_1026905 := by
    simpa [prefixWord, tailWord_1026905, baseEnd_1026905] using wordTrace_append hprefix tailTrace_1026905
  have hstable : (prefixWord ++ tailWord_1026905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026905).length < 2 ^ (prefixWord ++ tailWord_1026905).sum := by decide
  have hdescent : baseEnd_1026905 < baseStart_1026905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026970 : List Nat := [3, 1, 1, 4, 3, 2, 1, 3, 3]
def baseStart_1026970 : Nat := 118140960795 + 1026970 * 2 ^ 59
def prefixEnd_1026970 : Nat := 4983230072969 + 3 ^ 40 * 1026970 * 2
def baseEnd_1026970 : Nat := 234368545665756537267581

theorem tailTrace_1026970 : CollatzResearch.WordTrace tailWord_1026970 prefixEnd_1026970 234368545665756537267581 := by
  unfold tailWord_1026970
  simp only [CollatzResearch.WordTrace]
  refine ⟨9364168272367639339349591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24971115392980371571598909 9364168272367639339349591)
  ·
    refine ⟨14046252408551459009024387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9364168272367639339349591 14046252408551459009024387)
    ·
      refine ⟨21069378612827188513536581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14046252408551459009024387 21069378612827188513536581)
      ·
        refine ⟨3950508489905097846288109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21069378612827188513536581 3950508489905097846288109)
        ·
          refine ⟨1481440683714411692358041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3950508489905097846288109 1481440683714411692358041)
          ·
            refine ⟨1111080512785808769268531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1481440683714411692358041 1111080512785808769268531)
            ·
              refine ⟨1666620769178713153902797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1111080512785808769268531 1666620769178713153902797)
              ·
                refine ⟨624982788442017432713549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1666620769178713153902797 624982788442017432713549)
                ·
                  refine ⟨234368545665756537267581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 624982788442017432713549 234368545665756537267581)
                  ·
                    rfl

theorem cell21_1026970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 3, 3].length) (baseStart_1026970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1026970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1026970 prefixEnd_1026970 := by exact prefixLift 1026970
  have htrace : WordTrace (prefixWord ++ tailWord_1026970) baseStart_1026970 baseEnd_1026970 := by
    simpa [prefixWord, tailWord_1026970, baseEnd_1026970] using wordTrace_append hprefix tailTrace_1026970
  have hstable : (prefixWord ++ tailWord_1026970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026970).length < 2 ^ (prefixWord ++ tailWord_1026970).sum := by decide
  have hdescent : baseEnd_1026970 < baseStart_1026970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027057 : List Nat := [1, 2, 2, 2, 4, 3, 1, 6]
def baseStart_1027057 : Nat := 118140960795 + 1027057 * 2 ^ 59
def prefixEnd_1027057 : Nat := 4983230072969 + 3 ^ 40 * 1027057 * 2
def baseEnd_1027057 : Nat := 78129466750354573105801

theorem tailTrace_1027057 : CollatzResearch.WordTrace tailWord_1027057 prefixEnd_1027057 78129466750354573105801 := by
  unfold tailWord_1027057
  simp only [CollatzResearch.WordTrace]
  refine ⟨37459846240155371215815425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24973230826770247477210283 37459846240155371215815425)
  ·
    refine ⟨28094884680116528411861569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37459846240155371215815425 28094884680116528411861569)
    ·
      refine ⟨21071163510087396308896177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28094884680116528411861569 21071163510087396308896177)
      ·
        refine ⟨15803372632565547231672133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21071163510087396308896177 15803372632565547231672133)
        ·
          refine ⟨2963132368606040105938525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15803372632565547231672133 2963132368606040105938525)
          ·
            refine ⟨1111174638227265039726947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2963132368606040105938525 1111174638227265039726947)
            ·
              refine ⟨1666761957340897559590421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1111174638227265039726947 1666761957340897559590421)
              ·
                refine ⟨78129466750354573105801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1666761957340897559590421 78129466750354573105801)
                ·
                  rfl

theorem cell21_1027057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 6].length) (baseStart_1027057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1027057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1027057 prefixEnd_1027057 := by exact prefixLift 1027057
  have htrace : WordTrace (prefixWord ++ tailWord_1027057) baseStart_1027057 baseEnd_1027057 := by
    simpa [prefixWord, tailWord_1027057, baseEnd_1027057] using wordTrace_append hprefix tailTrace_1027057
  have hstable : (prefixWord ++ tailWord_1027057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027057).length < 2 ^ (prefixWord ++ tailWord_1027057).sum := by decide
  have hdescent : baseEnd_1027057 < baseStart_1027057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027133 : List Nat := [1, 4, 1, 3, 1, 2, 4, 5]
def baseStart_1027133 : Nat := 118140960795 + 1027133 * 2 ^ 59
def prefixEnd_1027133 : Nat := 4983230072969 + 3 ^ 40 * 1027133 * 2
def baseEnd_1027133 : Nat := 78135248162168158683527

theorem tailTrace_1027133 : CollatzResearch.WordTrace tailWord_1027133 prefixEnd_1027133 78135248162168158683527 := by
  unfold tailWord_1027133
  simp only [CollatzResearch.WordTrace]
  refine ⟨37462618187880036195582053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24975078791920024130388035 37462618187880036195582053)
  ·
    refine ⟨7024240910227506786671635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37462618187880036195582053 7024240910227506786671635)
    ·
      refine ⟨10536361365341260180007453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7024240910227506786671635 10536361365341260180007453)
      ·
        refine ⟨3951135512002972567502795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10536361365341260180007453 3951135512002972567502795)
        ·
          refine ⟨5926703268004458851254193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3951135512002972567502795 5926703268004458851254193)
          ·
            refine ⟨4445027451003344138440645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5926703268004458851254193 4445027451003344138440645)
            ·
              refine ⟨833442647063127025957621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4445027451003344138440645 833442647063127025957621)
              ·
                refine ⟨78135248162168158683527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 833442647063127025957621 78135248162168158683527)
                ·
                  rfl

theorem cell21_1027133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 5].length) (baseStart_1027133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1027133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1027133 prefixEnd_1027133 := by exact prefixLift 1027133
  have htrace : WordTrace (prefixWord ++ tailWord_1027133) baseStart_1027133 baseEnd_1027133 := by
    simpa [prefixWord, tailWord_1027133, baseEnd_1027133] using wordTrace_append hprefix tailTrace_1027133
  have hstable : (prefixWord ++ tailWord_1027133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027133).length < 2 ^ (prefixWord ++ tailWord_1027133).sum := by decide
  have hdescent : baseEnd_1027133 < baseStart_1027133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027251 : List Nat := [1, 1, 1, 2, 3, 2, 2, 9]
def baseStart_1027251 : Nat := 118140960795 + 1027251 * 2 ^ 59
def prefixEnd_1027251 : Nat := 4983230072969 + 3 ^ 40 * 1027251 * 2
def baseEnd_1027251 : Nat := 78144224564720831027891

theorem tailTrace_1027251 : CollatzResearch.WordTrace tailWord_1027251 prefixEnd_1027251 78144224564720831027891 := by
  unfold tailWord_1027251
  simp only [CollatzResearch.WordTrace]
  refine ⟨37466922001452542348377607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24977948000968361565585071 37466922001452542348377607)
  ·
    refine ⟨56200383002178813522566411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37466922001452542348377607 56200383002178813522566411)
    ·
      refine ⟨84300574503268220283849617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56200383002178813522566411 84300574503268220283849617)
      ·
        refine ⟨63225430877451165212887213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84300574503268220283849617 63225430877451165212887213)
        ·
          refine ⟨23709536579044186954832705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63225430877451165212887213 23709536579044186954832705)
          ·
            refine ⟨17782152434283140216124529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23709536579044186954832705 17782152434283140216124529)
            ·
              refine ⟨13336614325712355162093397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17782152434283140216124529 13336614325712355162093397)
              ·
                refine ⟨78144224564720831027891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13336614325712355162093397 78144224564720831027891)
                ·
                  rfl

theorem cell21_1027251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 9].length) (baseStart_1027251 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1027251 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1027251 prefixEnd_1027251 := by exact prefixLift 1027251
  have htrace : WordTrace (prefixWord ++ tailWord_1027251) baseStart_1027251 baseEnd_1027251 := by
    simpa [prefixWord, tailWord_1027251, baseEnd_1027251] using wordTrace_append hprefix tailTrace_1027251
  have hstable : (prefixWord ++ tailWord_1027251).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027251).length < 2 ^ (prefixWord ++ tailWord_1027251).sum := by decide
  have hdescent : baseEnd_1027251 < baseStart_1027251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027327 : List Nat := [1, 1, 2, 2, 1, 5, 9]
def baseStart_1027327 : Nat := 118140960795 + 1027327 * 2 ^ 59
def prefixEnd_1027327 : Nat := 4983230072969 + 3 ^ 40 * 1027327 * 2
def baseEnd_1027327 : Nat := 26050001992178138868539

theorem tailTrace_1027327 : CollatzResearch.WordTrace tailWord_1027327 prefixEnd_1027327 26050001992178138868539 := by
  unfold tailWord_1027327
  simp only [CollatzResearch.WordTrace]
  refine ⟨37469693949177207328144235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24979795966118138218762823 37469693949177207328144235)
  ·
    refine ⟨56204540923765810992216353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37469693949177207328144235 56204540923765810992216353)
    ·
      refine ⟨42153405692824358244162265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56204540923765810992216353 42153405692824358244162265)
      ·
        refine ⟨31615054269618268683121699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42153405692824358244162265 31615054269618268683121699)
        ·
          refine ⟨47422581404427403024682549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31615054269618268683121699 47422581404427403024682549)
          ·
            refine ⟨4445867006665069033563989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47422581404427403024682549 4445867006665069033563989)
            ·
              refine ⟨26050001992178138868539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4445867006665069033563989 26050001992178138868539)
              ·
                rfl

theorem cell21_1027327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 9].length) (baseStart_1027327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1027327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1027327 prefixEnd_1027327 := by exact prefixLift 1027327
  have htrace : WordTrace (prefixWord ++ tailWord_1027327) baseStart_1027327 baseEnd_1027327 := by
    simpa [prefixWord, tailWord_1027327, baseEnd_1027327] using wordTrace_append hprefix tailTrace_1027327
  have hstable : (prefixWord ++ tailWord_1027327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027327).length < 2 ^ (prefixWord ++ tailWord_1027327).sum := by decide
  have hdescent : baseEnd_1027327 < baseStart_1027327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027375 : List Nat := [1, 1, 2, 1, 2, 1, 3, 7, 3]
def baseStart_1027375 : Nat := 118140960795 + 1027375 * 2 ^ 59
def prefixEnd_1027375 : Nat := 4983230072969 + 3 ^ 40 * 1027375 * 2
def baseEnd_1027375 : Nat := 234460972183565833016753

theorem tailTrace_1027375 : CollatzResearch.WordTrace tailWord_1027375 prefixEnd_1027375 234460972183565833016753 := by
  unfold tailWord_1027375
  simp only [CollatzResearch.WordTrace]
  refine ⟨37471444653003311525891579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24980963102002207683927719 37471444653003311525891579)
  ·
    refine ⟨56207166979504967288837369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37471444653003311525891579 56207166979504967288837369)
    ·
      refine ⟨42155375234628725466628027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56207166979504967288837369 42155375234628725466628027)
      ·
        refine ⟨63233062851943088199942041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42155375234628725466628027 63233062851943088199942041)
        ·
          refine ⟨47424797138957316149956531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63233062851943088199942041 47424797138957316149956531)
          ·
            refine ⟨71137195708435974224934797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47424797138957316149956531 71137195708435974224934797)
            ·
              refine ⟨26676448390663490334350549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71137195708435974224934797 26676448390663490334350549)
              ·
                refine ⟨625229259156175554711341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 26676448390663490334350549 625229259156175554711341)
                ·
                  refine ⟨234460972183565833016753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 625229259156175554711341 234460972183565833016753)
                  ·
                    rfl

theorem cell21_1027375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 7, 3].length) (baseStart_1027375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1027375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1027375 prefixEnd_1027375 := by exact prefixLift 1027375
  have htrace : WordTrace (prefixWord ++ tailWord_1027375) baseStart_1027375 baseEnd_1027375 := by
    simpa [prefixWord, tailWord_1027375, baseEnd_1027375] using wordTrace_append hprefix tailTrace_1027375
  have hstable : (prefixWord ++ tailWord_1027375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027375).length < 2 ^ (prefixWord ++ tailWord_1027375).sum := by decide
  have hdescent : baseEnd_1027375 < baseStart_1027375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027451 : List Nat := [1, 1, 1, 1, 1, 6, 1, 6, 3]
def baseStart_1027451 : Nat := 118140960795 + 1027451 * 2 ^ 59
def prefixEnd_1027451 : Nat := 4983230072969 + 3 ^ 40 * 1027451 * 2
def baseEnd_1027451 : Nat := 234478316419006589749931

theorem tailTrace_1027451 : CollatzResearch.WordTrace tailWord_1027451 prefixEnd_1027451 234478316419006589749931 := by
  unfold tailWord_1027451
  simp only [CollatzResearch.WordTrace]
  refine ⟨37474216600727976505658207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24982811067151984337105471 37474216600727976505658207)
  ·
    refine ⟨56211324901091964758487311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37474216600727976505658207 56211324901091964758487311)
    ·
      refine ⟨84316987351637947137730967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56211324901091964758487311 84316987351637947137730967)
      ·
        refine ⟨126475481027456920706596451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84316987351637947137730967 126475481027456920706596451)
        ·
          refine ⟨189713221541185381059894677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126475481027456920706596451 189713221541185381059894677)
          ·
            refine ⟨8892807259743064737182563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 189713221541185381059894677 8892807259743064737182563)
            ·
              refine ⟨13339210889614597105773845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8892807259743064737182563 13339210889614597105773845)
              ·
                refine ⟨625275510450684239333149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13339210889614597105773845 625275510450684239333149)
                ·
                  refine ⟨234478316419006589749931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 625275510450684239333149 234478316419006589749931)
                  ·
                    rfl

theorem cell21_1027451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 6, 3].length) (baseStart_1027451 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1027451 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1027451 prefixEnd_1027451 := by exact prefixLift 1027451
  have htrace : WordTrace (prefixWord ++ tailWord_1027451) baseStart_1027451 baseEnd_1027451 := by
    simpa [prefixWord, tailWord_1027451, baseEnd_1027451] using wordTrace_append hprefix tailTrace_1027451
  have hstable : (prefixWord ++ tailWord_1027451).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027451).length < 2 ^ (prefixWord ++ tailWord_1027451).sum := by decide
  have hdescent : baseEnd_1027451 < baseStart_1027451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027485 : List Nat := [1, 4, 2, 1, 3, 3, 1, 3, 3]
def baseStart_1027485 : Nat := 118140960795 + 1027485 * 2 ^ 59
def prefixEnd_1027485 : Nat := 4983230072969 + 3 ^ 40 * 1027485 * 2
def baseEnd_1027485 : Nat := 234486075682230086183195

theorem tailTrace_1027485 : CollatzResearch.WordTrace tailWord_1027485 prefixEnd_1027485 234486075682230086183195 := by
  unfold tailWord_1027485
  simp only [CollatzResearch.WordTrace]
  refine ⟨37475456682604800312395909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24983637788403200208263939 37475456682604800312395909)
  ·
    refine ⟨7026648127988400058574233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37475456682604800312395909 7026648127988400058574233)
    ·
      refine ⟨5269986095991300043930675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7026648127988400058574233 5269986095991300043930675)
      ·
        refine ⟨7904979143986950065896013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5269986095991300043930675 7904979143986950065896013)
        ·
          refine ⟨2964367178995106274711005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7904979143986950065896013 2964367178995106274711005)
          ·
            refine ⟨1111637692123164853016627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2964367178995106274711005 1111637692123164853016627)
            ·
              refine ⟨1667456538184747279524941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1111637692123164853016627 1667456538184747279524941)
              ·
                refine ⟨625296201819280229821853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1667456538184747279524941 625296201819280229821853)
                ·
                  refine ⟨234486075682230086183195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 625296201819280229821853 234486075682230086183195)
                  ·
                    rfl

theorem cell21_1027485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_1027485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1027485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1027485 prefixEnd_1027485 := by exact prefixLift 1027485
  have htrace : WordTrace (prefixWord ++ tailWord_1027485) baseStart_1027485 baseEnd_1027485 := by
    simpa [prefixWord, tailWord_1027485, baseEnd_1027485] using wordTrace_append hprefix tailTrace_1027485
  have hstable : (prefixWord ++ tailWord_1027485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027485).length < 2 ^ (prefixWord ++ tailWord_1027485).sum := by decide
  have hdescent : baseEnd_1027485 < baseStart_1027485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027516 : List Nat := [2, 2, 2, 4, 2, 2, 2, 1, 4]
def baseStart_1027516 : Nat := 118140960795 + 1027516 * 2 ^ 59
def prefixEnd_1027516 : Nat := 4983230072969 + 3 ^ 40 * 1027516 * 2
def baseEnd_1027516 : Nat := 234493150304580921166465

theorem tailTrace_1027516 : CollatzResearch.WordTrace tailWord_1027516 prefixEnd_1027516 234493150304580921166465 := by
  unfold tailWord_1027516
  simp only [CollatzResearch.WordTrace]
  refine ⟨18738293672746246303387201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24984391563661661737849601 18738293672746246303387201)
  ·
    refine ⟨14053720254559684727540401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18738293672746246303387201 14053720254559684727540401)
    ·
      refine ⟨10540290190919763545655301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14053720254559684727540401 10540290190919763545655301)
      ·
        refine ⟨1976304410797455664810369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10540290190919763545655301 1976304410797455664810369)
        ·
          refine ⟨1482228308098091748607777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1976304410797455664810369 1482228308098091748607777)
          ·
            refine ⟨1111671231073568811455833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1482228308098091748607777 1111671231073568811455833)
            ·
              refine ⟨833753423305176608591875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1111671231073568811455833 833753423305176608591875)
              ·
                refine ⟨1250630134957764912887813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 833753423305176608591875 1250630134957764912887813)
                ·
                  refine ⟨234493150304580921166465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1250630134957764912887813 234493150304580921166465)
                  ·
                    rfl

theorem cell21_1027516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_1027516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1027516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1027516 prefixEnd_1027516 := by exact prefixLift 1027516
  have htrace : WordTrace (prefixWord ++ tailWord_1027516) baseStart_1027516 baseEnd_1027516 := by
    simpa [prefixWord, tailWord_1027516, baseEnd_1027516] using wordTrace_append hprefix tailTrace_1027516
  have hstable : (prefixWord ++ tailWord_1027516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027516).length < 2 ^ (prefixWord ++ tailWord_1027516).sum := by decide
  have hdescent : baseEnd_1027516 < baseStart_1027516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027555 : List Nat := [1, 1, 1, 6, 2, 10]
def baseStart_1027555 : Nat := 118140960795 + 1027555 * 2 ^ 59
def prefixEnd_1027555 : Nat := 4983230072969 + 3 ^ 40 * 1027555 * 2
def baseEnd_1027555 : Nat := 8685261134663908148755

theorem tailTrace_1027555 : CollatzResearch.WordTrace tailWord_1027555 prefixEnd_1027555 8685261134663908148755 := by
  unfold tailWord_1027555
  simp only [CollatzResearch.WordTrace]
  refine ⟨37478009792351202267444119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24985339861567468178296079 37478009792351202267444119)
  ·
    refine ⟨56217014688526803401166179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37478009792351202267444119 56217014688526803401166179)
    ·
      refine ⟨84325522032790205101749269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56217014688526803401166179 84325522032790205101749269)
      ·
        refine ⟨3952758845287040864144497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 84325522032790205101749269 3952758845287040864144497)
        ·
          refine ⟨2964569133965280648108373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3952758845287040864144497 2964569133965280648108373)
          ·
            refine ⟨8685261134663908148755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2964569133965280648108373 8685261134663908148755)
            ·
              rfl

theorem cell21_1027555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 10].length) (baseStart_1027555 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1027555 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1027555 prefixEnd_1027555 := by exact prefixLift 1027555
  have htrace : WordTrace (prefixWord ++ tailWord_1027555) baseStart_1027555 baseEnd_1027555 := by
    simpa [prefixWord, tailWord_1027555, baseEnd_1027555] using wordTrace_append hprefix tailTrace_1027555
  have hstable : (prefixWord ++ tailWord_1027555).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027555).length < 2 ^ (prefixWord ++ tailWord_1027555).sum := by decide
  have hdescent : baseEnd_1027555 < baseStart_1027555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027603 : List Nat := [1, 1, 1, 2, 1, 6, 1, 5, 3]
def baseStart_1027603 : Nat := 118140960795 + 1027603 * 2 ^ 59
def prefixEnd_1027603 : Nat := 4983230072969 + 3 ^ 40 * 1027603 * 2
def baseEnd_1027603 : Nat := 234513004889888103216287

theorem tailTrace_1027603 : CollatzResearch.WordTrace tailWord_1027603 prefixEnd_1027603 234513004889888103216287 := by
  unfold tailWord_1027603
  simp only [CollatzResearch.WordTrace]
  refine ⟨37479760496177306465191463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24986506997451537643460975 37479760496177306465191463)
  ·
    refine ⟨56219640744265959697787195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37479760496177306465191463 56219640744265959697787195)
    ·
      refine ⟨84329461116398939546680793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56219640744265959697787195 84329461116398939546680793)
      ·
        refine ⟨63247095837299204660010595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84329461116398939546680793 63247095837299204660010595)
        ·
          refine ⟨94870643755948806990015893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63247095837299204660010595 94870643755948806990015893)
          ·
            refine ⟨4447061426060100327656995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 94870643755948806990015893 4447061426060100327656995)
            ·
              refine ⟨6670592139090150491485493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4447061426060100327656995 6670592139090150491485493)
              ·
                refine ⟨625368013039701608576765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6670592139090150491485493 625368013039701608576765)
                ·
                  refine ⟨234513004889888103216287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 625368013039701608576765 234513004889888103216287)
                  ·
                    rfl

theorem cell21_1027603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 5, 3].length) (baseStart_1027603 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1027603 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1027603 prefixEnd_1027603 := by exact prefixLift 1027603
  have htrace : WordTrace (prefixWord ++ tailWord_1027603) baseStart_1027603 baseEnd_1027603 := by
    simpa [prefixWord, tailWord_1027603, baseEnd_1027603] using wordTrace_append hprefix tailTrace_1027603
  have hstable : (prefixWord ++ tailWord_1027603).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027603).length < 2 ^ (prefixWord ++ tailWord_1027603).sum := by decide
  have hdescent : baseEnd_1027603 < baseStart_1027603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027617 : List Nat := [1, 2, 3, 2, 2, 3, 1, 1, 6]
def baseStart_1027617 : Nat := 118140960795 + 1027617 * 2 ^ 59
def prefixEnd_1027617 : Nat := 4983230072969 + 3 ^ 40 * 1027617 * 2
def baseEnd_1027617 : Nat := 234516199880627189982925

theorem tailTrace_1027617 : CollatzResearch.WordTrace tailWord_1027617 prefixEnd_1027617 234516199880627189982925 := by
  unfold tailWord_1027617
  simp only [CollatzResearch.WordTrace]
  refine ⟨37480271118126586856201105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24986847412084391237467403 37480271118126586856201105)
  ·
    refine ⟨28110203338594940142150829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37480271118126586856201105 28110203338594940142150829)
    ·
      refine ⟨10541326251973102553306561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28110203338594940142150829 10541326251973102553306561)
      ·
        refine ⟨7905994688979826914979921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10541326251973102553306561 7905994688979826914979921)
        ·
          refine ⟨5929496016734870186234941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7905994688979826914979921 5929496016734870186234941)
          ·
            refine ⟨2223561006275576319838103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5929496016734870186234941 2223561006275576319838103)
            ·
              refine ⟨3335341509413364479757155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2223561006275576319838103 3335341509413364479757155)
              ·
                refine ⟨5003012264120046719635733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3335341509413364479757155 5003012264120046719635733)
                ·
                  refine ⟨234516199880627189982925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5003012264120046719635733 234516199880627189982925)
                  ·
                    rfl

theorem cell21_1027617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 6].length) (baseStart_1027617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1027617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1027617 prefixEnd_1027617 := by exact prefixLift 1027617
  have htrace : WordTrace (prefixWord ++ tailWord_1027617) baseStart_1027617 baseEnd_1027617 := by
    simpa [prefixWord, tailWord_1027617, baseEnd_1027617] using wordTrace_append hprefix tailTrace_1027617
  have hstable : (prefixWord ++ tailWord_1027617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027617).length < 2 ^ (prefixWord ++ tailWord_1027617).sum := by decide
  have hdescent : baseEnd_1027617 < baseStart_1027617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027730 : List Nat := [3, 2, 3, 1, 3, 2, 2, 2, 3]
def baseStart_1027730 : Nat := 118140960795 + 1027730 * 2 ^ 59
def prefixEnd_1027730 : Nat := 4983230072969 + 3 ^ 40 * 1027730 * 2
def baseEnd_1027730 : Nat := 234541988020164104599361

theorem tailTrace_1027730 : CollatzResearch.WordTrace tailWord_1027730 prefixEnd_1027730 234541988020164104599361 := by
  unfold tailWord_1027730
  simp only [CollatzResearch.WordTrace]
  refine ⟨9371098141679301788766161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24989595044478138103376429 9371098141679301788766161)
  ·
    refine ⟨7028323606259476341574621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9371098141679301788766161 7028323606259476341574621)
    ·
      refine ⟨2635621352347303628090483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7028323606259476341574621 2635621352347303628090483)
      ·
        refine ⟨3953432028520955442135725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2635621352347303628090483 3953432028520955442135725)
        ·
          refine ⟨1482537010695358290800897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3953432028520955442135725 1482537010695358290800897)
          ·
            refine ⟨1111902758021518718100673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1482537010695358290800897 1111902758021518718100673)
            ·
              refine ⟨833927068516139038575505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1111902758021518718100673 833927068516139038575505)
              ·
                refine ⟨625445301387104278931629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 833927068516139038575505 625445301387104278931629)
                ·
                  refine ⟨234541988020164104599361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 625445301387104278931629 234541988020164104599361)
                  ·
                    rfl

theorem cell21_1027730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_1027730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1027730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1027730 prefixEnd_1027730 := by exact prefixLift 1027730
  have htrace : WordTrace (prefixWord ++ tailWord_1027730) baseStart_1027730 baseEnd_1027730 := by
    simpa [prefixWord, tailWord_1027730, baseEnd_1027730] using wordTrace_append hprefix tailTrace_1027730
  have hstable : (prefixWord ++ tailWord_1027730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027730).length < 2 ^ (prefixWord ++ tailWord_1027730).sum := by decide
  have hdescent : baseEnd_1027730 < baseStart_1027730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027758 : List Nat := [4, 1, 4, 1, 2, 1, 3, 5]
def baseStart_1027758 : Nat := 118140960795 + 1027758 * 2 ^ 59
def prefixEnd_1027758 : Nat := 4983230072969 + 3 ^ 40 * 1027758 * 2
def baseEnd_1027758 : Nat := 78182792667214092710879

theorem tailTrace_1027758 : CollatzResearch.WordTrace tailWord_1027758 prefixEnd_1027758 78182792667214092710879 := by
  unfold tailWord_1027758
  simp only [CollatzResearch.WordTrace]
  refine ⟨4685676726326970992135491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24990275873743845291389285 4685676726326970992135491)
  ·
    refine ⟨7028515089490456488203237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4685676726326970992135491 7028515089490456488203237)
    ·
      refine ⟨1317846579279460591538107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7028515089490456488203237 1317846579279460591538107)
      ·
        refine ⟨1976769868919190887307161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1317846579279460591538107 1976769868919190887307161)
        ·
          refine ⟨1482577401689393165480371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1976769868919190887307161 1482577401689393165480371)
          ·
            refine ⟨2223866102534089748220557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1482577401689393165480371 2223866102534089748220557)
            ·
              refine ⟨833949788450283655582709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2223866102534089748220557 833949788450283655582709)
              ·
                refine ⟨78182792667214092710879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 833949788450283655582709 78182792667214092710879)
                ·
                  rfl

theorem cell21_1027758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_1027758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1027758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1027758 prefixEnd_1027758 := by exact prefixLift 1027758
  have htrace : WordTrace (prefixWord ++ tailWord_1027758) baseStart_1027758 baseEnd_1027758 := by
    simpa [prefixWord, tailWord_1027758, baseEnd_1027758] using wordTrace_append hprefix tailTrace_1027758
  have hstable : (prefixWord ++ tailWord_1027758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027758).length < 2 ^ (prefixWord ++ tailWord_1027758).sum := by decide
  have hdescent : baseEnd_1027758 < baseStart_1027758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027772 : List Nat := [2, 2, 2, 3, 1, 3, 2, 3, 3]
def baseStart_1027772 : Nat := 118140960795 + 1027772 * 2 ^ 59
def prefixEnd_1027772 : Nat := 4983230072969 + 3 ^ 40 * 1027772 * 2
def baseEnd_1027772 : Nat := 234551572992381364899275

theorem tailTrace_1027772 : CollatzResearch.WordTrace tailWord_1027772 prefixEnd_1027772 234551572992381364899275 := by
  unfold tailWord_1027772
  simp only [CollatzResearch.WordTrace]
  refine ⟨18742962216282524164046785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24990616288376698885395713 18742962216282524164046785)
  ·
    refine ⟨14057221662211893123035089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18742962216282524164046785 14057221662211893123035089)
    ·
      refine ⟨10542916246658919842276317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14057221662211893123035089 10542916246658919842276317)
      ·
        refine ⟨3953593592497094940853619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10542916246658919842276317 3953593592497094940853619)
        ·
          refine ⟨5930390388745642411280429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3953593592497094940853619 5930390388745642411280429)
          ·
            refine ⟨2223896395779615904230161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5930390388745642411280429 2223896395779615904230161)
            ·
              refine ⟨1667922296834711928172621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2223896395779615904230161 1667922296834711928172621)
              ·
                refine ⟨625470861313016973064733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1667922296834711928172621 625470861313016973064733)
                ·
                  refine ⟨234551572992381364899275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 625470861313016973064733 234551572992381364899275)
                  ·
                    rfl

theorem cell21_1027772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 3, 3].length) (baseStart_1027772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1027772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1027772 prefixEnd_1027772 := by exact prefixLift 1027772
  have htrace : WordTrace (prefixWord ++ tailWord_1027772) baseStart_1027772 baseEnd_1027772 := by
    simpa [prefixWord, tailWord_1027772, baseEnd_1027772] using wordTrace_append hprefix tailTrace_1027772
  have hstable : (prefixWord ++ tailWord_1027772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027772).length < 2 ^ (prefixWord ++ tailWord_1027772).sum := by decide
  have hdescent : baseEnd_1027772 < baseStart_1027772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027778 : List Nat := [3, 5, 1, 2, 2, 1, 1, 2, 4]
def baseStart_1027778 : Nat := 118140960795 + 1027778 * 2 ^ 59
def prefixEnd_1027778 : Nat := 4983230072969 + 3 ^ 40 * 1027778 * 2
def baseEnd_1027778 : Nat := 234552942274126687799263

theorem tailTrace_1027778 : CollatzResearch.WordTrace tailWord_1027778 prefixEnd_1027778 234552942274126687799263 := by
  unfold tailWord_1027778
  simp only [CollatzResearch.WordTrace]
  refine ⟨9371535817635827838202997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24990762180362207568541325 9371535817635827838202997)
  ·
    refine ⟨878581482903358859831531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9371535817635827838202997 878581482903358859831531)
    ·
      refine ⟨1317872224355038289747297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 878581482903358859831531 1317872224355038289747297)
      ·
        refine ⟨988404168266278717310473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1317872224355038289747297 988404168266278717310473)
        ·
          refine ⟨741303126199709037982855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 988404168266278717310473 741303126199709037982855)
          ·
            refine ⟨1111954689299563556974283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741303126199709037982855 1111954689299563556974283)
            ·
              refine ⟨1667932033949345335461425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1111954689299563556974283 1667932033949345335461425)
              ·
                refine ⟨1250949025462009001596069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1667932033949345335461425 1250949025462009001596069)
                ·
                  refine ⟨234552942274126687799263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1250949025462009001596069 234552942274126687799263)
                  ·
                    rfl

theorem cell21_1027778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_1027778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1027778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1027778 prefixEnd_1027778 := by exact prefixLift 1027778
  have htrace : WordTrace (prefixWord ++ tailWord_1027778) baseStart_1027778 baseEnd_1027778 := by
    simpa [prefixWord, tailWord_1027778, baseEnd_1027778] using wordTrace_append hprefix tailTrace_1027778
  have hstable : (prefixWord ++ tailWord_1027778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027778).length < 2 ^ (prefixWord ++ tailWord_1027778).sum := by decide
  have hdescent : baseEnd_1027778 < baseStart_1027778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027789 : List Nat := [1, 6, 2, 1, 1, 1, 2, 4, 3]
def baseStart_1027789 : Nat := 118140960795 + 1027789 * 2 ^ 59
def prefixEnd_1027789 : Nat := 4983230072969 + 3 ^ 40 * 1027789 * 2
def baseEnd_1027789 : Nat := 234555452623993113115907

theorem tailTrace_1027789 : CollatzResearch.WordTrace tailWord_1027789 prefixEnd_1027789 234555452623993113115907 := by
  unfold tailWord_1027789
  simp only [CollatzResearch.WordTrace]
  refine ⟨37486544473503460231462421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24991029649002306820974947 37486544473503460231462421)
  ·
    refine ⟨1757181772195474698349801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37486544473503460231462421 1757181772195474698349801)
    ·
      refine ⟨1317886329146606023762351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1757181772195474698349801 1317886329146606023762351)
      ·
        refine ⟨1976829493719909035643527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1317886329146606023762351 1976829493719909035643527)
        ·
          refine ⟨2965244240579863553465291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1976829493719909035643527 2965244240579863553465291)
          ·
            refine ⟨4447866360869795330197937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2965244240579863553465291 4447866360869795330197937)
            ·
              refine ⟨3335899770652346497648453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4447866360869795330197937 3335899770652346497648453)
              ·
                refine ⟨625481206997314968309085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3335899770652346497648453 625481206997314968309085)
                ·
                  refine ⟨234555452623993113115907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 625481206997314968309085 234555452623993113115907)
                  ·
                    rfl

theorem cell21_1027789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_1027789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1027789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1027789 prefixEnd_1027789 := by exact prefixLift 1027789
  have htrace : WordTrace (prefixWord ++ tailWord_1027789) baseStart_1027789 baseEnd_1027789 := by
    simpa [prefixWord, tailWord_1027789, baseEnd_1027789] using wordTrace_append hprefix tailTrace_1027789
  have hstable : (prefixWord ++ tailWord_1027789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027789).length < 2 ^ (prefixWord ++ tailWord_1027789).sum := by decide
  have hdescent : baseEnd_1027789 < baseStart_1027789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027831 : List Nat := [1, 1, 3, 1, 1, 1, 7, 3, 3]
def baseStart_1027831 : Nat := 118140960795 + 1027831 * 2 ^ 59
def prefixEnd_1027831 : Nat := 4983230072969 + 3 ^ 40 * 1027831 * 2
def baseEnd_1027831 : Nat := 234565037596210373415821

theorem tailTrace_1027831 : CollatzResearch.WordTrace tailWord_1027831 prefixEnd_1027831 234565037596210373415821 := by
  unfold tailWord_1027831
  simp only [CollatzResearch.WordTrace]
  refine ⟨37488076339351301404491347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24992050892900867602994231 37488076339351301404491347)
  ·
    refine ⟨56232114509026952106737021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37488076339351301404491347 56232114509026952106737021)
    ·
      refine ⟨21087042940885107040026383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56232114509026952106737021 21087042940885107040026383)
      ·
        refine ⟨31630564411327660560039575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21087042940885107040026383 31630564411327660560039575)
        ·
          refine ⟨47445846616991490840059363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31630564411327660560039575 47445846616991490840059363)
          ·
            refine ⟨71168769925487236260089045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47445846616991490840059363 71168769925487236260089045)
            ·
              refine ⟨1668018045128607099845837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 71168769925487236260089045 1668018045128607099845837)
              ·
                refine ⟨625506766923227662442189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1668018045128607099845837 625506766923227662442189)
                ·
                  refine ⟨234565037596210373415821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 625506766923227662442189 234565037596210373415821)
                  ·
                    rfl

theorem cell21_1027831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 3, 3].length) (baseStart_1027831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1027831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1027831 prefixEnd_1027831 := by exact prefixLift 1027831
  have htrace : WordTrace (prefixWord ++ tailWord_1027831) baseStart_1027831 baseEnd_1027831 := by
    simpa [prefixWord, tailWord_1027831, baseEnd_1027831] using wordTrace_append hprefix tailTrace_1027831
  have hstable : (prefixWord ++ tailWord_1027831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027831).length < 2 ^ (prefixWord ++ tailWord_1027831).sum := by decide
  have hdescent : baseEnd_1027831 < baseStart_1027831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027848 : List Nat := [2, 1, 3, 2, 2, 1, 5, 2, 3]
def baseStart_1027848 : Nat := 118140960795 + 1027848 * 2 ^ 59
def prefixEnd_1027848 : Nat := 4983230072969 + 3 ^ 40 * 1027848 * 2
def baseEnd_1027848 : Nat := 234568917227822121632453

theorem tailTrace_1027848 : CollatzResearch.WordTrace tailWord_1027848 prefixEnd_1027848 234568917227822121632453 := by
  unfold tailWord_1027848
  simp only [CollatzResearch.WordTrace]
  refine ⟨18744348190144856653930099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24992464253526475538573465 18744348190144856653930099)
  ·
    refine ⟨28116522285217284980895149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18744348190144856653930099 28116522285217284980895149)
    ·
      refine ⟨10543695856956481867835681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28116522285217284980895149 10543695856956481867835681)
      ·
        refine ⟨7907771892717361400876761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10543695856956481867835681 7907771892717361400876761)
        ·
          refine ⟨5930828919538021050657571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7907771892717361400876761 5930828919538021050657571)
          ·
            refine ⟨8896243379307031575986357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5930828919538021050657571 8896243379307031575986357)
            ·
              refine ⟨834022816810034210248721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8896243379307031575986357 834022816810034210248721)
              ·
                refine ⟨625517112607525657686541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 834022816810034210248721 625517112607525657686541)
                ·
                  refine ⟨234568917227822121632453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 625517112607525657686541 234568917227822121632453)
                  ·
                    rfl

theorem cell21_1027848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 2, 3].length) (baseStart_1027848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1027848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1027848 prefixEnd_1027848 := by exact prefixLift 1027848
  have htrace : WordTrace (prefixWord ++ tailWord_1027848) baseStart_1027848 baseEnd_1027848 := by
    simpa [prefixWord, tailWord_1027848, baseEnd_1027848] using wordTrace_append hprefix tailTrace_1027848
  have hstable : (prefixWord ++ tailWord_1027848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027848).length < 2 ^ (prefixWord ++ tailWord_1027848).sum := by decide
  have hdescent : baseEnd_1027848 < baseStart_1027848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027907 : List Nat := [1, 1, 1, 3, 1, 6, 1, 4, 3]
def baseStart_1027907 : Nat := 118140960795 + 1027907 * 2 ^ 59
def prefixEnd_1027907 : Nat := 4983230072969 + 3 ^ 40 * 1027907 * 2
def baseEnd_1027907 : Nat := 234582381831651130148999

theorem tailTrace_1027907 : CollatzResearch.WordTrace tailWord_1027907 prefixEnd_1027907 234582381831651130148999 := by
  unfold tailWord_1027907
  simp only [CollatzResearch.WordTrace]
  refine ⟨37490848287075966384257975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24993898858050644256171983 37490848287075966384257975)
  ·
    refine ⟨56236272430613949576386963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37490848287075966384257975 56236272430613949576386963)
    ·
      refine ⟨84354408645920924364580445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56236272430613949576386963 84354408645920924364580445)
      ·
        refine ⟨31632903242220346636717667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84354408645920924364580445 31632903242220346636717667)
        ·
          refine ⟨47449354863330519955076501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31632903242220346636717667 47449354863330519955076501)
          ·
            refine ⟨2224188509218618122894211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47449354863330519955076501 2224188509218618122894211)
            ·
              refine ⟨3336282763827927184341317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2224188509218618122894211 3336282763827927184341317)
              ·
                refine ⟨625553018217736347063997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3336282763827927184341317 625553018217736347063997)
                ·
                  refine ⟨234582381831651130148999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 625553018217736347063997 234582381831651130148999)
                  ·
                    rfl

theorem cell21_1027907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4, 3].length) (baseStart_1027907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1027907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1027907 prefixEnd_1027907 := by exact prefixLift 1027907
  have htrace : WordTrace (prefixWord ++ tailWord_1027907) baseStart_1027907 baseEnd_1027907 := by
    simpa [prefixWord, tailWord_1027907, baseEnd_1027907] using wordTrace_append hprefix tailTrace_1027907
  have hstable : (prefixWord ++ tailWord_1027907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027907).length < 2 ^ (prefixWord ++ tailWord_1027907).sum := by decide
  have hdescent : baseEnd_1027907 < baseStart_1027907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027910 : List Nat := [6, 1, 1, 2, 1, 3, 1, 6]
def baseStart_1027910 : Nat := 118140960795 + 1027910 * 2 ^ 59
def prefixEnd_1027910 : Nat := 4983230072969 + 3 ^ 40 * 1027910 * 2
def baseEnd_1027910 : Nat := 78194355490841263866331

theorem tailTrace_1027910 : CollatzResearch.WordTrace tailWord_1027910 prefixEnd_1027910 78194355490841263866331 := by
  unfold tailWord_1027910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1171592428314534309269287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24993971804043398597744789 1171592428314534309269287)
  ·
    refine ⟨1757388642471801463903931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1171592428314534309269287 1757388642471801463903931)
    ·
      refine ⟨2636082963707702195855897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1757388642471801463903931 2636082963707702195855897)
      ·
        refine ⟨1977062222780776646891923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2636082963707702195855897 1977062222780776646891923)
        ·
          refine ⟨2965593334171164970337885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1977062222780776646891923 2965593334171164970337885)
          ·
            refine ⟨1112097500314186863876707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2965593334171164970337885 1112097500314186863876707)
            ·
              refine ⟨1668146250471280295815061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1112097500314186863876707 1668146250471280295815061)
              ·
                refine ⟨78194355490841263866331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1668146250471280295815061 78194355490841263866331)
                ·
                  rfl

theorem cell21_1027910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_1027910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1027910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1027910 prefixEnd_1027910 := by exact prefixLift 1027910
  have htrace : WordTrace (prefixWord ++ tailWord_1027910) baseStart_1027910 baseEnd_1027910 := by
    simpa [prefixWord, tailWord_1027910, baseEnd_1027910] using wordTrace_append hprefix tailTrace_1027910
  have hstable : (prefixWord ++ tailWord_1027910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027910).length < 2 ^ (prefixWord ++ tailWord_1027910).sum := by decide
  have hdescent : baseEnd_1027910 < baseStart_1027910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027921 : List Nat := [1, 2, 2, 1, 5, 1, 2, 3, 4]
def baseStart_1027921 : Nat := 118140960795 + 1027921 * 2 ^ 59
def prefixEnd_1027921 : Nat := 4983230072969 + 3 ^ 40 * 1027921 * 2
def baseEnd_1027921 : Nat := 234585576822390216915637

theorem tailTrace_1027921 : CollatzResearch.WordTrace tailWord_1027921 prefixEnd_1027921 234585576822390216915637 := by
  unfold tailWord_1027921
  simp only [CollatzResearch.WordTrace]
  refine ⟨37491358909025246775267617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24994239272683497850178411 37491358909025246775267617)
  ·
    refine ⟨28118519181768935081450713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37491358909025246775267617 28118519181768935081450713)
    ·
      refine ⟨21088889386326701311088035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28118519181768935081450713 21088889386326701311088035)
      ·
        refine ⟨31633334079490051966632053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21088889386326701311088035 31633334079490051966632053)
        ·
          refine ⟨2965625069952192371871755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31633334079490051966632053 2965625069952192371871755)
          ·
            refine ⟨4448437604928288557807633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2965625069952192371871755 4448437604928288557807633)
            ·
              refine ⟨3336328203696216418355725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4448437604928288557807633 3336328203696216418355725)
              ·
                refine ⟨1251123076386081156883397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3336328203696216418355725 1251123076386081156883397)
                ·
                  refine ⟨234585576822390216915637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1251123076386081156883397 234585576822390216915637)
                  ·
                    rfl

theorem cell21_1027921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 4].length) (baseStart_1027921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1027921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1027921 prefixEnd_1027921 := by exact prefixLift 1027921
  have htrace : WordTrace (prefixWord ++ tailWord_1027921) baseStart_1027921 baseEnd_1027921 := by
    simpa [prefixWord, tailWord_1027921, baseEnd_1027921] using wordTrace_append hprefix tailTrace_1027921
  have hstable : (prefixWord ++ tailWord_1027921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027921).length < 2 ^ (prefixWord ++ tailWord_1027921).sum := by decide
  have hdescent : baseEnd_1027921 < baseStart_1027921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028101 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 7]
def baseStart_1028101 : Nat := 118140960795 + 1028101 * 2 ^ 59
def prefixEnd_1028101 : Nat := 4983230072969 + 3 ^ 40 * 1028101 * 2
def baseEnd_1028101 : Nat := 234626655274749903915269

theorem tailTrace_1028101 : CollatzResearch.WordTrace tailWord_1028101 prefixEnd_1028101 234626655274749903915269 := by
  unfold tailWord_1028101
  simp only [CollatzResearch.WordTrace]
  refine ⟨37497924048373137516820157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24998616032248758344546771 37497924048373137516820157)
  ·
    refine ⟨14061721518139926568807559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37497924048373137516820157 14061721518139926568807559)
    ·
      refine ⟨21092582277209889853211339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14061721518139926568807559 21092582277209889853211339)
      ·
        refine ⟨31638873415814834779817009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21092582277209889853211339 31638873415814834779817009)
        ·
          refine ⟨23729155061861126084862757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31638873415814834779817009 23729155061861126084862757)
          ·
            refine ⟨4449216574098961140911767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23729155061861126084862757 4449216574098961140911767)
            ·
              refine ⟨6673824861148441711367651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4449216574098961140911767 6673824861148441711367651)
              ·
                refine ⟨10010737291722662567051477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6673824861148441711367651 10010737291722662567051477)
                ·
                  refine ⟨234626655274749903915269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10010737291722662567051477 234626655274749903915269)
                  ·
                    rfl

theorem cell21_1028101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_1028101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1028101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1028101 prefixEnd_1028101 := by exact prefixLift 1028101
  have htrace : WordTrace (prefixWord ++ tailWord_1028101) baseStart_1028101 baseEnd_1028101 := by
    simpa [prefixWord, tailWord_1028101, baseEnd_1028101] using wordTrace_append hprefix tailTrace_1028101
  have hstable : (prefixWord ++ tailWord_1028101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028101).length < 2 ^ (prefixWord ++ tailWord_1028101).sum := by decide
  have hdescent : baseEnd_1028101 < baseStart_1028101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028298 : List Nat := [3, 1, 2, 1, 3, 1, 10]
def baseStart_1028298 : Nat := 118140960795 + 1028298 * 2 ^ 59
def prefixEnd_1028298 : Nat := 4983230072969 + 3 ^ 40 * 1028298 * 2
def baseEnd_1028298 : Nat := 26074623706524593236837

theorem tailTrace_1028298 : CollatzResearch.WordTrace tailWord_1028298 prefixEnd_1028298 26074623706524593236837 := by
  unfold tailWord_1028298
  simp only [CollatzResearch.WordTrace]
  refine ⟨9376277307164860040435387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25003406152439626774494365 9376277307164860040435387)
  ·
    refine ⟨14064415960747290060653081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9376277307164860040435387 14064415960747290060653081)
    ·
      refine ⟨10548311970560467545489811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14064415960747290060653081 10548311970560467545489811)
      ·
        refine ⟨15822467955840701318234717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10548311970560467545489811 15822467955840701318234717)
        ·
          refine ⟨5933425483440262994338019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15822467955840701318234717 5933425483440262994338019)
          ·
            refine ⟨8900138225160394491507029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5933425483440262994338019 8900138225160394491507029)
            ·
              refine ⟨26074623706524593236837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8900138225160394491507029 26074623706524593236837)
              ·
                rfl

theorem cell21_1028298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 10].length) (baseStart_1028298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1028298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1028298 prefixEnd_1028298 := by exact prefixLift 1028298
  have htrace : WordTrace (prefixWord ++ tailWord_1028298) baseStart_1028298 baseEnd_1028298 := by
    simpa [prefixWord, tailWord_1028298, baseEnd_1028298] using wordTrace_append hprefix tailTrace_1028298
  have hstable : (prefixWord ++ tailWord_1028298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028298).length < 2 ^ (prefixWord ++ tailWord_1028298).sum := by decide
  have hdescent : baseEnd_1028298 < baseStart_1028298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028360 : List Nat := [2, 1, 3, 2, 3, 1, 2, 1, 6]
def baseStart_1028360 : Nat := 118140960795 + 1028360 * 2 ^ 59
def prefixEnd_1028360 : Nat := 4983230072969 + 3 ^ 40 * 1028360 * 2
def baseEnd_1028360 : Nat := 234685762603423009098073

theorem tailTrace_1028360 : CollatzResearch.WordTrace tailWord_1028360 prefixEnd_1028360 234685762603423009098073 := by
  unfold tailWord_1028360
  simp only [CollatzResearch.WordTrace]
  refine ⟨18753685277217412375249267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25004913702956549833665689 18753685277217412375249267)
  ·
    refine ⟨28130527915826118562873901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18753685277217412375249267 28130527915826118562873901)
    ·
      refine ⟨10548947968434794461077713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28130527915826118562873901 10548947968434794461077713)
      ·
        refine ⟨7911710976326095845808285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10548947968434794461077713 7911710976326095845808285)
        ·
          refine ⟨2966891616122285942178107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7911710976326095845808285 2966891616122285942178107)
          ·
            refine ⟨4450337424183428913267161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2966891616122285942178107 4450337424183428913267161)
            ·
              refine ⟨3337753068137571684950371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4450337424183428913267161 3337753068137571684950371)
              ·
                refine ⟨5006629602206357527425557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3337753068137571684950371 5006629602206357527425557)
                ·
                  refine ⟨234685762603423009098073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5006629602206357527425557 234685762603423009098073)
                  ·
                    rfl

theorem cell21_1028360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 6].length) (baseStart_1028360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1028360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1028360 prefixEnd_1028360 := by exact prefixLift 1028360
  have htrace : WordTrace (prefixWord ++ tailWord_1028360) baseStart_1028360 baseEnd_1028360 := by
    simpa [prefixWord, tailWord_1028360, baseEnd_1028360] using wordTrace_append hprefix tailTrace_1028360
  have hstable : (prefixWord ++ tailWord_1028360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028360).length < 2 ^ (prefixWord ++ tailWord_1028360).sum := by decide
  have hdescent : baseEnd_1028360 < baseStart_1028360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028363 : List Nat := [1, 1, 1, 1, 5, 2, 5, 2, 3]
def baseStart_1028363 : Nat := 118140960795 + 1028363 * 2 ^ 59
def prefixEnd_1028363 : Nat := 4983230072969 + 3 ^ 40 * 1028363 * 2
def baseEnd_1028363 : Nat := 234686447244295670548067

theorem tailTrace_1028363 : CollatzResearch.WordTrace tailWord_1028363 prefixEnd_1028363 234686447244295670548067 := by
  unfold tailWord_1028363
  simp only [CollatzResearch.WordTrace]
  refine ⟨37507479973423956262857743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25004986648949304175238495 37507479973423956262857743)
  ·
    refine ⟨56261219960135934394286615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37507479973423956262857743 56261219960135934394286615)
    ·
      refine ⟨84391829940203901591429923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56261219960135934394286615 84391829940203901591429923)
      ·
        refine ⟨126587744910305852387144885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84391829940203901591429923 126587744910305852387144885)
        ·
          refine ⟨11867601085341173661294833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126587744910305852387144885 11867601085341173661294833)
          ·
            refine ⟨8900700814005880245971125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11867601085341173661294833 8900700814005880245971125)
            ·
              refine ⟨834440701313051273059793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8900700814005880245971125 834440701313051273059793)
              ·
                refine ⟨625830525984788454794845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 834440701313051273059793 625830525984788454794845)
                ·
                  refine ⟨234686447244295670548067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 625830525984788454794845 234686447244295670548067)
                  ·
                    rfl

theorem cell21_1028363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 2, 3].length) (baseStart_1028363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1028363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1028363 prefixEnd_1028363 := by exact prefixLift 1028363
  have htrace : WordTrace (prefixWord ++ tailWord_1028363) baseStart_1028363 baseEnd_1028363 := by
    simpa [prefixWord, tailWord_1028363, baseEnd_1028363] using wordTrace_append hprefix tailTrace_1028363
  have hstable : (prefixWord ++ tailWord_1028363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028363).length < 2 ^ (prefixWord ++ tailWord_1028363).sum := by decide
  have hdescent : baseEnd_1028363 < baseStart_1028363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028419 : List Nat := [1, 1, 1, 3, 1, 3, 2, 3, 6]
def baseStart_1028419 : Nat := 118140960795 + 1028419 * 2 ^ 59
def prefixEnd_1028419 : Nat := 4983230072969 + 3 ^ 40 * 1028419 * 2
def baseEnd_1028419 : Nat := 234699227207252017614619

theorem tailTrace_1028419 : CollatzResearch.WordTrace tailWord_1028419 prefixEnd_1028419 234699227207252017614619 := by
  unfold tailWord_1028419
  simp only [CollatzResearch.WordTrace]
  refine ⟨37509522461221077826896311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25006348307480718551264207 37509522461221077826896311)
  ·
    refine ⟨56264283691831616740344467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37509522461221077826896311 56264283691831616740344467)
    ·
      refine ⟨84396425537747425110516701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56264283691831616740344467 84396425537747425110516701)
      ·
        refine ⟨31648659576655284416443763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84396425537747425110516701 31648659576655284416443763)
        ·
          refine ⟨47472989364982926624665645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31648659576655284416443763 47472989364982926624665645)
          ·
            refine ⟨17802371011868597484249617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47472989364982926624665645 17802371011868597484249617)
            ·
              refine ⟨13351778258901448113187213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17802371011868597484249617 13351778258901448113187213)
              ·
                refine ⟨5006916847088043042445205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13351778258901448113187213 5006916847088043042445205)
                ·
                  refine ⟨234699227207252017614619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5006916847088043042445205 234699227207252017614619)
                  ·
                    rfl

theorem cell21_1028419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 6].length) (baseStart_1028419 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1028419 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1028419 prefixEnd_1028419 := by exact prefixLift 1028419
  have htrace : WordTrace (prefixWord ++ tailWord_1028419) baseStart_1028419 baseEnd_1028419 := by
    simpa [prefixWord, tailWord_1028419, baseEnd_1028419] using wordTrace_append hprefix tailTrace_1028419
  have hstable : (prefixWord ++ tailWord_1028419).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028419).length < 2 ^ (prefixWord ++ tailWord_1028419).sum := by decide
  have hdescent : baseEnd_1028419 < baseStart_1028419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028470 : List Nat := [5, 1, 1, 4, 1, 1, 1, 1, 6]
def baseStart_1028470 : Nat := 118140960795 + 1028470 * 2 ^ 59
def prefixEnd_1028470 : Nat := 4983230072969 + 3 ^ 40 * 1028470 * 2
def baseEnd_1028470 : Nat := 234710866102087262264515

theorem tailTrace_1028470 : CollatzResearch.WordTrace tailWord_1028470 prefixEnd_1028470 234710866102087262264515 := by
  unfold tailWord_1028470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2344461411502269596062679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25007588389357542358001909 2344461411502269596062679)
  ·
    refine ⟨3516692117253404394094019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2344461411502269596062679 3516692117253404394094019)
    ·
      refine ⟨5275038175880106591141029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3516692117253404394094019 5275038175880106591141029)
      ·
        refine ⟨989069657977519985838943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5275038175880106591141029 989069657977519985838943)
        ·
          refine ⟨1483604486966279978758415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 989069657977519985838943 1483604486966279978758415)
          ·
            refine ⟨2225406730449419968137623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483604486966279978758415 2225406730449419968137623)
            ·
              refine ⟨3338110095674129952206435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2225406730449419968137623 3338110095674129952206435)
              ·
                refine ⟨5007165143511194928309653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3338110095674129952206435 5007165143511194928309653)
                ·
                  refine ⟨234710866102087262264515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5007165143511194928309653 234710866102087262264515)
                  ·
                    rfl

theorem cell21_1028470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_1028470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1028470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1028470 prefixEnd_1028470 := by exact prefixLift 1028470
  have htrace : WordTrace (prefixWord ++ tailWord_1028470) baseStart_1028470 baseEnd_1028470 := by
    simpa [prefixWord, tailWord_1028470, baseEnd_1028470] using wordTrace_append hprefix tailTrace_1028470
  have hstable : (prefixWord ++ tailWord_1028470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028470).length < 2 ^ (prefixWord ++ tailWord_1028470).sum := by decide
  have hdescent : baseEnd_1028470 < baseStart_1028470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028515 : List Nat := [1, 1, 1, 4, 1, 6, 1, 3, 3]
def baseStart_1028515 : Nat := 118140960795 + 1028515 * 2 ^ 59
def prefixEnd_1028515 : Nat := 4983230072969 + 3 ^ 40 * 1028515 * 2
def baseEnd_1028515 : Nat := 234721135715177184014423

theorem tailTrace_1028515 : CollatzResearch.WordTrace tailWord_1028515 prefixEnd_1028515 234721135715177184014423 := by
  unfold tailWord_1028515
  simp only [CollatzResearch.WordTrace]
  refine ⟨37513023868873286222390999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25008682579248857481593999 37513023868873286222390999)
  ·
    refine ⟨56269535803309929333586499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37513023868873286222390999 56269535803309929333586499)
    ·
      refine ⟨84404303704964894000379749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56269535803309929333586499 84404303704964894000379749)
      ·
        refine ⟨15825806944680917625071203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84404303704964894000379749 15825806944680917625071203)
        ·
          refine ⟨23738710417021376437606805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15825806944680917625071203 23738710417021376437606805)
          ·
            refine ⟨1112752050797877020512819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23738710417021376437606805 1112752050797877020512819)
            ·
              refine ⟨1669128076196815530769229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1112752050797877020512819 1669128076196815530769229)
              ·
                refine ⟨625923028573805824038461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1669128076196815530769229 625923028573805824038461)
                ·
                  refine ⟨234721135715177184014423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 625923028573805824038461 234721135715177184014423)
                  ·
                    rfl

theorem cell21_1028515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 3, 3].length) (baseStart_1028515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1028515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1028515 prefixEnd_1028515 := by exact prefixLift 1028515
  have htrace : WordTrace (prefixWord ++ tailWord_1028515) baseStart_1028515 baseEnd_1028515 := by
    simpa [prefixWord, tailWord_1028515, baseEnd_1028515] using wordTrace_append hprefix tailTrace_1028515
  have hstable : (prefixWord ++ tailWord_1028515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028515).length < 2 ^ (prefixWord ++ tailWord_1028515).sum := by decide
  have hdescent : baseEnd_1028515 < baseStart_1028515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028588 : List Nat := [2, 2, 1, 1, 2, 1, 6, 2, 4]
def baseStart_1028588 : Nat := 118140960795 + 1028588 * 2 ^ 59
def prefixEnd_1028588 : Nat := 4983230072969 + 3 ^ 40 * 1028588 * 2
def baseEnd_1028588 : Nat := 234737795309745279297607

theorem tailTrace_1028588 : CollatzResearch.WordTrace tailWord_1028588 prefixEnd_1028588 234737795309745279297607 := by
  unfold tailWord_1028588
  simp only [CollatzResearch.WordTrace]
  refine ⟨18757843198804409844899209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25010457598405879793198945 18757843198804409844899209)
  ·
    refine ⟨14068382399103307383674407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18757843198804409844899209 14068382399103307383674407)
    ·
      refine ⟨21102573598654961075511611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14068382399103307383674407 21102573598654961075511611)
      ·
        refine ⟨31653860397982441613267417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21102573598654961075511611 31653860397982441613267417)
        ·
          refine ⟨23740395298486831209950563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31653860397982441613267417 23740395298486831209950563)
          ·
            refine ⟨35610592947730246814925845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23740395298486831209950563 35610592947730246814925845)
            ·
              refine ⟨1669246544424855319449649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35610592947730246814925845 1669246544424855319449649)
              ·
                refine ⟨1251934908318641489587237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1669246544424855319449649 1251934908318641489587237)
                ·
                  refine ⟨234737795309745279297607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1251934908318641489587237 234737795309745279297607)
                  ·
                    rfl

theorem cell21_1028588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_1028588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1028588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1028588 prefixEnd_1028588 := by exact prefixLift 1028588
  have htrace : WordTrace (prefixWord ++ tailWord_1028588) baseStart_1028588 baseEnd_1028588 := by
    simpa [prefixWord, tailWord_1028588, baseEnd_1028588] using wordTrace_append hprefix tailTrace_1028588
  have hstable : (prefixWord ++ tailWord_1028588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028588).length < 2 ^ (prefixWord ++ tailWord_1028588).sum := by decide
  have hdescent : baseEnd_1028588 < baseStart_1028588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028619 : List Nat := [1, 1, 1, 1, 7, 2, 3, 5]
def baseStart_1028619 : Nat := 118140960795 + 1028619 * 2 ^ 59
def prefixEnd_1028619 : Nat := 4983230072969 + 3 ^ 40 * 1028619 * 2
def baseEnd_1028619 : Nat := 78248289977365371426959

theorem tailTrace_1028619 : CollatzResearch.WordTrace tailWord_1028619 prefixEnd_1028619 78248289977365371426959 := by
  unfold tailWord_1028619
  simp only [CollatzResearch.WordTrace]
  refine ⟨37516817060496511984176911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25011211373664341322784607 37516817060496511984176911)
  ·
    refine ⟨56275225590744767976265367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37516817060496511984176911 56275225590744767976265367)
    ·
      refine ⟨84412838386117151964398051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56275225590744767976265367 84412838386117151964398051)
      ·
        refine ⟨126619257579175727946597077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84412838386117151964398051 126619257579175727946597077)
        ·
          refine ⟨2967638849511931123748369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 126619257579175727946597077 2967638849511931123748369)
          ·
            refine ⟨2225729137133948342811277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2967638849511931123748369 2225729137133948342811277)
            ·
              refine ⟨834648426425230628554229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2225729137133948342811277 834648426425230628554229)
              ·
                refine ⟨78248289977365371426959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 834648426425230628554229 78248289977365371426959)
                ·
                  rfl

theorem cell21_1028619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 5].length) (baseStart_1028619 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1028619 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1028619 prefixEnd_1028619 := by exact prefixLift 1028619
  have htrace : WordTrace (prefixWord ++ tailWord_1028619) baseStart_1028619 baseEnd_1028619 := by
    simpa [prefixWord, tailWord_1028619, baseEnd_1028619] using wordTrace_append hprefix tailTrace_1028619
  have hstable : (prefixWord ++ tailWord_1028619).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028619).length < 2 ^ (prefixWord ++ tailWord_1028619).sum := by decide
  have hdescent : baseEnd_1028619 < baseStart_1028619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028650 : List Nat := [3, 1, 4, 1, 1, 3, 2, 1, 5]
def baseStart_1028650 : Nat := 118140960795 + 1028650 * 2 ^ 59
def prefixEnd_1028650 : Nat := 4983230072969 + 3 ^ 40 * 1028650 * 2
def baseEnd_1028650 : Nat := 234751944554446949264147

theorem tailTrace_1028650 : CollatzResearch.WordTrace tailWord_1028650 prefixEnd_1028650 234751944554446949264147 := by
  unfold tailWord_1028650
  simp only [CollatzResearch.WordTrace]
  refine ⟨9379486930846051069638851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25011965148922802852370269 9379486930846051069638851)
  ·
    refine ⟨14069230396269076604458277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9379486930846051069638851 14069230396269076604458277)
    ·
      refine ⟨2637980699300451863335927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14069230396269076604458277 2637980699300451863335927)
      ·
        refine ⟨3956971048950677795003891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2637980699300451863335927 3956971048950677795003891)
        ·
          refine ⟨5935456573426016692505837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3956971048950677795003891 5935456573426016692505837)
          ·
            refine ⟨2225796215034756259689689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5935456573426016692505837 2225796215034756259689689)
            ·
              refine ⟨1669347161276067194767267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2225796215034756259689689 1669347161276067194767267)
              ·
                refine ⟨2504020741914100792150901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1669347161276067194767267 2504020741914100792150901)
                ·
                  refine ⟨234751944554446949264147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2504020741914100792150901 234751944554446949264147)
                  ·
                    rfl

theorem cell21_1028650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_1028650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1028650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1028650 prefixEnd_1028650 := by exact prefixLift 1028650
  have htrace : WordTrace (prefixWord ++ tailWord_1028650) baseStart_1028650 baseEnd_1028650 := by
    simpa [prefixWord, tailWord_1028650, baseEnd_1028650] using wordTrace_append hprefix tailTrace_1028650
  have hstable : (prefixWord ++ tailWord_1028650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028650).length < 2 ^ (prefixWord ++ tailWord_1028650).sum := by decide
  have hdescent : baseEnd_1028650 < baseStart_1028650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028670 : List Nat := [4, 2, 1, 4, 2, 1, 2, 5]
def baseStart_1028670 : Nat := 118140960795 + 1028670 * 2 ^ 59
def prefixEnd_1028670 : Nat := 4983230072969 + 3 ^ 40 * 1028670 * 2
def baseEnd_1028670 : Nat := 78252169608977119643591

theorem tailTrace_1028670 : CollatzResearch.WordTrace tailWord_1028670 prefixEnd_1028670 78252169608977119643591 := by
  unfold tailWord_1028670
  simp only [CollatzResearch.WordTrace]
  refine ⟨4689834647913968461785433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25012451455541165129522309 4689834647913968461785433)
  ·
    refine ⟨3517375985935476346339075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4689834647913968461785433 3517375985935476346339075)
    ·
      refine ⟨5276063978903214519508613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3517375985935476346339075 5276063978903214519508613)
      ·
        refine ⟨989261996044352722407865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5276063978903214519508613 989261996044352722407865)
        ·
          refine ⟨741946497033264541805899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 989261996044352722407865 741946497033264541805899)
          ·
            refine ⟨1112919745549896812708849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741946497033264541805899 1112919745549896812708849)
            ·
              refine ⟨834689809162422609531637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1112919745549896812708849 834689809162422609531637)
              ·
                refine ⟨78252169608977119643591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 834689809162422609531637 78252169608977119643591)
                ·
                  rfl

theorem cell21_1028670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_1028670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1028670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1028670 prefixEnd_1028670 := by exact prefixLift 1028670
  have htrace : WordTrace (prefixWord ++ tailWord_1028670) baseStart_1028670 baseEnd_1028670 := by
    simpa [prefixWord, tailWord_1028670, baseEnd_1028670] using wordTrace_append hprefix tailTrace_1028670
  have hstable : (prefixWord ++ tailWord_1028670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028670).length < 2 ^ (prefixWord ++ tailWord_1028670).sum := by decide
  have hdescent : baseEnd_1028670 < baseStart_1028670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028754 : List Nat := [3, 2, 3, 1, 2, 10]
def baseStart_1028754 : Nat := 118140960795 + 1028754 * 2 ^ 59
def prefixEnd_1028754 : Nat := 4983230072969 + 3 ^ 40 * 1028754 * 2
def baseEnd_1028754 : Nat := 8695395510050588130763

theorem tailTrace_1028754 : CollatzResearch.WordTrace tailWord_1028754 prefixEnd_1028754 8695395510050588130763 := by
  unfold tailWord_1028754
  simp only [CollatzResearch.WordTrace]
  refine ⟨9380435228751857510085329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25014493943338286693560877 9380435228751857510085329)
  ·
    refine ⟨7035326421563893132563997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9380435228751857510085329 7035326421563893132563997)
    ·
      refine ⟨2638247408086459924711499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7035326421563893132563997 2638247408086459924711499)
      ·
        refine ⟨3957371112129689887067249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2638247408086459924711499 3957371112129689887067249)
        ·
          refine ⟨2968028334097267415300437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3957371112129689887067249 2968028334097267415300437)
          ·
            refine ⟨8695395510050588130763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2968028334097267415300437 8695395510050588130763)
            ·
              rfl

theorem cell21_1028754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 10].length) (baseStart_1028754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1028754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1028754 prefixEnd_1028754 := by exact prefixLift 1028754
  have htrace : WordTrace (prefixWord ++ tailWord_1028754) baseStart_1028754 baseEnd_1028754 := by
    simpa [prefixWord, tailWord_1028754, baseEnd_1028754] using wordTrace_append hprefix tailTrace_1028754
  have hstable : (prefixWord ++ tailWord_1028754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028754).length < 2 ^ (prefixWord ++ tailWord_1028754).sum := by decide
  have hdescent : baseEnd_1028754 < baseStart_1028754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028833 : List Nat := [1, 2, 3, 1, 4, 2, 3, 1, 4]
def baseStart_1028833 : Nat := 118140960795 + 1028833 * 2 ^ 59
def prefixEnd_1028833 : Nat := 4983230072969 + 3 ^ 40 * 1028833 * 2
def baseEnd_1028833 : Nat := 234793707647679297713773

theorem tailTrace_1028833 : CollatzResearch.WordTrace tailWord_1028833 prefixEnd_1028833 234793707647679297713773 := by
  unfold tailWord_1028833
  simp only [CollatzResearch.WordTrace]
  refine ⟨37524622281721226532467153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25016414854480817688311435 37524622281721226532467153)
  ·
    refine ⟨28143466711290919899350365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37524622281721226532467153 28143466711290919899350365)
    ·
      refine ⟨10553800016734094962256387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28143466711290919899350365 10553800016734094962256387)
      ·
        refine ⟨15830700025101142443384581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10553800016734094962256387 15830700025101142443384581)
        ·
          refine ⟨2968256254706464208134609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15830700025101142443384581 2968256254706464208134609)
          ·
            refine ⟨2226192191029848156100957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2968256254706464208134609 2226192191029848156100957)
            ·
              refine ⟨834822071636193058537859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2226192191029848156100957 834822071636193058537859)
              ·
                refine ⟨1252233107454289587806789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 834822071636193058537859 1252233107454289587806789)
                ·
                  refine ⟨234793707647679297713773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1252233107454289587806789 234793707647679297713773)
                  ·
                    rfl

theorem cell21_1028833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 4].length) (baseStart_1028833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1028833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1028833 prefixEnd_1028833 := by exact prefixLift 1028833
  have htrace : WordTrace (prefixWord ++ tailWord_1028833) baseStart_1028833 baseEnd_1028833 := by
    simpa [prefixWord, tailWord_1028833, baseEnd_1028833] using wordTrace_append hprefix tailTrace_1028833
  have hstable : (prefixWord ++ tailWord_1028833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028833).length < 2 ^ (prefixWord ++ tailWord_1028833).sum := by decide
  have hdescent : baseEnd_1028833 < baseStart_1028833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028847 : List Nat := [1, 1, 2, 1, 5, 4, 2, 5]
def baseStart_1028847 : Nat := 118140960795 + 1028847 * 2 ^ 59
def prefixEnd_1028847 : Nat := 4983230072969 + 3 ^ 40 * 1028847 * 2
def baseEnd_1028847 : Nat := 78265634212806128160137

theorem tailTrace_1028847 : CollatzResearch.WordTrace tailWord_1028847 prefixEnd_1028847 78265634212806128160137 := by
  unfold tailWord_1028847
  simp only [CollatzResearch.WordTrace]
  refine ⟨37525132903670506923476795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25016755269113671282317863 37525132903670506923476795)
  ·
    refine ⟨56287699355505760385215193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37525132903670506923476795 56287699355505760385215193)
    ·
      refine ⟨42215774516629320288911395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56287699355505760385215193 42215774516629320288911395)
      ·
        refine ⟨63323661774943980433367093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42215774516629320288911395 63323661774943980433367093)
        ·
          refine ⟨5936593291400998165628165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63323661774943980433367093 5936593291400998165628165)
          ·
            refine ⟨1113111242137687156055281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5936593291400998165628165 1113111242137687156055281)
            ·
              refine ⟨834833431603265367041461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1113111242137687156055281 834833431603265367041461)
              ·
                refine ⟨78265634212806128160137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 834833431603265367041461 78265634212806128160137)
                ·
                  rfl

theorem cell21_1028847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 5].length) (baseStart_1028847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1028847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1028847 prefixEnd_1028847 := by exact prefixLift 1028847
  have htrace : WordTrace (prefixWord ++ tailWord_1028847) baseStart_1028847 baseEnd_1028847 := by
    simpa [prefixWord, tailWord_1028847, baseEnd_1028847] using wordTrace_append hprefix tailTrace_1028847
  have hstable : (prefixWord ++ tailWord_1028847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028847).length < 2 ^ (prefixWord ++ tailWord_1028847).sum := by decide
  have hdescent : baseEnd_1028847 < baseStart_1028847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028875 : List Nat := [1, 1, 1, 1, 5, 1, 1, 6, 4]
def baseStart_1028875 : Nat := 118140960795 + 1028875 * 2 ^ 59
def prefixEnd_1028875 : Nat := 4983230072969 + 3 ^ 40 * 1028875 * 2
def baseEnd_1028875 : Nat := 234803292619896558013687

theorem tailTrace_1028875 : CollatzResearch.WordTrace tailWord_1028875 prefixEnd_1028875 234803292619896558013687 := by
  unfold tailWord_1028875
  simp only [CollatzResearch.WordTrace]
  refine ⟨37526154147569067705496079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25017436098379378470330719 37526154147569067705496079)
  ·
    refine ⟨56289231221353601558244119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37526154147569067705496079 56289231221353601558244119)
    ·
      refine ⟨84433846832030402337366179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56289231221353601558244119 84433846832030402337366179)
      ·
        refine ⟨126650770248045603506049269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84433846832030402337366179 126650770248045603506049269)
        ·
          refine ⟨11873509710754275328692119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126650770248045603506049269 11873509710754275328692119)
          ·
            refine ⟨17810264566131412993038179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11873509710754275328692119 17810264566131412993038179)
            ·
              refine ⟨26715396849197119489557269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17810264566131412993038179 26715396849197119489557269)
              ·
                refine ⟨1252284227306114976072997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26715396849197119489557269 1252284227306114976072997)
                ·
                  refine ⟨234803292619896558013687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1252284227306114976072997 234803292619896558013687)
                  ·
                    rfl

theorem cell21_1028875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 4].length) (baseStart_1028875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1028875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1028875 prefixEnd_1028875 := by exact prefixLift 1028875
  have htrace : WordTrace (prefixWord ++ tailWord_1028875) baseStart_1028875 baseEnd_1028875 := by
    simpa [prefixWord, tailWord_1028875, baseEnd_1028875] using wordTrace_append hprefix tailTrace_1028875
  have hstable : (prefixWord ++ tailWord_1028875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028875).length < 2 ^ (prefixWord ++ tailWord_1028875).sum := by decide
  have hdescent : baseEnd_1028875 < baseStart_1028875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028892 : List Nat := [2, 2, 3, 1, 1, 4, 1, 3, 4]
def baseStart_1028892 : Nat := 118140960795 + 1028892 * 2 ^ 59
def prefixEnd_1028892 : Nat := 4983230072969 + 3 ^ 40 * 1028892 * 2
def baseEnd_1028892 : Nat := 234807172251508306230319

theorem tailTrace_1028892 : CollatzResearch.WordTrace tailWord_1028892 prefixEnd_1028892 234807172251508306230319 := by
  unfold tailWord_1028892
  simp only [CollatzResearch.WordTrace]
  refine ⟨18763387094253739804432465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25017849459004986405909953 18763387094253739804432465)
  ·
    refine ⟨14072540320690304853324349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18763387094253739804432465 14072540320690304853324349)
    ·
      refine ⟨5277202620258864319996631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14072540320690304853324349 5277202620258864319996631)
      ·
        refine ⟨7915803930388296479994947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5277202620258864319996631 7915803930388296479994947)
        ·
          refine ⟨11873705895582444719992421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7915803930388296479994947 11873705895582444719992421)
          ·
            refine ⟨2226319855421708384998579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11873705895582444719992421 2226319855421708384998579)
            ·
              refine ⟨3339479783132562577497869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2226319855421708384998579 3339479783132562577497869)
              ·
                refine ⟨1252304918674710966561701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3339479783132562577497869 1252304918674710966561701)
                ·
                  refine ⟨234807172251508306230319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1252304918674710966561701 234807172251508306230319)
                  ·
                    rfl

theorem cell21_1028892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_1028892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1028892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1028892 prefixEnd_1028892 := by exact prefixLift 1028892
  have htrace : WordTrace (prefixWord ++ tailWord_1028892) baseStart_1028892 baseEnd_1028892 := by
    simpa [prefixWord, tailWord_1028892, baseEnd_1028892] using wordTrace_append hprefix tailTrace_1028892
  have hstable : (prefixWord ++ tailWord_1028892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028892).length < 2 ^ (prefixWord ++ tailWord_1028892).sum := by decide
  have hdescent : baseEnd_1028892 < baseStart_1028892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028929 : List Nat := [1, 2, 5, 3, 1, 2, 2, 2, 3]
def baseStart_1028929 : Nat := 118140960795 + 1028929 * 2 ^ 59
def prefixEnd_1028929 : Nat := 4983230072969 + 3 ^ 40 * 1028929 * 2
def baseEnd_1028929 : Nat := 234815616155604464113577

theorem tailTrace_1028929 : CollatzResearch.WordTrace tailWord_1028929 prefixEnd_1028929 234815616155604464113577 := by
  unfold tailWord_1028929
  simp only [CollatzResearch.WordTrace]
  refine ⟨37528123689373434927961841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25018749126248956618641227 37528123689373434927961841)
  ·
    refine ⟨28146092767030076195971381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37528123689373434927961841 28146092767030076195971381)
    ·
      refine ⟨2638696196909069643372317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28146092767030076195971381 2638696196909069643372317)
      ·
        refine ⟨989511073840901116264619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2638696196909069643372317 989511073840901116264619)
        ·
          refine ⟨1484266610761351674396929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 989511073840901116264619 1484266610761351674396929)
          ·
            refine ⟨1113199958071013755797697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1484266610761351674396929 1113199958071013755797697)
            ·
              refine ⟨834899968553260316848273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1113199958071013755797697 834899968553260316848273)
              ·
                refine ⟨626174976414945237636205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 834899968553260316848273 626174976414945237636205)
                ·
                  refine ⟨234815616155604464113577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 626174976414945237636205 234815616155604464113577)
                  ·
                    rfl

theorem cell21_1028929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 2, 3].length) (baseStart_1028929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1028929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1028929 prefixEnd_1028929 := by exact prefixLift 1028929
  have htrace : WordTrace (prefixWord ++ tailWord_1028929) baseStart_1028929 baseEnd_1028929 := by
    simpa [prefixWord, tailWord_1028929, baseEnd_1028929] using wordTrace_append hprefix tailTrace_1028929
  have hstable : (prefixWord ++ tailWord_1028929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028929).length < 2 ^ (prefixWord ++ tailWord_1028929).sum := by decide
  have hdescent : baseEnd_1028929 < baseStart_1028929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028965 : List Nat := [1, 3, 1, 3, 1, 1, 2, 9]
def baseStart_1028965 : Nat := 118140960795 + 1028965 * 2 ^ 59
def prefixEnd_1028965 : Nat := 4983230072969 + 3 ^ 40 * 1028965 * 2
def baseEnd_1028965 : Nat := 78274610615358800504501

theorem tailTrace_1028965 : CollatzResearch.WordTrace tailWord_1028965 prefixEnd_1028965 78274610615358800504501 := by
  unfold tailWord_1028965
  simp only [CollatzResearch.WordTrace]
  refine ⟨37529436717243013076272349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25019624478162008717514899 37529436717243013076272349)
  ·
    refine ⟨14073538768966129903602131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37529436717243013076272349 14073538768966129903602131)
    ·
      refine ⟨21110308153449194855403197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14073538768966129903602131 21110308153449194855403197)
      ·
        refine ⟨7916365557543448070776199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21110308153449194855403197 7916365557543448070776199)
        ·
          refine ⟨11874548336315172106164299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7916365557543448070776199 11874548336315172106164299)
          ·
            refine ⟨17811822504472758159246449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11874548336315172106164299 17811822504472758159246449)
            ·
              refine ⟨13358866878354568619434837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17811822504472758159246449 13358866878354568619434837)
              ·
                refine ⟨78274610615358800504501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13358866878354568619434837 78274610615358800504501)
                ·
                  rfl

theorem cell21_1028965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 9].length) (baseStart_1028965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1028965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1028965 prefixEnd_1028965 := by exact prefixLift 1028965
  have htrace : WordTrace (prefixWord ++ tailWord_1028965) baseStart_1028965 baseEnd_1028965 := by
    simpa [prefixWord, tailWord_1028965, baseEnd_1028965] using wordTrace_append hprefix tailTrace_1028965
  have hstable : (prefixWord ++ tailWord_1028965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028965).length < 2 ^ (prefixWord ++ tailWord_1028965).sum := by decide
  have hdescent : baseEnd_1028965 < baseStart_1028965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029089 : List Nat := [1, 2, 3, 1, 2, 1, 1, 7, 3]
def baseStart_1029089 : Nat := 118140960795 + 1029089 * 2 ^ 59
def prefixEnd_1029089 : Nat := 4983230072969 + 3 ^ 40 * 1029089 * 2
def baseEnd_1029089 : Nat := 234852130335479741446583

theorem tailTrace_1029089 : CollatzResearch.WordTrace tailWord_1029089 prefixEnd_1029089 234852130335479741446583 := by
  unfold tailWord_1029089
  simp only [CollatzResearch.WordTrace]
  refine ⟨37533959368793782253786321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25022639579195854835857547 37533959368793782253786321)
  ·
    refine ⟨28150469526595336690339741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37533959368793782253786321 28150469526595336690339741)
    ·
      refine ⟨10556426072473251258877403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28150469526595336690339741 10556426072473251258877403)
      ·
        refine ⟨15834639108709876888316105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10556426072473251258877403 15834639108709876888316105)
        ·
          refine ⟨11875979331532407666237079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15834639108709876888316105 11875979331532407666237079)
          ·
            refine ⟨17813968997298611499355619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11875979331532407666237079 17813968997298611499355619)
            ·
              refine ⟨26720953495947917249033429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17813968997298611499355619 26720953495947917249033429)
              ·
                refine ⟨626272347561279310524221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 26720953495947917249033429 626272347561279310524221)
                ·
                  refine ⟨234852130335479741446583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 626272347561279310524221 234852130335479741446583)
                  ·
                    rfl

theorem cell21_1029089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 7, 3].length) (baseStart_1029089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1029089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1029089 prefixEnd_1029089 := by exact prefixLift 1029089
  have htrace : WordTrace (prefixWord ++ tailWord_1029089) baseStart_1029089 baseEnd_1029089 := by
    simpa [prefixWord, tailWord_1029089, baseEnd_1029089] using wordTrace_append hprefix tailTrace_1029089
  have hstable : (prefixWord ++ tailWord_1029089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029089).length < 2 ^ (prefixWord ++ tailWord_1029089).sum := by decide
  have hdescent : baseEnd_1029089 < baseStart_1029089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029103 : List Nat := [1, 1, 2, 1, 4, 3, 1, 4, 4]
def baseStart_1029103 : Nat := 118140960795 + 1029103 * 2 ^ 59
def prefixEnd_1029103 : Nat := 4983230072969 + 3 ^ 40 * 1029103 * 2
def baseEnd_1029103 : Nat := 234855325326218828213221

theorem tailTrace_1029103 : CollatzResearch.WordTrace tailWord_1029103 prefixEnd_1029103 234855325326218828213221 := by
  unfold tailWord_1029103
  simp only [CollatzResearch.WordTrace]
  refine ⟨37534469990743062644795963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25022979993828708429863975 37534469990743062644795963)
  ·
    refine ⟨56301704986114593967193945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37534469990743062644795963 56301704986114593967193945)
    ·
      refine ⟨42226278739585945475395459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56301704986114593967193945 42226278739585945475395459)
      ·
        refine ⟨63339418109378918213093189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42226278739585945475395459 63339418109378918213093189)
        ·
          refine ⟨11876140895508547164954973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63339418109378918213093189 11876140895508547164954973)
          ·
            refine ⟨4453552835815705186858115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11876140895508547164954973 4453552835815705186858115)
            ·
              refine ⟨6680329253723557780287173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4453552835815705186858115 6680329253723557780287173)
              ·
                refine ⟨1252561735073167083803845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6680329253723557780287173 1252561735073167083803845)
                ·
                  refine ⟨234855325326218828213221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1252561735073167083803845 234855325326218828213221)
                  ·
                    rfl

theorem cell21_1029103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 4].length) (baseStart_1029103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1029103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1029103 prefixEnd_1029103 := by exact prefixLift 1029103
  have htrace : WordTrace (prefixWord ++ tailWord_1029103) baseStart_1029103 baseEnd_1029103 := by
    simpa [prefixWord, tailWord_1029103, baseEnd_1029103] using wordTrace_append hprefix tailTrace_1029103
  have hstable : (prefixWord ++ tailWord_1029103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029103).length < 2 ^ (prefixWord ++ tailWord_1029103).sum := by decide
  have hdescent : baseEnd_1029103 < baseStart_1029103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029109 : List Nat := [1, 3, 5, 2, 2, 1, 1, 6]
def baseStart_1029109 : Nat := 118140960795 + 1029109 * 2 ^ 59
def prefixEnd_1029109 : Nat := 4983230072969 + 3 ^ 40 * 1029109 * 2
def baseEnd_1029109 : Nat := 78285564869321383704403

theorem tailTrace_1029109 : CollatzResearch.WordTrace tailWord_1029109 prefixEnd_1029109 78285564869321383704403 := by
  unfold tailWord_1029109
  simp only [CollatzResearch.WordTrace]
  refine ⟨37534688828721325669514381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25023125885814217113009587 37534688828721325669514381)
  ·
    refine ⟨14075508310770497126067893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37534688828721325669514381 14075508310770497126067893)
    ·
      refine ⟨1319578904134734105568865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14075508310770497126067893 1319578904134734105568865)
      ·
        refine ⟨989684178101050579176649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1319578904134734105568865 989684178101050579176649)
        ·
          refine ⟨742263133575787934382487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 989684178101050579176649 742263133575787934382487)
          ·
            refine ⟨1113394700363681901573731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742263133575787934382487 1113394700363681901573731)
            ·
              refine ⟨1670092050545522852360597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1113394700363681901573731 1670092050545522852360597)
              ·
                refine ⟨78285564869321383704403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1670092050545522852360597 78285564869321383704403)
                ·
                  rfl

theorem cell21_1029109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 6].length) (baseStart_1029109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1029109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1029109 prefixEnd_1029109 := by exact prefixLift 1029109
  have htrace : WordTrace (prefixWord ++ tailWord_1029109) baseStart_1029109 baseEnd_1029109 := by
    simpa [prefixWord, tailWord_1029109, baseEnd_1029109] using wordTrace_append hprefix tailTrace_1029109
  have hstable : (prefixWord ++ tailWord_1029109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029109).length < 2 ^ (prefixWord ++ tailWord_1029109).sum := by decide
  have hdescent : baseEnd_1029109 < baseStart_1029109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029272 : List Nat := [2, 1, 2, 4, 2, 2, 2, 2, 4]
def baseStart_1029272 : Nat := 118140960795 + 1029272 * 2 ^ 59
def prefixEnd_1029272 : Nat := 4983230072969 + 3 ^ 40 * 1029272 * 2
def baseEnd_1029272 : Nat := 234893893428712089896209

theorem tailTrace_1029272 : CollatzResearch.WordTrace tailWord_1029272 prefixEnd_1029272 234893893428712089896209 := by
  unfold tailWord_1029272
  simp only [CollatzResearch.WordTrace]
  refine ⟨18770316963565402253849035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25027089284753869671798713 18770316963565402253849035)
  ·
    refine ⟨28155475445348103380773553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18770316963565402253849035 28155475445348103380773553)
    ·
      refine ⟨21116606584011077535580165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28155475445348103380773553 21116606584011077535580165)
      ·
        refine ⟨3959363734502077037921281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21116606584011077535580165 3959363734502077037921281)
        ·
          refine ⟨2969522800876557778440961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3959363734502077037921281 2969522800876557778440961)
          ·
            refine ⟨2227142100657418333830721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2969522800876557778440961 2227142100657418333830721)
            ·
              refine ⟨1670356575493063750373041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2227142100657418333830721 1670356575493063750373041)
              ·
                refine ⟨1252767431619797812779781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1670356575493063750373041 1252767431619797812779781)
                ·
                  refine ⟨234893893428712089896209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1252767431619797812779781 234893893428712089896209)
                  ·
                    rfl

theorem cell21_1029272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 4].length) (baseStart_1029272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1029272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1029272 prefixEnd_1029272 := by exact prefixLift 1029272
  have htrace : WordTrace (prefixWord ++ tailWord_1029272) baseStart_1029272 baseEnd_1029272 := by
    simpa [prefixWord, tailWord_1029272, baseEnd_1029272] using wordTrace_append hprefix tailTrace_1029272
  have hstable : (prefixWord ++ tailWord_1029272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029272).length < 2 ^ (prefixWord ++ tailWord_1029272).sum := by decide
  have hdescent : baseEnd_1029272 < baseStart_1029272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029283 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 9]
def baseStart_1029283 : Nat := 118140960795 + 1029283 * 2 ^ 59
def prefixEnd_1029283 : Nat := 4983230072969 + 3 ^ 40 * 1029283 * 2
def baseEnd_1029283 : Nat := 234896403778578515212853

theorem tailTrace_1029283 : CollatzResearch.WordTrace tailWord_1029283 prefixEnd_1029283 234896403778578515212853 := by
  unfold tailWord_1029283
  simp only [CollatzResearch.WordTrace]
  refine ⟨37541035130090953386348503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25027356753393968924232335 37541035130090953386348503)
  ·
    refine ⟨56311552695136430079522755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37541035130090953386348503 56311552695136430079522755)
    ·
      refine ⟨84467329042704645119284133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56311552695136430079522755 84467329042704645119284133)
      ·
        refine ⟨15837624195507120959865775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84467329042704645119284133 15837624195507120959865775)
        ·
          refine ⟨23756436293260681439798663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15837624195507120959865775 23756436293260681439798663)
          ·
            refine ⟨35634654439891022159697995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23756436293260681439798663 35634654439891022159697995)
            ·
              refine ⟨53451981659836533239546993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35634654439891022159697995 53451981659836533239546993)
              ·
                refine ⟨40088986244877399929660245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53451981659836533239546993 40088986244877399929660245)
                ·
                  refine ⟨234896403778578515212853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40088986244877399929660245 234896403778578515212853)
                  ·
                    rfl

theorem cell21_1029283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 9].length) (baseStart_1029283 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1029283 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1029283 prefixEnd_1029283 := by exact prefixLift 1029283
  have htrace : WordTrace (prefixWord ++ tailWord_1029283) baseStart_1029283 baseEnd_1029283 := by
    simpa [prefixWord, tailWord_1029283, baseEnd_1029283] using wordTrace_append hprefix tailTrace_1029283
  have hstable : (prefixWord ++ tailWord_1029283).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029283).length < 2 ^ (prefixWord ++ tailWord_1029283).sum := by decide
  have hdescent : baseEnd_1029283 < baseStart_1029283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029362 : List Nat := [3, 2, 1, 3, 3, 1, 1, 7]
def baseStart_1029362 : Nat := 118140960795 + 1029362 * 2 ^ 59
def prefixEnd_1029362 : Nat := 4983230072969 + 3 ^ 40 * 1029362 * 2
def baseEnd_1029362 : Nat := 78304810884963977798675

theorem tailTrace_1029362 : CollatzResearch.WordTrace tailWord_1029362 prefixEnd_1029362 78304810884963977798675 := by
  unfold tailWord_1029362
  simp only [CollatzResearch.WordTrace]
  refine ⟨9385979124201187469618585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25029277664536499918982893 9385979124201187469618585)
  ·
    refine ⟨7039484343150890602213939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9385979124201187469618585 7039484343150890602213939)
    ·
      refine ⟨10559226514726335903320909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7039484343150890602213939 10559226514726335903320909)
      ·
        refine ⟨3959709943022375963745341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10559226514726335903320909 3959709943022375963745341)
        ·
          refine ⟨1484891228633390986404503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3959709943022375963745341 1484891228633390986404503)
          ·
            refine ⟨2227336842950086479606755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1484891228633390986404503 2227336842950086479606755)
            ·
              refine ⟨3341005264425129719410133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2227336842950086479606755 3341005264425129719410133)
              ·
                refine ⟨78304810884963977798675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3341005264425129719410133 78304810884963977798675)
                ·
                  rfl

theorem cell21_1029362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 7].length) (baseStart_1029362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1029362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1029362 prefixEnd_1029362 := by exact prefixLift 1029362
  have htrace : WordTrace (prefixWord ++ tailWord_1029362) baseStart_1029362 baseEnd_1029362 := by
    simpa [prefixWord, tailWord_1029362, baseEnd_1029362] using wordTrace_append hprefix tailTrace_1029362
  have hstable : (prefixWord ++ tailWord_1029362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029362).length < 2 ^ (prefixWord ++ tailWord_1029362).sum := by decide
  have hdescent : baseEnd_1029362 < baseStart_1029362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029444 : List Nat := [2, 3, 4, 1, 1, 3, 2, 2, 3]
def baseStart_1029444 : Nat := 118140960795 + 1029444 * 2 ^ 59
def prefixEnd_1029444 : Nat := 4983230072969 + 3 ^ 40 * 1029444 * 2
def baseEnd_1029444 : Nat := 234933146172078013029191

theorem tailTrace_1029444 : CollatzResearch.WordTrace tailWord_1029444 prefixEnd_1029444 234933146172078013029191 := by
  unfold tailWord_1029444
  simp only [CollatzResearch.WordTrace]
  refine ⟨18773453641253838941479693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25031271521671785255306257 18773453641253838941479693)
  ·
    refine ⟨7040045115470189603054885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18773453641253838941479693 7040045115470189603054885)
    ·
      refine ⟨1320008459150660550572791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7040045115470189603054885 1320008459150660550572791)
      ·
        refine ⟨1980012688725990825859187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1320008459150660550572791 1980012688725990825859187)
        ·
          refine ⟨2970019033088986238788781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1980012688725990825859187 2970019033088986238788781)
          ·
            refine ⟨1113757137408369839545793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2970019033088986238788781 1113757137408369839545793)
            ·
              refine ⟨835317853056277379659345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1113757137408369839545793 835317853056277379659345)
              ·
                refine ⟨626488389792208034744509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 835317853056277379659345 626488389792208034744509)
                ·
                  refine ⟨234933146172078013029191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 626488389792208034744509 234933146172078013029191)
                  ·
                    rfl

theorem cell21_1029444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_1029444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1029444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1029444 prefixEnd_1029444 := by exact prefixLift 1029444
  have htrace : WordTrace (prefixWord ++ tailWord_1029444) baseStart_1029444 baseEnd_1029444 := by
    simpa [prefixWord, tailWord_1029444, baseEnd_1029444] using wordTrace_append hprefix tailTrace_1029444
  have hstable : (prefixWord ++ tailWord_1029444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029444).length < 2 ^ (prefixWord ++ tailWord_1029444).sum := by decide
  have hdescent : baseEnd_1029444 < baseStart_1029444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029590 : List Nat := [5, 2, 1, 1, 1, 2, 2, 7]
def baseStart_1029590 : Nat := 118140960795 + 1029590 * 2 ^ 59
def prefixEnd_1029590 : Nat := 4983230072969 + 3 ^ 40 * 1029590 * 2
def baseEnd_1029590 : Nat := 78322155120404734531853

theorem tailTrace_1029590 : CollatzResearch.WordTrace tailWord_1029590 prefixEnd_1029590 78322155120404734531853 := by
  unfold tailWord_1029590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2347014521248671551110889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25034821559985829878516149 2347014521248671551110889)
  ·
    refine ⟨1760260890936503663333167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2347014521248671551110889 1760260890936503663333167)
    ·
      refine ⟨2640391336404755494999751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1760260890936503663333167 2640391336404755494999751)
      ·
        refine ⟨3960587004607133242499627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2640391336404755494999751 3960587004607133242499627)
        ·
          refine ⟨5940880506910699863749441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3960587004607133242499627 5940880506910699863749441)
          ·
            refine ⟨4455660380183024897812081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5940880506910699863749441 4455660380183024897812081)
            ·
              refine ⟨3341745285137268673359061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4455660380183024897812081 3341745285137268673359061)
              ·
                refine ⟨78322155120404734531853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3341745285137268673359061 78322155120404734531853)
                ·
                  rfl

theorem cell21_1029590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_1029590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1029590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1029590 prefixEnd_1029590 := by exact prefixLift 1029590
  have htrace : WordTrace (prefixWord ++ tailWord_1029590) baseStart_1029590 baseEnd_1029590 := by
    simpa [prefixWord, tailWord_1029590, baseEnd_1029590] using wordTrace_append hprefix tailTrace_1029590
  have hstable : (prefixWord ++ tailWord_1029590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029590).length < 2 ^ (prefixWord ++ tailWord_1029590).sum := by decide
  have hdescent : baseEnd_1029590 < baseStart_1029590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029649 : List Nat := [1, 2, 2, 1, 1, 2, 7, 5]
def baseStart_1029649 : Nat := 118140960795 + 1029649 * 2 ^ 59
def prefixEnd_1029649 : Nat := 4983230072969 + 3 ^ 40 * 1029649 * 2
def baseEnd_1029649 : Nat := 78326643321681070704035

theorem tailTrace_1029649 : CollatzResearch.WordTrace tailWord_1029649 prefixEnd_1029649 78326643321681070704035 := by
  unfold tailWord_1029649
  simp only [CollatzResearch.WordTrace]
  refine ⟨37554384246764997894172001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25036256164509998596114667 37554384246764997894172001)
  ·
    refine ⟨28165788185073748420629001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37554384246764997894172001 28165788185073748420629001)
    ·
      refine ⟨21124341138805311315471751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28165788185073748420629001 21124341138805311315471751)
      ·
        refine ⟨31686511708207966973207627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21124341138805311315471751 31686511708207966973207627)
        ·
          refine ⟨47529767562311950459811441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31686511708207966973207627 47529767562311950459811441)
          ·
            refine ⟨35647325671733962844858581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47529767562311950459811441 35647325671733962844858581)
            ·
              refine ⟨835484195431264754176373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 35647325671733962844858581 835484195431264754176373)
              ·
                refine ⟨78326643321681070704035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 835484195431264754176373 78326643321681070704035)
                ·
                  rfl

theorem cell21_1029649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 5].length) (baseStart_1029649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1029649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1029649 prefixEnd_1029649 := by exact prefixLift 1029649
  have htrace : WordTrace (prefixWord ++ tailWord_1029649) baseStart_1029649 baseEnd_1029649 := by
    simpa [prefixWord, tailWord_1029649, baseEnd_1029649] using wordTrace_append hprefix tailTrace_1029649
  have hstable : (prefixWord ++ tailWord_1029649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029649).length < 2 ^ (prefixWord ++ tailWord_1029649).sum := by decide
  have hdescent : baseEnd_1029649 < baseStart_1029649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029714 : List Nat := [3, 2, 2, 1, 2, 4, 1, 3, 3]
def baseStart_1029714 : Nat := 118140960795 + 1029714 * 2 ^ 59
def prefixEnd_1029714 : Nat := 4983230072969 + 3 ^ 40 * 1029714 * 2
def baseEnd_1029714 : Nat := 234994763850617543528639

theorem tailTrace_1029714 : CollatzResearch.WordTrace tailWord_1029714 prefixEnd_1029714 234994763850617543528639 := by
  unfold tailWord_1029714
  simp only [CollatzResearch.WordTrace]
  refine ⟨9389188747882378498822049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25037836661019675996858797 9389188747882378498822049)
  ·
    refine ⟨7041891560911783874116537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9389188747882378498822049 7041891560911783874116537)
    ·
      refine ⟨5281418670683837905587403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7041891560911783874116537 5281418670683837905587403)
      ·
        refine ⟨7922128006025756858381105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5281418670683837905587403 7922128006025756858381105)
        ·
          refine ⟨5941596004519317643785829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7922128006025756858381105 5941596004519317643785829)
          ·
            refine ⟨1114049250847372058209843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5941596004519317643785829 1114049250847372058209843)
            ·
              refine ⟨1671073876271058087314765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1114049250847372058209843 1671073876271058087314765)
              ·
                refine ⟨626652703601646782743037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1671073876271058087314765 626652703601646782743037)
                ·
                  refine ⟨234994763850617543528639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 626652703601646782743037 234994763850617543528639)
                  ·
                    rfl

theorem cell21_1029714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_1029714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1029714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1029714 prefixEnd_1029714 := by exact prefixLift 1029714
  have htrace : WordTrace (prefixWord ++ tailWord_1029714) baseStart_1029714 baseEnd_1029714 := by
    simpa [prefixWord, tailWord_1029714, baseEnd_1029714] using wordTrace_append hprefix tailTrace_1029714
  have hstable : (prefixWord ++ tailWord_1029714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029714).length < 2 ^ (prefixWord ++ tailWord_1029714).sum := by decide
  have hdescent : baseEnd_1029714 < baseStart_1029714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029742 : List Nat := [4, 1, 2, 2, 3, 1, 2, 6]
def baseStart_1029742 : Nat := 118140960795 + 1029742 * 2 ^ 59
def prefixEnd_1029742 : Nat := 4983230072969 + 3 ^ 40 * 1029742 * 2
def baseEnd_1029742 : Nat := 78333717944031905687305

theorem tailTrace_1029742 : CollatzResearch.WordTrace tailWord_1029742 prefixEnd_1029742 78333717944031905687305 := by
  unfold tailWord_1029742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4694722029428509347163435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25038517490285383184871653 4694722029428509347163435)
  ·
    refine ⟨7042083044142764020745153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4694722029428509347163435 7042083044142764020745153)
    ·
      refine ⟨5281562283107073015558865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7042083044142764020745153 5281562283107073015558865)
      ·
        refine ⟨3961171712330304761669149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5281562283107073015558865 3961171712330304761669149)
        ·
          refine ⟨1485439392123864285625931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3961171712330304761669149 1485439392123864285625931)
          ·
            refine ⟨2228159088185796428438897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1485439392123864285625931 2228159088185796428438897)
            ·
              refine ⟨1671119316139347321329173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2228159088185796428438897 1671119316139347321329173)
              ·
                refine ⟨78333717944031905687305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1671119316139347321329173 78333717944031905687305)
                ·
                  rfl

theorem cell21_1029742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_1029742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1029742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1029742 prefixEnd_1029742 := by exact prefixLift 1029742
  have htrace : WordTrace (prefixWord ++ tailWord_1029742) baseStart_1029742 baseEnd_1029742 := by
    simpa [prefixWord, tailWord_1029742, baseEnd_1029742] using wordTrace_append hprefix tailTrace_1029742
  have hstable : (prefixWord ++ tailWord_1029742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029742).length < 2 ^ (prefixWord ++ tailWord_1029742).sum := by decide
  have hdescent : baseEnd_1029742 < baseStart_1029742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029784 : List Nat := [2, 1, 2, 4, 1, 11]
def baseStart_1029784 : Nat := 118140960795 + 1029784 * 2 ^ 59
def prefixEnd_1029784 : Nat := 4983230072969 + 3 ^ 40 * 1029784 * 2
def baseEnd_1029784 : Nat := 8704101437196776939327

theorem tailTrace_1029784 : CollatzResearch.WordTrace tailWord_1029784 prefixEnd_1029784 8704101437196776939327 := by
  unfold tailWord_1029784
  simp only [CollatzResearch.WordTrace]
  refine ⟨18779654050637957975168203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25039538734183943966890937 18779654050637957975168203)
  ·
    refine ⟨28169481075956936962752305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18779654050637957975168203 28169481075956936962752305)
    ·
      refine ⟨21127110806967702722064229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28169481075956936962752305 21127110806967702722064229)
      ·
        refine ⟨3961333276306444260387043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21127110806967702722064229 3961333276306444260387043)
        ·
          refine ⟨5941999914459666390580565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3961333276306444260387043 5941999914459666390580565)
          ·
            refine ⟨8704101437196776939327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5941999914459666390580565 8704101437196776939327)
            ·
              rfl

theorem cell21_1029784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 11].length) (baseStart_1029784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1029784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1029784 prefixEnd_1029784 := by exact prefixLift 1029784
  have htrace : WordTrace (prefixWord ++ tailWord_1029784) baseStart_1029784 baseEnd_1029784 := by
    simpa [prefixWord, tailWord_1029784, baseEnd_1029784] using wordTrace_append hprefix tailTrace_1029784
  have hstable : (prefixWord ++ tailWord_1029784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029784).length < 2 ^ (prefixWord ++ tailWord_1029784).sum := by decide
  have hdescent : baseEnd_1029784 < baseStart_1029784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029790 : List Nat := [4, 3, 1, 1, 1, 3, 1, 4, 3]
def baseStart_1029790 : Nat := 118140960795 + 1029790 * 2 ^ 59
def prefixEnd_1029790 : Nat := 4983230072969 + 3 ^ 40 * 1029790 * 2
def baseEnd_1029790 : Nat := 235012108086058300261817

theorem tailTrace_1029790 : CollatzResearch.WordTrace tailWord_1029790 prefixEnd_1029790 235012108086058300261817 := by
  unfold tailWord_1029790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4694940867406772371881853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25039684626169452650036549 4694940867406772371881853)
  ·
    refine ⟨1760602825277539639455695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4694940867406772371881853 1760602825277539639455695)
    ·
      refine ⟨2640904237916309459183543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1760602825277539639455695 2640904237916309459183543)
      ·
        refine ⟨3961356356874464188775315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2640904237916309459183543 3961356356874464188775315)
        ·
          refine ⟨5942034535311696283162973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3961356356874464188775315 5942034535311696283162973)
          ·
            refine ⟨2228262950741886106186115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5942034535311696283162973 2228262950741886106186115)
            ·
              refine ⟨3342394426112829159279173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2228262950741886106186115 3342394426112829159279173)
              ·
                refine ⟨626698954896155467364845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3342394426112829159279173 626698954896155467364845)
                ·
                  refine ⟨235012108086058300261817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 626698954896155467364845 235012108086058300261817)
                  ·
                    rfl

theorem cell21_1029790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_1029790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1029790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1029790 prefixEnd_1029790 := by exact prefixLift 1029790
  have htrace : WordTrace (prefixWord ++ tailWord_1029790) baseStart_1029790 baseEnd_1029790 := by
    simpa [prefixWord, tailWord_1029790, baseEnd_1029790] using wordTrace_append hprefix tailTrace_1029790
  have hstable : (prefixWord ++ tailWord_1029790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029790).length < 2 ^ (prefixWord ++ tailWord_1029790).sum := by decide
  have hdescent : baseEnd_1029790 < baseStart_1029790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029815 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 7]
def baseStart_1029815 : Nat := 118140960795 + 1029815 * 2 ^ 59
def prefixEnd_1029815 : Nat := 4983230072969 + 3 ^ 40 * 1029815 * 2
def baseEnd_1029815 : Nat := 235017813426663812345099

theorem tailTrace_1029815 : CollatzResearch.WordTrace tailWord_1029815 prefixEnd_1029815 235017813426663812345099 := by
  unfold tailWord_1029815
  simp only [CollatzResearch.WordTrace]
  refine ⟨37560438764163608244714899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25040292509442405496476599 37560438764163608244714899)
  ·
    refine ⟨56340658146245412367072349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37560438764163608244714899 56340658146245412367072349)
    ·
      refine ⟨21127746804842029637652131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56340658146245412367072349 21127746804842029637652131)
      ·
        refine ⟨31691620207263044456478197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21127746804842029637652131 31691620207263044456478197)
        ·
          refine ⟨2971089394430910417794831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31691620207263044456478197 2971089394430910417794831)
          ·
            refine ⟨4456634091646365626692247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2971089394430910417794831 4456634091646365626692247)
            ·
              refine ⟨6684951137469548440038371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4456634091646365626692247 6684951137469548440038371)
              ·
                refine ⟨10027426706204322660057557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6684951137469548440038371 10027426706204322660057557)
                ·
                  refine ⟨235017813426663812345099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10027426706204322660057557 235017813426663812345099)
                  ·
                    rfl

theorem cell21_1029815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 7].length) (baseStart_1029815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1029815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1029815 prefixEnd_1029815 := by exact prefixLift 1029815
  have htrace : WordTrace (prefixWord ++ tailWord_1029815) baseStart_1029815 baseEnd_1029815 := by
    simpa [prefixWord, tailWord_1029815, baseEnd_1029815] using wordTrace_append hprefix tailTrace_1029815
  have hstable : (prefixWord ++ tailWord_1029815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029815).length < 2 ^ (prefixWord ++ tailWord_1029815).sum := by decide
  have hdescent : baseEnd_1029815 < baseStart_1029815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029829 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 8]
def baseStart_1029829 : Nat := 118140960795 + 1029829 * 2 ^ 59
def prefixEnd_1029829 : Nat := 4983230072969 + 3 ^ 40 * 1029829 * 2
def baseEnd_1029829 : Nat := 235021008417402899111737

theorem tailTrace_1029829 : CollatzResearch.WordTrace tailWord_1029829 prefixEnd_1029829 235021008417402899111737 := by
  unfold tailWord_1029829
  simp only [CollatzResearch.WordTrace]
  refine ⟨37560949386112888635724541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25040632924075259090483027 37560949386112888635724541)
  ·
    refine ⟨14085356019792333238396703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37560949386112888635724541 14085356019792333238396703)
    ·
      refine ⟨21128034029688499857595055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14085356019792333238396703 21128034029688499857595055)
      ·
        refine ⟨31692051044532749786392583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21128034029688499857595055 31692051044532749786392583)
        ·
          refine ⟨47538076566799124679588875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31692051044532749786392583 47538076566799124679588875)
          ·
            refine ⟨71307114850198687019383313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47538076566799124679588875 71307114850198687019383313)
            ·
              refine ⟨53480336137649015264537485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71307114850198687019383313 53480336137649015264537485)
              ·
                refine ⟨20055126051618380724201557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53480336137649015264537485 20055126051618380724201557)
                ·
                  refine ⟨235021008417402899111737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20055126051618380724201557 235021008417402899111737)
                  ·
                    rfl

theorem cell21_1029829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_1029829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1029829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1029829 prefixEnd_1029829 := by exact prefixLift 1029829
  have htrace : WordTrace (prefixWord ++ tailWord_1029829) baseStart_1029829 baseEnd_1029829 := by
    simpa [prefixWord, tailWord_1029829, baseEnd_1029829] using wordTrace_append hprefix tailTrace_1029829
  have hstable : (prefixWord ++ tailWord_1029829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029829).length < 2 ^ (prefixWord ++ tailWord_1029829).sum := by decide
  have hdescent : baseEnd_1029829 < baseStart_1029829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029860 : List Nat := [2, 3, 1, 1, 1, 3, 2, 8]
def baseStart_1029860 : Nat := 118140960795 + 1029860 * 2 ^ 59
def prefixEnd_1029860 : Nat := 4983230072969 + 3 ^ 40 * 1029860 * 2
def baseEnd_1029860 : Nat := 78342694346584578031669

theorem tailTrace_1029860 : CollatzResearch.WordTrace tailWord_1029860 prefixEnd_1029860 78342694346584578031669 := by
  unfold tailWord_1029860
  simp only [CollatzResearch.WordTrace]
  refine ⟨18781040024500290465051517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25041386699333720620068689 18781040024500290465051517)
  ·
    refine ⟨7042890009187608924394319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18781040024500290465051517 7042890009187608924394319)
    ·
      refine ⟨10564335013781413386591479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7042890009187608924394319 10564335013781413386591479)
      ·
        refine ⟨15846502520672120079887219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10564335013781413386591479 15846502520672120079887219)
        ·
          refine ⟨23769753781008180119830829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15846502520672120079887219 23769753781008180119830829)
          ·
            refine ⟨8913657667878067544936561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23769753781008180119830829 8913657667878067544936561)
            ·
              refine ⟨6685243250908550658702421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8913657667878067544936561 6685243250908550658702421)
              ·
                refine ⟨78342694346584578031669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6685243250908550658702421 78342694346584578031669)
                ·
                  rfl

theorem cell21_1029860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 8].length) (baseStart_1029860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1029860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1029860 prefixEnd_1029860 := by exact prefixLift 1029860
  have htrace : WordTrace (prefixWord ++ tailWord_1029860) baseStart_1029860 baseEnd_1029860 := by
    simpa [prefixWord, tailWord_1029860, baseEnd_1029860] using wordTrace_append hprefix tailTrace_1029860
  have hstable : (prefixWord ++ tailWord_1029860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029860).length < 2 ^ (prefixWord ++ tailWord_1029860).sum := by decide
  have hdescent : baseEnd_1029860 < baseStart_1029860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030088 : List Nat := [2, 1, 3, 1, 4, 1, 1, 8]
def baseStart_1030088 : Nat := 118140960795 + 1030088 * 2 ^ 59
def prefixEnd_1030088 : Nat := 4983230072969 + 3 ^ 40 * 1030088 * 2
def baseEnd_1030088 : Nat := 78360038582025334764847

theorem tailTrace_1030088 : CollatzResearch.WordTrace tailWord_1030088 prefixEnd_1030088 78360038582025334764847 := by
  unfold tailWord_1030088
  simp only [CollatzResearch.WordTrace]
  refine ⟨18785197946087287934701459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25046930594783050579601945 18785197946087287934701459)
  ·
    refine ⟨28177796919130931902052189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18785197946087287934701459 28177796919130931902052189)
    ·
      refine ⟨10566673844674099463269571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28177796919130931902052189 10566673844674099463269571)
      ·
        refine ⟨15850010767011149194904357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10566673844674099463269571 15850010767011149194904357)
        ·
          refine ⟨2971877018814590474044567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15850010767011149194904357 2971877018814590474044567)
          ·
            refine ⟨4457815528221885711066851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2971877018814590474044567 4457815528221885711066851)
            ·
              refine ⟨6686723292332828566600277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4457815528221885711066851 6686723292332828566600277)
              ·
                refine ⟨78360038582025334764847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6686723292332828566600277 78360038582025334764847)
                ·
                  rfl

theorem cell21_1030088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 8].length) (baseStart_1030088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1030088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1030088 prefixEnd_1030088 := by exact prefixLift 1030088
  have htrace : WordTrace (prefixWord ++ tailWord_1030088) baseStart_1030088 baseEnd_1030088 := by
    simpa [prefixWord, tailWord_1030088, baseEnd_1030088] using wordTrace_append hprefix tailTrace_1030088
  have hstable : (prefixWord ++ tailWord_1030088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030088).length < 2 ^ (prefixWord ++ tailWord_1030088).sum := by decide
  have hdescent : baseEnd_1030088 < baseStart_1030088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030223 : List Nat := [1, 1, 2, 1, 1, 2, 2, 11]
def baseStart_1030223 : Nat := 118140960795 + 1030223 * 2 ^ 59
def prefixEnd_1030223 : Nat := 4983230072969 + 3 ^ 40 * 1030223 * 2
def baseEnd_1030223 : Nat := 78370308195115256514755

theorem tailTrace_1030223 : CollatzResearch.WordTrace tailWord_1030223 prefixEnd_1030223 78370308195115256514755 := by
  unfold tailWord_1030223
  simp only [CollatzResearch.WordTrace]
  refine ⟨37575319746685493925567323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25050213164456995950378215 37575319746685493925567323)
  ·
    refine ⟨56362979620028240888350985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37575319746685493925567323 56362979620028240888350985)
    ·
      refine ⟨42272234715021180666263239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56362979620028240888350985 42272234715021180666263239)
      ·
        refine ⟨63408352072531770999394859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42272234715021180666263239 63408352072531770999394859)
        ·
          refine ⟨95112528108797656499092289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63408352072531770999394859 95112528108797656499092289)
          ·
            refine ⟨71334396081598242374319217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95112528108797656499092289 71334396081598242374319217)
            ·
              refine ⟨53500797061198681780739413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71334396081598242374319217 53500797061198681780739413)
              ·
                refine ⟨78370308195115256514755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 53500797061198681780739413 78370308195115256514755)
                ·
                  rfl

theorem cell21_1030223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 11].length) (baseStart_1030223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1030223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1030223 prefixEnd_1030223 := by exact prefixLift 1030223
  have htrace : WordTrace (prefixWord ++ tailWord_1030223) baseStart_1030223 baseEnd_1030223 := by
    simpa [prefixWord, tailWord_1030223, baseEnd_1030223] using wordTrace_append hprefix tailTrace_1030223
  have hstable : (prefixWord ++ tailWord_1030223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030223).length < 2 ^ (prefixWord ++ tailWord_1030223).sum := by decide
  have hdescent : baseEnd_1030223 < baseStart_1030223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030229 : List Nat := [1, 3, 2, 2, 1, 5, 1, 3, 3]
def baseStart_1030229 : Nat := 118140960795 + 1030229 * 2 ^ 59
def prefixEnd_1030229 : Nat := 4983230072969 + 3 ^ 40 * 1030229 * 2
def baseEnd_1030229 : Nat := 235112293867091092444253

theorem tailTrace_1030229 : CollatzResearch.WordTrace tailWord_1030229 prefixEnd_1030229 235112293867091092444253 := by
  unfold tailWord_1030229
  simp only [CollatzResearch.WordTrace]
  refine ⟨37575538584663756950285741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25050359056442504633523827 37575538584663756950285741)
  ·
    refine ⟨14090826969248908856357153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37575538584663756950285741 14090826969248908856357153)
    ·
      refine ⟨10568120226936681642267865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14090826969248908856357153 10568120226936681642267865)
      ·
        refine ⟨7926090170202511231700899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10568120226936681642267865 7926090170202511231700899)
        ·
          refine ⟨11889135255303766847551349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7926090170202511231700899 11889135255303766847551349)
          ·
            refine ⟨1114606430184728141957939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11889135255303766847551349 1114606430184728141957939)
            ·
              refine ⟨1671909645277092212936909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1114606430184728141957939 1671909645277092212936909)
              ·
                refine ⟨626966116978909579851341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1671909645277092212936909 626966116978909579851341)
                ·
                  refine ⟨235112293867091092444253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 626966116978909579851341 235112293867091092444253)
                  ·
                    rfl

theorem cell21_1030229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 3, 3].length) (baseStart_1030229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1030229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1030229 prefixEnd_1030229 := by exact prefixLift 1030229
  have htrace : WordTrace (prefixWord ++ tailWord_1030229) baseStart_1030229 baseEnd_1030229 := by
    simpa [prefixWord, tailWord_1030229, baseEnd_1030229] using wordTrace_append hprefix tailTrace_1030229
  have hstable : (prefixWord ++ tailWord_1030229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030229).length < 2 ^ (prefixWord ++ tailWord_1030229).sum := by decide
  have hdescent : baseEnd_1030229 < baseStart_1030229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030240 : List Nat := [2, 1, 1, 3, 2, 5, 7]
def baseStart_1030240 : Nat := 118140960795 + 1030240 * 2 ^ 59
def prefixEnd_1030240 : Nat := 4983230072969 + 3 ^ 40 * 1030240 * 2
def baseEnd_1030240 : Nat := 26123867135217501973433

theorem tailTrace_1030240 : CollatzResearch.WordTrace tailWord_1030240 prefixEnd_1030240 26123867135217501973433 := by
  unfold tailWord_1030240
  simp only [CollatzResearch.WordTrace]
  refine ⟨18787969893811952914468087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25050626525082603885957449 18787969893811952914468087)
  ·
    refine ⟨28181954840717929371702131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18787969893811952914468087 28181954840717929371702131)
    ·
      refine ⟨42272932261076894057553197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28181954840717929371702131 42272932261076894057553197)
      ·
        refine ⟨15852349597903835271582449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42272932261076894057553197 15852349597903835271582449)
        ·
          refine ⟨11889262198427876453686837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15852349597903835271582449 11889262198427876453686837)
          ·
            refine ⟨1114618331102613417533141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11889262198427876453686837 1114618331102613417533141)
            ·
              refine ⟨26123867135217501973433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1114618331102613417533141 26123867135217501973433)
              ·
                rfl

theorem cell21_1030240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 7].length) (baseStart_1030240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1030240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1030240 prefixEnd_1030240 := by exact prefixLift 1030240
  have htrace : WordTrace (prefixWord ++ tailWord_1030240) baseStart_1030240 baseEnd_1030240 := by
    simpa [prefixWord, tailWord_1030240, baseEnd_1030240] using wordTrace_append hprefix tailTrace_1030240
  have hstable : (prefixWord ++ tailWord_1030240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030240).length < 2 ^ (prefixWord ++ tailWord_1030240).sum := by decide
  have hdescent : baseEnd_1030240 < baseStart_1030240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030305 : List Nat := [1, 2, 3, 3, 1, 2, 4, 2, 3]
def baseStart_1030305 : Nat := 118140960795 + 1030305 * 2 ^ 59
def prefixEnd_1030305 : Nat := 4983230072969 + 3 ^ 40 * 1030305 * 2
def baseEnd_1030305 : Nat := 235129638102531849177431

theorem tailTrace_1030305 : CollatzResearch.WordTrace tailWord_1030305 prefixEnd_1030305 235129638102531849177431 := by
  unfold tailWord_1030305
  simp only [CollatzResearch.WordTrace]
  refine ⟨37578310532388421930052369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25052207021592281286701579 37578310532388421930052369)
  ·
    refine ⟨28183732899291316447539277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37578310532388421930052369 28183732899291316447539277)
    ·
      refine ⟨10568899837234243667827229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28183732899291316447539277 10568899837234243667827229)
      ·
        refine ⟨3963337438962841375435211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10568899837234243667827229 3963337438962841375435211)
        ·
          refine ⟨5945006158444262063152817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3963337438962841375435211 5945006158444262063152817)
          ·
            refine ⟨4458754618833196547364613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5945006158444262063152817 4458754618833196547364613)
            ·
              refine ⟨836016491031224352630865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4458754618833196547364613 836016491031224352630865)
              ·
                refine ⟨627012368273418264473149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 836016491031224352630865 627012368273418264473149)
                ·
                  refine ⟨235129638102531849177431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 627012368273418264473149 235129638102531849177431)
                  ·
                    rfl

theorem cell21_1030305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 2, 3].length) (baseStart_1030305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1030305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1030305 prefixEnd_1030305 := by exact prefixLift 1030305
  have htrace : WordTrace (prefixWord ++ tailWord_1030305) baseStart_1030305 baseEnd_1030305 := by
    simpa [prefixWord, tailWord_1030305, baseEnd_1030305] using wordTrace_append hprefix tailTrace_1030305
  have hstable : (prefixWord ++ tailWord_1030305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030305).length < 2 ^ (prefixWord ++ tailWord_1030305).sum := by decide
  have hdescent : baseEnd_1030305 < baseStart_1030305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030330 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 7]
def baseStart_1030330 : Nat := 118140960795 + 1030330 * 2 ^ 59
def prefixEnd_1030330 : Nat := 4983230072969 + 3 ^ 40 * 1030330 * 2
def baseEnd_1030330 : Nat := 235135343443137361260713

theorem tailTrace_1030330 : CollatzResearch.WordTrace tailWord_1030330 prefixEnd_1030330 235135343443137361260713 := by
  unfold tailWord_1030330
  simp only [CollatzResearch.WordTrace]
  refine ⟨9394805589324462799928111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25052814904865234133141629 9394805589324462799928111)
  ·
    refine ⟨14092208383986694199892167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9394805589324462799928111 14092208383986694199892167)
    ·
      refine ⟨21138312575980041299838251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14092208383986694199892167 21138312575980041299838251)
      ·
        refine ⟨31707468863970061949757377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21138312575980041299838251 31707468863970061949757377)
        ·
          refine ⟨23780601647977546462318033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31707468863970061949757377 23780601647977546462318033)
          ·
            refine ⟨17835451235983159846738525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23780601647977546462318033 17835451235983159846738525)
            ·
              refine ⟨6688294213493684942526947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17835451235983159846738525 6688294213493684942526947)
              ·
                refine ⟨10032441320240527413790421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6688294213493684942526947 10032441320240527413790421)
                ·
                  refine ⟨235135343443137361260713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10032441320240527413790421 235135343443137361260713)
                  ·
                    rfl

theorem cell21_1030330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_1030330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1030330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1030330 prefixEnd_1030330 := by exact prefixLift 1030330
  have htrace : WordTrace (prefixWord ++ tailWord_1030330) baseStart_1030330 baseEnd_1030330 := by
    simpa [prefixWord, tailWord_1030330, baseEnd_1030330] using wordTrace_append hprefix tailTrace_1030330
  have hstable : (prefixWord ++ tailWord_1030330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030330).length < 2 ^ (prefixWord ++ tailWord_1030330).sum := by decide
  have hdescent : baseEnd_1030330 < baseStart_1030330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030370 : List Nat := [3, 3, 4, 1, 1, 1, 3, 1, 4]
def baseStart_1030370 : Nat := 118140960795 + 1030370 * 2 ^ 59
def prefixEnd_1030370 : Nat := 4983230072969 + 3 ^ 40 * 1030370 * 2
def baseEnd_1030370 : Nat := 235144471988106180593965

theorem tailTrace_1030370 : CollatzResearch.WordTrace tailWord_1030370 prefixEnd_1030370 235144471988106180593965 := by
  unfold tailWord_1030370
  simp only [CollatzResearch.WordTrace]
  refine ⟨9395170319288234507792141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25053787518101958687445709 9395170319288234507792141)
  ·
    refine ⟨3523188869733087940422053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9395170319288234507792141 3523188869733087940422053)
    ·
      refine ⟨660597913074953988829135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3523188869733087940422053 660597913074953988829135)
      ·
        refine ⟨990896869612430983243703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660597913074953988829135 990896869612430983243703)
        ·
          refine ⟨1486345304418646474865555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 990896869612430983243703 1486345304418646474865555)
          ·
            refine ⟨2229517956627969712298333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1486345304418646474865555 2229517956627969712298333)
            ·
              refine ⟨836069233735488642111875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2229517956627969712298333 836069233735488642111875)
              ·
                refine ⟨1254103850603232963167813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 836069233735488642111875 1254103850603232963167813)
                ·
                  refine ⟨235144471988106180593965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1254103850603232963167813 235144471988106180593965)
                  ·
                    rfl

theorem cell21_1030370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_1030370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1030370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1030370 prefixEnd_1030370 := by exact prefixLift 1030370
  have htrace : WordTrace (prefixWord ++ tailWord_1030370) baseStart_1030370 baseEnd_1030370 := by
    simpa [prefixWord, tailWord_1030370, baseEnd_1030370] using wordTrace_append hprefix tailTrace_1030370
  have hstable : (prefixWord ++ tailWord_1030370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030370).length < 2 ^ (prefixWord ++ tailWord_1030370).sum := by decide
  have hdescent : baseEnd_1030370 < baseStart_1030370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030423 : List Nat := [1, 1, 3, 4, 1, 2, 3, 1, 5]
def baseStart_1030423 : Nat := 118140960795 + 1030423 * 2 ^ 59
def prefixEnd_1030423 : Nat := 4983230072969 + 3 ^ 40 * 1030423 * 2
def baseEnd_1030423 : Nat := 235156567310189866210523

theorem tailTrace_1030423 : CollatzResearch.WordTrace tailWord_1030423 prefixEnd_1030423 235156567310189866210523 := by
  unfold tailWord_1030423
  simp only [CollatzResearch.WordTrace]
  refine ⟨37582614345960928082847923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25055076230640618721898615 37582614345960928082847923)
  ·
    refine ⟨56373921518941392124271885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37582614345960928082847923 56373921518941392124271885)
    ·
      refine ⟨21140220569603022046601957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56373921518941392124271885 21140220569603022046601957)
      ·
        refine ⟨3963791356800566633737867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21140220569603022046601957 3963791356800566633737867)
        ·
          refine ⟨5945687035200849950606801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3963791356800566633737867 5945687035200849950606801)
          ·
            refine ⟨4459265276400637462955101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5945687035200849950606801 4459265276400637462955101)
            ·
              refine ⟨1672224478650239048608163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4459265276400637462955101 1672224478650239048608163)
              ·
                refine ⟨2508336717975358572912245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1672224478650239048608163 2508336717975358572912245)
                ·
                  refine ⟨235156567310189866210523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2508336717975358572912245 235156567310189866210523)
                  ·
                    rfl

theorem cell21_1030423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 5].length) (baseStart_1030423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1030423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1030423 prefixEnd_1030423 := by exact prefixLift 1030423
  have htrace : WordTrace (prefixWord ++ tailWord_1030423) baseStart_1030423 baseEnd_1030423 := by
    simpa [prefixWord, tailWord_1030423, baseEnd_1030423] using wordTrace_append hprefix tailTrace_1030423
  have hstable : (prefixWord ++ tailWord_1030423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030423).length < 2 ^ (prefixWord ++ tailWord_1030423).sum := by decide
  have hdescent : baseEnd_1030423 < baseStart_1030423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030429 : List Nat := [1, 4, 2, 3, 3, 1, 2, 1, 4]
def baseStart_1030429 : Nat := 118140960795 + 1030429 * 2 ^ 59
def prefixEnd_1030429 : Nat := 4983230072969 + 3 ^ 40 * 1030429 * 2
def baseEnd_1030429 : Nat := 235157936591935189110511

theorem tailTrace_1030429 : CollatzResearch.WordTrace tailWord_1030429 prefixEnd_1030429 235157936591935189110511 := by
  unfold tailWord_1030429
  simp only [CollatzResearch.WordTrace]
  refine ⟨37582833183939191107566341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25055222122626127405044227 37582833183939191107566341)
  ·
    refine ⟨7046781221988598332668689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37582833183939191107566341 7046781221988598332668689)
    ·
      refine ⟨5285085916491448749501517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7046781221988598332668689 5285085916491448749501517)
      ·
        refine ⟨1981907218684293281063069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5285085916491448749501517 1981907218684293281063069)
        ·
          refine ⟨743215207006609980398651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1981907218684293281063069 743215207006609980398651)
          ·
            refine ⟨1114822810509914970597977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743215207006609980398651 1114822810509914970597977)
            ·
              refine ⟨836117107882436227948483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1114822810509914970597977 836117107882436227948483)
              ·
                refine ⟨1254175661823654341922725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 836117107882436227948483 1254175661823654341922725)
                ·
                  refine ⟨235157936591935189110511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1254175661823654341922725 235157936591935189110511)
                  ·
                    rfl

theorem cell21_1030429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_1030429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1030429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1030429 prefixEnd_1030429 := by exact prefixLift 1030429
  have htrace : WordTrace (prefixWord ++ tailWord_1030429) baseStart_1030429 baseEnd_1030429 := by
    simpa [prefixWord, tailWord_1030429, baseEnd_1030429] using wordTrace_append hprefix tailTrace_1030429
  have hstable : (prefixWord ++ tailWord_1030429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030429).length < 2 ^ (prefixWord ++ tailWord_1030429).sum := by decide
  have hdescent : baseEnd_1030429 < baseStart_1030429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030451 : List Nat := [1, 1, 1, 2, 5, 1, 1, 9]
def baseStart_1030451 : Nat := 118140960795 + 1030451 * 2 ^ 59
def prefixEnd_1030451 : Nat := 4983230072969 + 3 ^ 40 * 1030451 * 2
def baseEnd_1030451 : Nat := 78387652430556013247933

theorem tailTrace_1030451 : CollatzResearch.WordTrace tailWord_1030451 prefixEnd_1030451 78387652430556013247933 := by
  unfold tailWord_1030451
  simp only [CollatzResearch.WordTrace]
  refine ⟨37583635589859488864867207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25055757059906325909911471 37583635589859488864867207)
  ·
    refine ⟨56375453384789233297300811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37583635589859488864867207 56375453384789233297300811)
    ·
      refine ⟨84563180077183849945951217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56375453384789233297300811 84563180077183849945951217)
      ·
        refine ⟨63422385057887887459463413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84563180077183849945951217 63422385057887887459463413)
        ·
          refine ⟨5945848599176989449324695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63422385057887887459463413 5945848599176989449324695)
          ·
            refine ⟨8918772898765484173987043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5945848599176989449324695 8918772898765484173987043)
            ·
              refine ⟨13378159348148226260980565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8918772898765484173987043 13378159348148226260980565)
              ·
                refine ⟨78387652430556013247933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13378159348148226260980565 78387652430556013247933)
                ·
                  rfl

theorem cell21_1030451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 9].length) (baseStart_1030451 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1030451 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1030451 prefixEnd_1030451 := by exact prefixLift 1030451
  have htrace : WordTrace (prefixWord ++ tailWord_1030451) baseStart_1030451 baseEnd_1030451 := by
    simpa [prefixWord, tailWord_1030451, baseEnd_1030451] using wordTrace_append hprefix tailTrace_1030451
  have hstable : (prefixWord ++ tailWord_1030451).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030451).length < 2 ^ (prefixWord ++ tailWord_1030451).sum := by decide
  have hdescent : baseEnd_1030451 < baseStart_1030451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030468 : List Nat := [2, 3, 4, 1, 11]
def baseStart_1030468 : Nat := 118140960795 + 1030468 * 2 ^ 59
def prefixEnd_1030468 : Nat := 4983230072969 + 3 ^ 40 * 1030468 * 2
def baseEnd_1030468 : Nat := 2903294283003454172351

theorem tailTrace_1030468 : CollatzResearch.WordTrace tailWord_1030468 prefixEnd_1030468 2903294283003454172351 := by
  unfold tailWord_1030468
  simp only [CollatzResearch.WordTrace]
  refine ⟨18792127815398950384118029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25056170420531933845490705 18792127815398950384118029)
  ·
    refine ⟨7047047930774606394044261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18792127815398950384118029 7047047930774606394044261)
    ·
      refine ⟨1321321487020238698883299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7047047930774606394044261 1321321487020238698883299)
      ·
        refine ⟨1981982230530358048324949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1321321487020238698883299 1981982230530358048324949)
        ·
          refine ⟨2903294283003454172351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1981982230530358048324949 2903294283003454172351)
          ·
            rfl

theorem cell21_1030468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 11].length) (baseStart_1030468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1030468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1030468 prefixEnd_1030468 := by exact prefixLift 1030468
  have htrace : WordTrace (prefixWord ++ tailWord_1030468) baseStart_1030468 baseEnd_1030468 := by
    simpa [prefixWord, tailWord_1030468, baseEnd_1030468] using wordTrace_append hprefix tailTrace_1030468
  have hstable : (prefixWord ++ tailWord_1030468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030468).length < 2 ^ (prefixWord ++ tailWord_1030468).sum := by decide
  have hdescent : baseEnd_1030468 < baseStart_1030468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030485 : List Nat := [1, 3, 2, 2, 4, 2, 1, 6]
def baseStart_1030485 : Nat := 118140960795 + 1030485 * 2 ^ 59
def prefixEnd_1030485 : Nat := 4983230072969 + 3 ^ 40 * 1030485 * 2
def baseEnd_1030485 : Nat := 78390238851630512059021

theorem tailTrace_1030485 : CollatzResearch.WordTrace tailWord_1030485 prefixEnd_1030485 78390238851630512059021 := by
  unfold tailWord_1030485
  simp only [CollatzResearch.WordTrace]
  refine ⟨37584875671736312671604909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25056583781157541781069939 37584875671736312671604909)
  ·
    refine ⟨14094328376901117251851841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37584875671736312671604909 14094328376901117251851841)
    ·
      refine ⟨10570746282675837938888881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14094328376901117251851841 10570746282675837938888881)
      ·
        refine ⟨7928059712006878454166661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10570746282675837938888881 7928059712006878454166661)
        ·
          refine ⟨1486511196001289710156249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7928059712006878454166661 1486511196001289710156249)
          ·
            refine ⟨1114883397000967282617187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1486511196001289710156249 1114883397000967282617187)
            ·
              refine ⟨1672325095501450923925781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1114883397000967282617187 1672325095501450923925781)
              ·
                refine ⟨78390238851630512059021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1672325095501450923925781 78390238851630512059021)
                ·
                  rfl

theorem cell21_1030485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 6].length) (baseStart_1030485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1030485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1030485 prefixEnd_1030485 := by exact prefixLift 1030485
  have htrace : WordTrace (prefixWord ++ tailWord_1030485) baseStart_1030485 baseEnd_1030485 := by
    simpa [prefixWord, tailWord_1030485, baseEnd_1030485] using wordTrace_append hprefix tailTrace_1030485
  have hstable : (prefixWord ++ tailWord_1030485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030485).length < 2 ^ (prefixWord ++ tailWord_1030485).sum := by decide
  have hdescent : baseEnd_1030485 < baseStart_1030485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030561 : List Nat := [1, 2, 3, 5, 1, 1, 1, 7]
def baseStart_1030561 : Nat := 118140960795 + 1030561 * 2 ^ 59
def prefixEnd_1030561 : Nat := 4983230072969 + 3 ^ 40 * 1030561 * 2
def baseEnd_1030561 : Nat := 78396020263444097636747

theorem tailTrace_1030561 : CollatzResearch.WordTrace tailWord_1030561 prefixEnd_1030561 78396020263444097636747 := by
  unfold tailWord_1030561
  simp only [CollatzResearch.WordTrace]
  refine ⟨37587647619460977651371537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25058431746307318434247691 37587647619460977651371537)
  ·
    refine ⟨28190735714595733238528653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37587647619460977651371537 28190735714595733238528653)
    ·
      refine ⟨10571525892973399964448245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28190735714595733238528653 10571525892973399964448245)
      ·
        refine ⟨991080552466256246667023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10571525892973399964448245 991080552466256246667023)
        ·
          refine ⟨1486620828699384370000535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 991080552466256246667023 1486620828699384370000535)
          ·
            refine ⟨2229931243049076555000803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1486620828699384370000535 2229931243049076555000803)
            ·
              refine ⟨3344896864573614832501205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2229931243049076555000803 3344896864573614832501205)
              ·
                refine ⟨78396020263444097636747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3344896864573614832501205 78396020263444097636747)
                ·
                  rfl

theorem cell21_1030561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 7].length) (baseStart_1030561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1030561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1030561 prefixEnd_1030561 := by exact prefixLift 1030561
  have htrace : WordTrace (prefixWord ++ tailWord_1030561) baseStart_1030561 baseEnd_1030561 := by
    simpa [prefixWord, tailWord_1030561, baseEnd_1030561] using wordTrace_append hprefix tailTrace_1030561
  have hstable : (prefixWord ++ tailWord_1030561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030561).length < 2 ^ (prefixWord ++ tailWord_1030561).sum := by decide
  have hdescent : baseEnd_1030561 < baseStart_1030561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030589 : List Nat := [1, 4, 1, 2, 2, 2, 2, 1, 6]
def baseStart_1030589 : Nat := 118140960795 + 1030589 * 2 ^ 59
def prefixEnd_1030589 : Nat := 4983230072969 + 3 ^ 40 * 1030589 * 2
def baseEnd_1030589 : Nat := 235194450771810466443517

theorem tailTrace_1030589 : CollatzResearch.WordTrace tailWord_1030589 prefixEnd_1030589 235194450771810466443517 := by
  unfold tailWord_1030589
  simp only [CollatzResearch.WordTrace]
  refine ⟨37588668863359538433390821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25059112575573025622260547 37588668863359538433390821)
  ·
    refine ⟨7047875411879913456260779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37588668863359538433390821 7047875411879913456260779)
    ·
      refine ⟨10571813117819870184391169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7047875411879913456260779 10571813117819870184391169)
      ·
        refine ⟨7928859838364902638293377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10571813117819870184391169 7928859838364902638293377)
        ·
          refine ⟨5946644878773676978720033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7928859838364902638293377 5946644878773676978720033)
          ·
            refine ⟨4459983659080257734040025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5946644878773676978720033 4459983659080257734040025)
            ·
              refine ⟨3344987744310193300530019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4459983659080257734040025 3344987744310193300530019)
              ·
                refine ⟨5017481616465289950795029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3344987744310193300530019 5017481616465289950795029)
                ·
                  refine ⟨235194450771810466443517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5017481616465289950795029 235194450771810466443517)
                  ·
                    rfl

theorem cell21_1030589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_1030589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1030589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1030589 prefixEnd_1030589 := by exact prefixLift 1030589
  have htrace : WordTrace (prefixWord ++ tailWord_1030589) baseStart_1030589 baseEnd_1030589 := by
    simpa [prefixWord, tailWord_1030589, baseEnd_1030589] using wordTrace_append hprefix tailTrace_1030589
  have hstable : (prefixWord ++ tailWord_1030589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030589).length < 2 ^ (prefixWord ++ tailWord_1030589).sum := by decide
  have hdescent : baseEnd_1030589 < baseStart_1030589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030696 : List Nat := [2, 1, 5, 2, 1, 2, 8]
def baseStart_1030696 : Nat := 118140960795 + 1030696 * 2 ^ 59
def prefixEnd_1030696 : Nat := 4983230072969 + 3 ^ 40 * 1030696 * 2
def baseEnd_1030696 : Nat := 26135429958844673128885

theorem tailTrace_1030696 : CollatzResearch.WordTrace tailWord_1030696 prefixEnd_1030696 26135429958844673128885 := by
  unfold tailWord_1030696
  simp only [CollatzResearch.WordTrace]
  refine ⟨18796285736985947853767971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25061714315981263805023961 18796285736985947853767971)
  ·
    refine ⟨28194428605478921780651957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18796285736985947853767971 28194428605478921780651957)
    ·
      refine ⟨2643227681763648916936121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28194428605478921780651957 2643227681763648916936121)
      ·
        refine ⟨1982420761322736687702091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2643227681763648916936121 1982420761322736687702091)
        ·
          refine ⟨2973631141984105031553137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1982420761322736687702091 2973631141984105031553137)
          ·
            refine ⟨2230223356488078773664853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2973631141984105031553137 2230223356488078773664853)
            ·
              refine ⟨26135429958844673128885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2230223356488078773664853 26135429958844673128885)
              ·
                rfl

theorem cell21_1030696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 8].length) (baseStart_1030696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1030696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1030696 prefixEnd_1030696 := by exact prefixLift 1030696
  have htrace : WordTrace (prefixWord ++ tailWord_1030696) baseStart_1030696 baseEnd_1030696 := by
    simpa [prefixWord, tailWord_1030696, baseEnd_1030696] using wordTrace_append hprefix tailTrace_1030696
  have hstable : (prefixWord ++ tailWord_1030696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030696).length < 2 ^ (prefixWord ++ tailWord_1030696).sum := by decide
  have hdescent : baseEnd_1030696 < baseStart_1030696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030831 : List Nat := [1, 1, 2, 1, 2, 5, 3, 6]
def baseStart_1030831 : Nat := 118140960795 + 1030831 * 2 ^ 59
def prefixEnd_1030831 : Nat := 4983230072969 + 3 ^ 40 * 1030831 * 2
def baseEnd_1030831 : Nat := 78416559489623941136563

theorem tailTrace_1030831 : CollatzResearch.WordTrace tailWord_1030831 prefixEnd_1030831 78416559489623941136563 := by
  unfold tailWord_1030831
  simp only [CollatzResearch.WordTrace]
  refine ⟨37597495328482813763700347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25064996885655209175800231 37597495328482813763700347)
  ·
    refine ⟨56396242992724220645550521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37597495328482813763700347 56396242992724220645550521)
    ·
      refine ⟨42297182244543165484162891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56396242992724220645550521 42297182244543165484162891)
      ·
        refine ⟨63445773366814748226244337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42297182244543165484162891 63445773366814748226244337)
        ·
          refine ⟨47584330025111061169683253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63445773366814748226244337 47584330025111061169683253)
          ·
            refine ⟨4461030939854161984657805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47584330025111061169683253 4461030939854161984657805)
            ·
              refine ⟨1672886602445310744246677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4461030939854161984657805 1672886602445310744246677)
              ·
                refine ⟨78416559489623941136563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1672886602445310744246677 78416559489623941136563)
                ·
                  rfl

theorem cell21_1030831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 6].length) (baseStart_1030831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1030831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1030831 prefixEnd_1030831 := by exact prefixLift 1030831
  have htrace : WordTrace (prefixWord ++ tailWord_1030831) baseStart_1030831 baseEnd_1030831 := by
    simpa [prefixWord, tailWord_1030831, baseEnd_1030831] using wordTrace_append hprefix tailTrace_1030831
  have hstable : (prefixWord ++ tailWord_1030831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030831).length < 2 ^ (prefixWord ++ tailWord_1030831).sum := by decide
  have hdescent : baseEnd_1030831 < baseStart_1030831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030848 : List Nat := [2, 1, 1, 2, 4, 3, 3, 5]
def baseStart_1030848 : Nat := 118140960795 + 1030848 * 2 ^ 59
def prefixEnd_1030848 : Nat := 4983230072969 + 3 ^ 40 * 1030848 * 2
def baseEnd_1030848 : Nat := 78417852700161190542107

theorem tailTrace_1030848 : CollatzResearch.WordTrace tailWord_1030848 prefixEnd_1030848 78417852700161190542107 := by
  unfold tailWord_1030848
  simp only [CollatzResearch.WordTrace]
  refine ⟨18799057684710612833534599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25065410246280817111379465 18799057684710612833534599)
  ·
    refine ⟨28198586527065919250301899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18799057684710612833534599 28198586527065919250301899)
    ·
      refine ⟨42297879790598878875452849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28198586527065919250301899 42297879790598878875452849)
      ·
        refine ⟨31723409842949159156589637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42297879790598878875452849 31723409842949159156589637)
        ·
          refine ⟨5948139345552967341860557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31723409842949159156589637 5948139345552967341860557)
          ·
            refine ⟨2230552254582362753197709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5948139345552967341860557 2230552254582362753197709)
            ·
              refine ⟨836457095468386032449141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2230552254582362753197709 836457095468386032449141)
              ·
                refine ⟨78417852700161190542107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 836457095468386032449141 78417852700161190542107)
                ·
                  rfl

theorem cell21_1030848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 5].length) (baseStart_1030848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1030848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1030848 prefixEnd_1030848 := by exact prefixLift 1030848
  have htrace : WordTrace (prefixWord ++ tailWord_1030848) baseStart_1030848 baseEnd_1030848 := by
    simpa [prefixWord, tailWord_1030848, baseEnd_1030848] using wordTrace_append hprefix tailTrace_1030848
  have hstable : (prefixWord ++ tailWord_1030848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030848).length < 2 ^ (prefixWord ++ tailWord_1030848).sum := by decide
  have hdescent : baseEnd_1030848 < baseStart_1030848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030868 : List Nat := [2, 4, 1, 3, 3, 1, 1, 2, 4]
def baseStart_1030868 : Nat := 118140960795 + 1030868 * 2 ^ 59
def prefixEnd_1030868 : Nat := 4983230072969 + 3 ^ 40 * 1030868 * 2
def baseEnd_1030868 : Nat := 235258122372967981292947

theorem tailTrace_1030868 : CollatzResearch.WordTrace tailWord_1030868 prefixEnd_1030868 235258122372967981292947 := by
  unfold tailWord_1030868
  simp only [CollatzResearch.WordTrace]
  refine ⟨18799422414674384541398629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25065896552899179388531505 18799422414674384541398629)
  ·
    refine ⟨3524891702751447101512243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18799422414674384541398629 3524891702751447101512243)
    ·
      refine ⟨5287337554127170652268365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3524891702751447101512243 5287337554127170652268365)
      ·
        refine ⟨1982751582797688994600637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5287337554127170652268365 1982751582797688994600637)
        ·
          refine ⟨743531843549133372975239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1982751582797688994600637 743531843549133372975239)
          ·
            refine ⟨1115297765323700059462859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743531843549133372975239 1115297765323700059462859)
            ·
              refine ⟨1672946647985550089194289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1115297765323700059462859 1672946647985550089194289)
              ·
                refine ⟨1254709985989162566895717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1672946647985550089194289 1254709985989162566895717)
                ·
                  refine ⟨235258122372967981292947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1254709985989162566895717 235258122372967981292947)
                  ·
                    rfl

theorem cell21_1030868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_1030868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1030868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1030868 prefixEnd_1030868 := by exact prefixLift 1030868
  have htrace : WordTrace (prefixWord ++ tailWord_1030868) baseStart_1030868 baseEnd_1030868 := by
    simpa [prefixWord, tailWord_1030868, baseEnd_1030868] using wordTrace_append hprefix tailTrace_1030868
  have hstable : (prefixWord ++ tailWord_1030868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030868).length < 2 ^ (prefixWord ++ tailWord_1030868).sum := by decide
  have hdescent : baseEnd_1030868 < baseStart_1030868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030879 : List Nat := [1, 1, 2, 3, 2, 3, 2, 4, 3]
def baseStart_1030879 : Nat := 118140960795 + 1030879 * 2 ^ 59
def prefixEnd_1030879 : Nat := 4983230072969 + 3 ^ 40 * 1030879 * 2
def baseEnd_1030879 : Nat := 235260632722834406609591

theorem tailTrace_1030879 : CollatzResearch.WordTrace tailWord_1030879 prefixEnd_1030879 235260632722834406609591 := by
  unfold tailWord_1030879
  simp only [CollatzResearch.WordTrace]
  refine ⟨37599246032308917961447691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25066164021539278640965127 37599246032308917961447691)
  ·
    refine ⟨56398869048463376942171537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37599246032308917961447691 56398869048463376942171537)
    ·
      refine ⟨42299151786347532706628653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56398869048463376942171537 42299151786347532706628653)
      ·
        refine ⟨15862181919880324764985745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42299151786347532706628653 15862181919880324764985745)
        ·
          refine ⟨11896636439910243573739309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15862181919880324764985745 11896636439910243573739309)
          ·
            refine ⟨4461238664966341340152241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11896636439910243573739309 4461238664966341340152241)
            ·
              refine ⟨3345928998724756005114181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4461238664966341340152241 3345928998724756005114181)
              ·
                refine ⟨627361687260891750958909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3345928998724756005114181 627361687260891750958909)
                ·
                  refine ⟨235260632722834406609591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 627361687260891750958909 235260632722834406609591)
                  ·
                    rfl

theorem cell21_1030879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 4, 3].length) (baseStart_1030879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1030879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1030879 prefixEnd_1030879 := by exact prefixLift 1030879
  have htrace : WordTrace (prefixWord ++ tailWord_1030879) baseStart_1030879 baseEnd_1030879 := by
    simpa [prefixWord, tailWord_1030879, baseEnd_1030879] using wordTrace_append hprefix tailTrace_1030879
  have hstable : (prefixWord ++ tailWord_1030879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030879).length < 2 ^ (prefixWord ++ tailWord_1030879).sum := by decide
  have hdescent : baseEnd_1030879 < baseStart_1030879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030921 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 7]
def baseStart_1030921 : Nat := 118140960795 + 1030921 * 2 ^ 59
def prefixEnd_1030921 : Nat := 4983230072969 + 3 ^ 40 * 1030921 * 2
def baseEnd_1030921 : Nat := 235270217695051666909505

theorem tailTrace_1030921 : CollatzResearch.WordTrace tailWord_1030921 prefixEnd_1030921 235270217695051666909505 := by
  unfold tailWord_1030921
  simp only [CollatzResearch.WordTrace]
  refine ⟨37600777898156759134476617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25067185265437839422984411 37600777898156759134476617)
  ·
    refine ⟨28200583423617569350857463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37600777898156759134476617 28200583423617569350857463)
    ·
      refine ⟨42300875135426354026286195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28200583423617569350857463 42300875135426354026286195)
      ·
        refine ⟨63451312703139531039429293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42300875135426354026286195 63451312703139531039429293)
        ·
          refine ⟨23794242263677324139785985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63451312703139531039429293 23794242263677324139785985)
          ·
            refine ⟨17845681697757993104839489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23794242263677324139785985 17845681697757993104839489)
            ·
              refine ⟨13384261273318494828629617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17845681697757993104839489 13384261273318494828629617)
              ·
                refine ⟨10038195954988871121472213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13384261273318494828629617 10038195954988871121472213)
                ·
                  refine ⟨235270217695051666909505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10038195954988871121472213 235270217695051666909505)
                  ·
                    rfl

theorem cell21_1030921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 7].length) (baseStart_1030921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1030921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1030921 prefixEnd_1030921 := by exact prefixLift 1030921
  have htrace : WordTrace (prefixWord ++ tailWord_1030921) baseStart_1030921 baseEnd_1030921 := by
    simpa [prefixWord, tailWord_1030921, baseEnd_1030921] using wordTrace_append hprefix tailTrace_1030921
  have hstable : (prefixWord ++ tailWord_1030921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030921).length < 2 ^ (prefixWord ++ tailWord_1030921).sum := by decide
  have hdescent : baseEnd_1030921 < baseStart_1030921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030930 : List Nat := [3, 2, 4, 1, 2, 1, 3, 2, 3]
def baseStart_1030930 : Nat := 118140960795 + 1030930 * 2 ^ 59
def prefixEnd_1030930 : Nat := 4983230072969 + 3 ^ 40 * 1030930 * 2
def baseEnd_1030930 : Nat := 235272271617669651259487

theorem tailTrace_1030930 : CollatzResearch.WordTrace tailWord_1030930 prefixEnd_1030930 235272271617669651259487 := by
  unfold tailWord_1030930
  simp only [CollatzResearch.WordTrace]
  refine ⟨9400276538781038417888561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25067404103416102447702829 9400276538781038417888561)
  ·
    refine ⟨7050207404085778813416421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9400276538781038417888561 7050207404085778813416421)
    ·
      refine ⟨1321913888266083527515579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7050207404085778813416421 1321913888266083527515579)
      ·
        refine ⟨1982870832399125291273369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1321913888266083527515579 1982870832399125291273369)
        ·
          refine ⟨1487153124299343968455027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1982870832399125291273369 1487153124299343968455027)
          ·
            refine ⟨2230729686449015952682541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1487153124299343968455027 2230729686449015952682541)
            ·
              refine ⟨836523632418380982255953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2230729686449015952682541 836523632418380982255953)
              ·
                refine ⟨627392724313785736691965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 836523632418380982255953 627392724313785736691965)
                ·
                  refine ⟨235272271617669651259487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 627392724313785736691965 235272271617669651259487)
                  ·
                    rfl

theorem cell21_1030930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_1030930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1030930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1030930 prefixEnd_1030930 := by exact prefixLift 1030930
  have htrace : WordTrace (prefixWord ++ tailWord_1030930) baseStart_1030930 baseEnd_1030930 := by
    simpa [prefixWord, tailWord_1030930, baseEnd_1030930] using wordTrace_append hprefix tailTrace_1030930
  have hstable : (prefixWord ++ tailWord_1030930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030930).length < 2 ^ (prefixWord ++ tailWord_1030930).sum := by decide
  have hdescent : baseEnd_1030930 < baseStart_1030930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030941 : List Nat := [1, 4, 2, 4, 1, 1, 2, 6]
def baseStart_1030941 : Nat := 118140960795 + 1030941 * 2 ^ 59
def prefixEnd_1030941 : Nat := 4983230072969 + 3 ^ 40 * 1030941 * 2
def baseEnd_1030941 : Nat := 78424927322512025525377

theorem tailTrace_1030941 : CollatzResearch.WordTrace tailWord_1030941 prefixEnd_1030941 78424927322512025525377 := by
  unfold tailWord_1030941
  simp only [CollatzResearch.WordTrace]
  refine ⟨37601507358084302550204677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25067671572056201700136451 37601507358084302550204677)
  ·
    refine ⟨7050282629640806728163377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37601507358084302550204677 7050282629640806728163377)
    ·
      refine ⟨5287711972230605046122533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7050282629640806728163377 5287711972230605046122533)
      ·
        refine ⟨991445994793238446147975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5287711972230605046122533 991445994793238446147975)
        ·
          refine ⟨1487168992189857669221963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 991445994793238446147975 1487168992189857669221963)
          ·
            refine ⟨2230753488284786503832945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1487168992189857669221963 2230753488284786503832945)
            ·
              refine ⟨1673065116213589877874709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2230753488284786503832945 1673065116213589877874709)
              ·
                refine ⟨78424927322512025525377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1673065116213589877874709 78424927322512025525377)
                ·
                  rfl

theorem cell21_1030941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 6].length) (baseStart_1030941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1030941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1030941 prefixEnd_1030941 := by exact prefixLift 1030941
  have htrace : WordTrace (prefixWord ++ tailWord_1030941) baseStart_1030941 baseEnd_1030941 := by
    simpa [prefixWord, tailWord_1030941, baseEnd_1030941] using wordTrace_append hprefix tailTrace_1030941
  have hstable : (prefixWord ++ tailWord_1030941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030941).length < 2 ^ (prefixWord ++ tailWord_1030941).sum := by decide
  have hdescent : baseEnd_1030941 < baseStart_1030941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030989 : List Nat := [1, 6, 1, 2, 2, 1, 1, 4, 3]
def baseStart_1030989 : Nat := 118140960795 + 1030989 * 2 ^ 59
def prefixEnd_1030989 : Nat := 4983230072969 + 3 ^ 40 * 1030989 * 2
def baseEnd_1030989 : Nat := 235285736221498659776033

theorem tailTrace_1030989 : CollatzResearch.WordTrace tailWord_1030989 prefixEnd_1030989 235285736221498659776033 := by
  unfold tailWord_1030989
  simp only [CollatzResearch.WordTrace]
  refine ⟨37603258061910406747952021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25068838707940271165301347 37603258061910406747952021)
  ·
    refine ⟨1762652721652050316310251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37603258061910406747952021 1762652721652050316310251)
    ·
      refine ⟨2643979082478075474465377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1762652721652050316310251 2643979082478075474465377)
      ·
        refine ⟨1982984311858556605849033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2643979082478075474465377 1982984311858556605849033)
        ·
          refine ⟨1487238233893917454386775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1982984311858556605849033 1487238233893917454386775)
          ·
            refine ⟨2230857350840876181580163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1487238233893917454386775 2230857350840876181580163)
            ·
              refine ⟨3346286026261314272370245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2230857350840876181580163 3346286026261314272370245)
              ·
                refine ⟨627428629923996426069421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3346286026261314272370245 627428629923996426069421)
                ·
                  refine ⟨235285736221498659776033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 627428629923996426069421 235285736221498659776033)
                  ·
                    rfl

theorem cell21_1030989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_1030989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1030989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1030989 prefixEnd_1030989 := by exact prefixLift 1030989
  have htrace : WordTrace (prefixWord ++ tailWord_1030989) baseStart_1030989 baseEnd_1030989 := by
    simpa [prefixWord, tailWord_1030989, baseEnd_1030989] using wordTrace_append hprefix tailTrace_1030989
  have hstable : (prefixWord ++ tailWord_1030989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030989).length < 2 ^ (prefixWord ++ tailWord_1030989).sum := by decide
  have hdescent : baseEnd_1030989 < baseStart_1030989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031045 : List Nat := [1, 3, 1, 1, 3, 3, 3, 2, 4]
def baseStart_1031045 : Nat := 118140960795 + 1031045 * 2 ^ 59
def prefixEnd_1031045 : Nat := 4983230072969 + 3 ^ 40 * 1031045 * 2
def baseEnd_1031045 : Nat := 235298516184455006842585

theorem tailTrace_1031045 : CollatzResearch.WordTrace tailWord_1031045 prefixEnd_1031045 235298516184455006842585 := by
  unfold tailWord_1031045
  simp only [CollatzResearch.WordTrace]
  refine ⟨37605300549707528311990589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25070200366471685541327059 37605300549707528311990589)
  ·
    refine ⟨14101987706140323116996471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37605300549707528311990589 14101987706140323116996471)
    ·
      refine ⟨21152981559210484675494707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14101987706140323116996471 21152981559210484675494707)
      ·
        refine ⟨31729472338815727013242061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21152981559210484675494707 31729472338815727013242061)
        ·
          refine ⟨11898552127055897629965773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31729472338815727013242061 11898552127055897629965773)
          ·
            refine ⟨4461957047645961611237165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11898552127055897629965773 4461957047645961611237165)
            ·
              refine ⟨1673233892867235604213937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4461957047645961611237165 1673233892867235604213937)
              ·
                refine ⟨1254925419650426703160453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1673233892867235604213937 1254925419650426703160453)
                ·
                  refine ⟨235298516184455006842585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1254925419650426703160453 235298516184455006842585)
                  ·
                    rfl

theorem cell21_1031045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_1031045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1031045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1031045 prefixEnd_1031045 := by exact prefixLift 1031045
  have htrace : WordTrace (prefixWord ++ tailWord_1031045) baseStart_1031045 baseEnd_1031045 := by
    simpa [prefixWord, tailWord_1031045, baseEnd_1031045] using wordTrace_append hprefix tailTrace_1031045
  have hstable : (prefixWord ++ tailWord_1031045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031045).length < 2 ^ (prefixWord ++ tailWord_1031045).sum := by decide
  have hdescent : baseEnd_1031045 < baseStart_1031045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031104 : List Nat := [2, 1, 1, 2, 3, 3, 2, 1, 6]
def baseStart_1031104 : Nat := 118140960795 + 1031104 * 2 ^ 59
def prefixEnd_1031104 : Nat := 4983230072969 + 3 ^ 40 * 1031104 * 2
def baseEnd_1031104 : Nat := 235311980788284015359131

theorem tailTrace_1031104 : CollatzResearch.WordTrace tailWord_1031104 prefixEnd_1031104 235311980788284015359131 := by
  unfold tailWord_1031104
  simp only [CollatzResearch.WordTrace]
  refine ⟨18803726228246890694194183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25071634970995854258925577 18803726228246890694194183)
  ·
    refine ⟨28205589342370336041291275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18803726228246890694194183 28205589342370336041291275)
    ·
      refine ⟨42308384013555504061936913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28205589342370336041291275 42308384013555504061936913)
      ·
        refine ⟨31731288010166628046452685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42308384013555504061936913 31731288010166628046452685)
        ·
          refine ⟨11899233003812485517419757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31731288010166628046452685 11899233003812485517419757)
          ·
            refine ⟨4462212376429682069032409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11899233003812485517419757 4462212376429682069032409)
            ·
              refine ⟨3346659282322261551774307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4462212376429682069032409 3346659282322261551774307)
              ·
                refine ⟨5019988923483392327661461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3346659282322261551774307 5019988923483392327661461)
                ·
                  refine ⟨235311980788284015359131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5019988923483392327661461 235311980788284015359131)
                  ·
                    rfl

theorem cell21_1031104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 6].length) (baseStart_1031104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1031104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1031104 prefixEnd_1031104 := by exact prefixLift 1031104
  have htrace : WordTrace (prefixWord ++ tailWord_1031104) baseStart_1031104 baseEnd_1031104 := by
    simpa [prefixWord, tailWord_1031104, baseEnd_1031104] using wordTrace_append hprefix tailTrace_1031104
  have hstable : (prefixWord ++ tailWord_1031104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031104).length < 2 ^ (prefixWord ++ tailWord_1031104).sum := by decide
  have hdescent : baseEnd_1031104 < baseStart_1031104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031245 : List Nat := [1, 6, 1, 1, 1, 4, 2, 5]
def baseStart_1031245 : Nat := 118140960795 + 1031245 * 2 ^ 59
def prefixEnd_1031245 : Nat := 4983230072969 + 3 ^ 40 * 1031245 * 2
def baseEnd_1031245 : Nat := 78448052969766367836281

theorem tailTrace_1031245 : CollatzResearch.WordTrace tailWord_1031245 prefixEnd_1031245 78448052969766367836281 := by
  unfold tailWord_1031245
  simp only [CollatzResearch.WordTrace]
  refine ⟨37612595148982962469271189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25075063432655308312847459 37612595148982962469271189)
  ·
    refine ⟨1763090397608576365747087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37612595148982962469271189 1763090397608576365747087)
    ·
      refine ⟨2644635596412864548620631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1763090397608576365747087 2644635596412864548620631)
      ·
        refine ⟨3966953394619296822930947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2644635596412864548620631 3966953394619296822930947)
        ·
          refine ⟨5950430091928945234396421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3966953394619296822930947 5950430091928945234396421)
          ·
            refine ⟨1115705642236677231449329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5950430091928945234396421 1115705642236677231449329)
            ·
              refine ⟨836779231677507923586997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1115705642236677231449329 836779231677507923586997)
              ·
                refine ⟨78448052969766367836281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 836779231677507923586997 78448052969766367836281)
                ·
                  rfl

theorem cell21_1031245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 5].length) (baseStart_1031245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1031245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1031245 prefixEnd_1031245 := by exact prefixLift 1031245
  have htrace : WordTrace (prefixWord ++ tailWord_1031245) baseStart_1031245 baseEnd_1031245 := by
    simpa [prefixWord, tailWord_1031245, baseEnd_1031245] using wordTrace_append hprefix tailTrace_1031245
  have hstable : (prefixWord ++ tailWord_1031245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031245).length < 2 ^ (prefixWord ++ tailWord_1031245).sum := by decide
  have hdescent : baseEnd_1031245 < baseStart_1031245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031315 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 8]
def baseStart_1031315 : Nat := 118140960795 + 1031315 * 2 ^ 59
def prefixEnd_1031315 : Nat := 4983230072969 + 3 ^ 40 * 1031315 * 2
def baseEnd_1031315 : Nat := 235360133862994537342033

theorem tailTrace_1031315 : CollatzResearch.WordTrace tailWord_1031315 prefixEnd_1031315 235360133862994537342033 := by
  unfold tailWord_1031315
  simp only [CollatzResearch.WordTrace]
  refine ⟨37615148258729364424319399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25076765505819576282879599 37615148258729364424319399)
  ·
    refine ⟨56422722388094046636479099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37615148258729364424319399 56422722388094046636479099)
    ·
      refine ⟨84634083582141069954718649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56422722388094046636479099 84634083582141069954718649)
      ·
        refine ⟨63475562686605802466038987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84634083582141069954718649 63475562686605802466038987)
        ·
          refine ⟨95213344029908703699058481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63475562686605802466038987 95213344029908703699058481)
          ·
            refine ⟨71410008022431527774293861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95213344029908703699058481 71410008022431527774293861)
            ·
              refine ⟨13389376504205911457680099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71410008022431527774293861 13389376504205911457680099)
              ·
                refine ⟨20084064756308867186520149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13389376504205911457680099 20084064756308867186520149)
                ·
                  refine ⟨235360133862994537342033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20084064756308867186520149 235360133862994537342033)
                  ·
                    rfl

theorem cell21_1031315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 8].length) (baseStart_1031315 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1031315 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1031315 prefixEnd_1031315 := by exact prefixLift 1031315
  have htrace : WordTrace (prefixWord ++ tailWord_1031315) baseStart_1031315 baseEnd_1031315 := by
    simpa [prefixWord, tailWord_1031315, baseEnd_1031315] using wordTrace_append hprefix tailTrace_1031315
  have hstable : (prefixWord ++ tailWord_1031315).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031315).length < 2 ^ (prefixWord ++ tailWord_1031315).sum := by decide
  have hdescent : baseEnd_1031315 < baseStart_1031315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031380 : List Nat := [2, 4, 1, 4, 1, 1, 8]
def baseStart_1031380 : Nat := 118140960795 + 1031380 * 2 ^ 59
def prefixEnd_1031380 : Nat := 4983230072969 + 3 ^ 40 * 1031380 * 2
def baseEnd_1031380 : Nat := 26152774194285429862063

theorem tailTrace_1031380 : CollatzResearch.WordTrace tailWord_1031380 prefixEnd_1031380 26152774194285429862063 := by
  unfold tailWord_1031380
  simp only [CollatzResearch.WordTrace]
  refine ⟨18808759501746940262717797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25078346002329253683623729 18808759501746940262717797)
  ·
    refine ⟨3526642406577551299259587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18808759501746940262717797 3526642406577551299259587)
    ·
      refine ⟨5289963609866326948889381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3526642406577551299259587 5289963609866326948889381)
      ·
        refine ⟨991868176849936302916759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5289963609866326948889381 991868176849936302916759)
        ·
          refine ⟨1487802265274904454375139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 991868176849936302916759 1487802265274904454375139)
          ·
            refine ⟨2231703397912356681562709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1487802265274904454375139 2231703397912356681562709)
            ·
              refine ⟨26152774194285429862063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2231703397912356681562709 26152774194285429862063)
              ·
                rfl

theorem cell21_1031380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 8].length) (baseStart_1031380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1031380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1031380 prefixEnd_1031380 := by exact prefixLift 1031380
  have htrace : WordTrace (prefixWord ++ tailWord_1031380) baseStart_1031380 baseEnd_1031380 := by
    simpa [prefixWord, tailWord_1031380, baseEnd_1031380] using wordTrace_append hprefix tailTrace_1031380
  have hstable : (prefixWord ++ tailWord_1031380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031380).length < 2 ^ (prefixWord ++ tailWord_1031380).sum := by decide
  have hdescent : baseEnd_1031380 < baseStart_1031380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031428 : List Nat := [2, 3, 2, 2, 2, 3, 1, 3, 3]
def baseStart_1031428 : Nat := 118140960795 + 1031428 * 2 ^ 59
def prefixEnd_1031428 : Nat := 4983230072969 + 3 ^ 40 * 1031428 * 2
def baseEnd_1031428 : Nat := 235385922002531451958469

theorem tailTrace_1031428 : CollatzResearch.WordTrace tailWord_1031428 prefixEnd_1031428 235385922002531451958469 := by
  unfold tailWord_1031428
  simp only [CollatzResearch.WordTrace]
  refine ⟨18809634853659992361591469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25079513138213323148788625 18809634853659992361591469)
  ·
    refine ⟨7053613070122497135596801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18809634853659992361591469 7053613070122497135596801)
    ·
      refine ⟨5290209802591872851697601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7053613070122497135596801 5290209802591872851697601)
      ·
        refine ⟨3967657351943904638773201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5290209802591872851697601 3967657351943904638773201)
        ·
          refine ⟨2975743013957928479079901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3967657351943904638773201 2975743013957928479079901)
          ·
            refine ⟨1115903630234223179654963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2975743013957928479079901 1115903630234223179654963)
            ·
              refine ⟨1673855445351334769482445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1115903630234223179654963 1673855445351334769482445)
              ·
                refine ⟨627695792006750538555917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1673855445351334769482445 627695792006750538555917)
                ·
                  refine ⟨235385922002531451958469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 627695792006750538555917 235385922002531451958469)
                  ·
                    rfl

theorem cell21_1031428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_1031428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1031428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1031428 prefixEnd_1031428 := by exact prefixLift 1031428
  have htrace : WordTrace (prefixWord ++ tailWord_1031428) baseStart_1031428 baseEnd_1031428 := by
    simpa [prefixWord, tailWord_1031428, baseEnd_1031428] using wordTrace_append hprefix tailTrace_1031428
  have hstable : (prefixWord ++ tailWord_1031428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031428).length < 2 ^ (prefixWord ++ tailWord_1031428).sum := by decide
  have hdescent : baseEnd_1031428 < baseStart_1031428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031543 : List Nat := [1, 1, 3, 1, 1, 2, 4, 2, 6]
def baseStart_1031543 : Nat := 118140960795 + 1031543 * 2 ^ 59
def prefixEnd_1031543 : Nat := 4983230072969 + 3 ^ 40 * 1031543 * 2
def baseEnd_1031543 : Nat := 235412166569316807541567

theorem tailTrace_1031543 : CollatzResearch.WordTrace tailWord_1031543 prefixEnd_1031543 235412166569316807541567 := by
  unfold tailWord_1031543
  simp only [CollatzResearch.WordTrace]
  refine ⟨37623464101903359363619283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25082309401268906242412855 37623464101903359363619283)
  ·
    refine ⟨56435196152855039045428925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37623464101903359363619283 56435196152855039045428925)
    ·
      refine ⟨21163198557320639642035847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56435196152855039045428925 21163198557320639642035847)
      ·
        refine ⟨31744797835980959463053771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21163198557320639642035847 31744797835980959463053771)
        ·
          refine ⟨47617196753971439194580657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31744797835980959463053771 47617196753971439194580657)
          ·
            refine ⟨35712897565478579395935493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47617196753971439194580657 35712897565478579395935493)
            ·
              refine ⟨6696168293527233636737905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35712897565478579395935493 6696168293527233636737905)
              ·
                refine ⟨5022126220145425227553429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6696168293527233636737905 5022126220145425227553429)
                ·
                  refine ⟨235412166569316807541567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5022126220145425227553429 235412166569316807541567)
                  ·
                    rfl

theorem cell21_1031543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 6].length) (baseStart_1031543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1031543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1031543 prefixEnd_1031543 := by exact prefixLift 1031543
  have htrace : WordTrace (prefixWord ++ tailWord_1031543) baseStart_1031543 baseEnd_1031543 := by
    simpa [prefixWord, tailWord_1031543, baseEnd_1031543] using wordTrace_append hprefix tailTrace_1031543
  have hstable : (prefixWord ++ tailWord_1031543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031543).length < 2 ^ (prefixWord ++ tailWord_1031543).sum := by decide
  have hdescent : baseEnd_1031543 < baseStart_1031543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031560 : List Nat := [2, 1, 3, 3, 1, 3, 1, 1, 6]
def baseStart_1031560 : Nat := 118140960795 + 1031560 * 2 ^ 59
def prefixEnd_1031560 : Nat := 4983230072969 + 3 ^ 40 * 1031560 * 2
def baseEnd_1031560 : Nat := 235416046200928555758199

theorem tailTrace_1031560 : CollatzResearch.WordTrace tailWord_1031560 prefixEnd_1031560 235416046200928555758199 := by
  unfold tailWord_1031560
  simp only [CollatzResearch.WordTrace]
  refine ⟨18812042071420885633494067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25082722761894514177992089 18812042071420885633494067)
  ·
    refine ⟨28218063107131328450241101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18812042071420885633494067 28218063107131328450241101)
    ·
      refine ⟨10581773665174248168840413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28218063107131328450241101 10581773665174248168840413)
      ·
        refine ⟨3968165124440343063315155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10581773665174248168840413 3968165124440343063315155)
        ·
          refine ⟨5952247686660514594972733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3968165124440343063315155 5952247686660514594972733)
          ·
            refine ⟨2232092882497692973114775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5952247686660514594972733 2232092882497692973114775)
            ·
              refine ⟨3348139323746539459672163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2232092882497692973114775 3348139323746539459672163)
              ·
                refine ⟨5022208985619809189508245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3348139323746539459672163 5022208985619809189508245)
                ·
                  refine ⟨235416046200928555758199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5022208985619809189508245 235416046200928555758199)
                  ·
                    rfl

theorem cell21_1031560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 6].length) (baseStart_1031560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1031560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1031560 prefixEnd_1031560 := by exact prefixLift 1031560
  have htrace : WordTrace (prefixWord ++ tailWord_1031560) baseStart_1031560 baseEnd_1031560 := by
    simpa [prefixWord, tailWord_1031560, baseEnd_1031560] using wordTrace_append hprefix tailTrace_1031560
  have hstable : (prefixWord ++ tailWord_1031560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031560).length < 2 ^ (prefixWord ++ tailWord_1031560).sum := by decide
  have hdescent : baseEnd_1031560 < baseStart_1031560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031577 : List Nat := [1, 2, 1, 2, 1, 6, 3, 1, 4]
def baseStart_1031577 : Nat := 118140960795 + 1031577 * 2 ^ 59
def prefixEnd_1031577 : Nat := 4983230072969 + 3 ^ 40 * 1031577 * 2
def baseEnd_1031577 : Nat := 235419925832540303974831

theorem tailTrace_1031577 : CollatzResearch.WordTrace tailWord_1031577 prefixEnd_1031577 235419925832540303974831 := by
  unfold tailWord_1031577
  simp only [CollatzResearch.WordTrace]
  refine ⟨37624704183780183170356985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25083136122520122113571323 37624704183780183170356985)
  ·
    refine ⟨28218528137835137377767739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37624704183780183170356985 28218528137835137377767739)
    ·
      refine ⟨42327792206752706066651609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28218528137835137377767739 42327792206752706066651609)
      ·
        refine ⟨31745844155064529549988707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42327792206752706066651609 31745844155064529549988707)
        ·
          refine ⟨47618766232596794324983061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31745844155064529549988707 47618766232596794324983061)
          ·
            refine ⟨2232129667152974733983581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47618766232596794324983061 2232129667152974733983581)
            ·
              refine ⟨837048625182365525243843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2232129667152974733983581 837048625182365525243843)
              ·
                refine ⟨1255572937773548287865765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 837048625182365525243843 1255572937773548287865765)
                ·
                  refine ⟨235419925832540303974831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1255572937773548287865765 235419925832540303974831)
                  ·
                    rfl

theorem cell21_1031577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 4].length) (baseStart_1031577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1031577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1031577 prefixEnd_1031577 := by exact prefixLift 1031577
  have htrace : WordTrace (prefixWord ++ tailWord_1031577) baseStart_1031577 baseEnd_1031577 := by
    simpa [prefixWord, tailWord_1031577, baseEnd_1031577] using wordTrace_append hprefix tailTrace_1031577
  have hstable : (prefixWord ++ tailWord_1031577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031577).length < 2 ^ (prefixWord ++ tailWord_1031577).sum := by decide
  have hdescent : baseEnd_1031577 < baseStart_1031577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031619 : List Nat := [1, 1, 1, 3, 1, 1, 6, 1, 6]
def baseStart_1031619 : Nat := 118140960795 + 1031619 * 2 ^ 59
def prefixEnd_1031619 : Nat := 4983230072969 + 3 ^ 40 * 1031619 * 2
def baseEnd_1031619 : Nat := 235429510804757564274745

theorem tailTrace_1031619 : CollatzResearch.WordTrace tailWord_1031619 prefixEnd_1031619 235429510804757564274745 := by
  unfold tailWord_1031619
  simp only [CollatzResearch.WordTrace]
  refine ⟨37626236049628024343385911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25084157366418682895590607 37626236049628024343385911)
  ·
    refine ⟨56439354074442036515078867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37626236049628024343385911 56439354074442036515078867)
    ·
      refine ⟨84659031111663054772618301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56439354074442036515078867 84659031111663054772618301)
      ·
        refine ⟨31747136666873645539731863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84659031111663054772618301 31747136666873645539731863)
        ·
          refine ⟨47620705000310468309597795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31747136666873645539731863 47620705000310468309597795)
          ·
            refine ⟨71431057500465702464396693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47620705000310468309597795 71431057500465702464396693)
            ·
              refine ⟨3348330820334329803018595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71431057500465702464396693 3348330820334329803018595)
              ·
                refine ⟨5022496230501494704527893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3348330820334329803018595 5022496230501494704527893)
                ·
                  refine ⟨235429510804757564274745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5022496230501494704527893 235429510804757564274745)
                  ·
                    rfl

theorem cell21_1031619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 6].length) (baseStart_1031619 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1031619 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1031619 prefixEnd_1031619 := by exact prefixLift 1031619
  have htrace : WordTrace (prefixWord ++ tailWord_1031619) baseStart_1031619 baseEnd_1031619 := by
    simpa [prefixWord, tailWord_1031619, baseEnd_1031619] using wordTrace_append hprefix tailTrace_1031619
  have hstable : (prefixWord ++ tailWord_1031619).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031619).length < 2 ^ (prefixWord ++ tailWord_1031619).sum := by decide
  have hdescent : baseEnd_1031619 < baseStart_1031619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031684 : List Nat := [2, 3, 2, 3, 2, 2, 1, 6]
def baseStart_1031684 : Nat := 118140960795 + 1031684 * 2 ^ 59
def prefixEnd_1031684 : Nat := 4983230072969 + 3 ^ 40 * 1031684 * 2
def baseEnd_1031684 : Nat := 78481448230110631897093

theorem tailTrace_1031684 : CollatzResearch.WordTrace tailWord_1031684 prefixEnd_1031684 78481448230110631897093 := by
  unfold tailWord_1031684
  simp only [CollatzResearch.WordTrace]
  refine ⟨18814303397196270222251053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25085737862928360296334737 18814303397196270222251053)
  ·
    refine ⟨7055363773948601333344145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18814303397196270222251053 7055363773948601333344145)
    ·
      refine ⟨5291522830461451000008109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7055363773948601333344145 5291522830461451000008109)
      ·
        refine ⟨1984321061423044125003041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5291522830461451000008109 1984321061423044125003041)
        ·
          refine ⟨1488240796067283093752281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1984321061423044125003041 1488240796067283093752281)
          ·
            refine ⟨1116180597050462320314211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1488240796067283093752281 1116180597050462320314211)
            ·
              refine ⟨1674270895575693480471317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1116180597050462320314211 1674270895575693480471317)
              ·
                refine ⟨78481448230110631897093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1674270895575693480471317 78481448230110631897093)
                ·
                  rfl

theorem cell21_1031684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 6].length) (baseStart_1031684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1031684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1031684 prefixEnd_1031684 := by exact prefixLift 1031684
  have htrace : WordTrace (prefixWord ++ tailWord_1031684) baseStart_1031684 baseEnd_1031684 := by
    simpa [prefixWord, tailWord_1031684, baseEnd_1031684] using wordTrace_append hprefix tailTrace_1031684
  have hstable : (prefixWord ++ tailWord_1031684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031684).length < 2 ^ (prefixWord ++ tailWord_1031684).sum := by decide
  have hdescent : baseEnd_1031684 < baseStart_1031684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031715 : List Nat := [1, 1, 1, 4, 5, 1, 2, 3, 3]
def baseStart_1031715 : Nat := 118140960795 + 1031715 * 2 ^ 59
def prefixEnd_1031715 : Nat := 4983230072969 + 3 ^ 40 * 1031715 * 2
def baseEnd_1031715 : Nat := 235451419312682730674549

theorem tailTrace_1031715 : CollatzResearch.WordTrace tailWord_1031715 prefixEnd_1031715 235451419312682730674549 := by
  unfold tailWord_1031715
  simp only [CollatzResearch.WordTrace]
  refine ⟨37629737457280232738880599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25086491638186821825920399 37629737457280232738880599)
  ·
    refine ⟨56444606185920349108320899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37629737457280232738880599 56444606185920349108320899)
    ·
      refine ⟨84666909278880523662481349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56444606185920349108320899 84666909278880523662481349)
      ·
        refine ⟨15875045489790098186715253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84666909278880523662481349 15875045489790098186715253)
        ·
          refine ⟨1488285514667821705004555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15875045489790098186715253 1488285514667821705004555)
          ·
            refine ⟨2232428272001732557506833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488285514667821705004555 2232428272001732557506833)
            ·
              refine ⟨1674321204001299418130125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2232428272001732557506833 1674321204001299418130125)
              ·
                refine ⟨627870451500487281798797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1674321204001299418130125 627870451500487281798797)
                ·
                  refine ⟨235451419312682730674549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 627870451500487281798797 235451419312682730674549)
                  ·
                    rfl

theorem cell21_1031715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 3, 3].length) (baseStart_1031715 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1031715 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1031715 prefixEnd_1031715 := by exact prefixLift 1031715
  have htrace : WordTrace (prefixWord ++ tailWord_1031715) baseStart_1031715 baseEnd_1031715 := by
    simpa [prefixWord, tailWord_1031715, baseEnd_1031715] using wordTrace_append hprefix tailTrace_1031715
  have hstable : (prefixWord ++ tailWord_1031715).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031715).length < 2 ^ (prefixWord ++ tailWord_1031715).sum := by decide
  have hdescent : baseEnd_1031715 < baseStart_1031715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031766 : List Nat := [5, 2, 2, 2, 1, 2, 1, 3, 3]
def baseStart_1031766 : Nat := 118140960795 + 1031766 * 2 ^ 59
def prefixEnd_1031766 : Nat := 4983230072969 + 3 ^ 40 * 1031766 * 2
def baseEnd_1031766 : Nat := 235463058207517975324445

theorem tailTrace_1031766 : CollatzResearch.WordTrace tailWord_1031766 prefixEnd_1031766 235463058207517975324445 := by
  unfold tailWord_1031766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2351974848755966778061697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25087731720063645632658101 2351974848755966778061697)
  ·
    refine ⟨1763981136566975083546273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2351974848755966778061697 1763981136566975083546273)
    ·
      refine ⟨1322985852425231312659705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1763981136566975083546273 1322985852425231312659705)
      ·
        refine ⟨992239389318923484494779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1322985852425231312659705 992239389318923484494779)
        ·
          refine ⟨1488359083978385226742169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 992239389318923484494779 1488359083978385226742169)
          ·
            refine ⟨1116269312983788920056627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1488359083978385226742169 1116269312983788920056627)
            ·
              refine ⟨1674403969475683380084941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1116269312983788920056627 1674403969475683380084941)
              ·
                refine ⟨627901488553381267531853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1674403969475683380084941 627901488553381267531853)
                ·
                  refine ⟨235463058207517975324445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 627901488553381267531853 235463058207517975324445)
                  ·
                    rfl

theorem cell21_1031766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_1031766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1031766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1031766 prefixEnd_1031766 := by exact prefixLift 1031766
  have htrace : WordTrace (prefixWord ++ tailWord_1031766) baseStart_1031766 baseEnd_1031766 := by
    simpa [prefixWord, tailWord_1031766, baseEnd_1031766] using wordTrace_append hprefix tailTrace_1031766
  have hstable : (prefixWord ++ tailWord_1031766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031766).length < 2 ^ (prefixWord ++ tailWord_1031766).sum := by decide
  have hdescent : baseEnd_1031766 < baseStart_1031766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031785 : List Nat := [1, 2, 1, 1, 1, 4, 11]
def baseStart_1031785 : Nat := 118140960795 + 1031785 * 2 ^ 59
def prefixEnd_1031785 : Nat := 4983230072969 + 3 ^ 40 * 1031785 * 2
def baseEnd_1031785 : Nat := 26163043807375351611971

theorem tailTrace_1031785 : CollatzResearch.WordTrace tailWord_1031785 prefixEnd_1031785 26163043807375351611971 := by
  unfold tailWord_1031785
  simp only [CollatzResearch.WordTrace]
  refine ⟨37632290567026634693928809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25088193711351089795952539 37632290567026634693928809)
  ·
    refine ⟨28224217925269976020446607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37632290567026634693928809 28224217925269976020446607)
    ·
      refine ⟨42336326887904964030669911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28224217925269976020446607 42336326887904964030669911)
      ·
        refine ⟨63504490331857446046004867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42336326887904964030669911 63504490331857446046004867)
        ·
          refine ⟨95256735497786169069007301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63504490331857446046004867 95256735497786169069007301)
          ·
            refine ⟨17860637905834906700438869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95256735497786169069007301 17860637905834906700438869)
            ·
              refine ⟨26163043807375351611971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 17860637905834906700438869 26163043807375351611971)
              ·
                rfl

theorem cell21_1031785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 11].length) (baseStart_1031785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1031785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1031785 prefixEnd_1031785 := by exact prefixLift 1031785
  have htrace : WordTrace (prefixWord ++ tailWord_1031785) baseStart_1031785 baseEnd_1031785 := by
    simpa [prefixWord, tailWord_1031785, baseEnd_1031785] using wordTrace_append hprefix tailTrace_1031785
  have hstable : (prefixWord ++ tailWord_1031785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031785).length < 2 ^ (prefixWord ++ tailWord_1031785).sum := by decide
  have hdescent : baseEnd_1031785 < baseStart_1031785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
