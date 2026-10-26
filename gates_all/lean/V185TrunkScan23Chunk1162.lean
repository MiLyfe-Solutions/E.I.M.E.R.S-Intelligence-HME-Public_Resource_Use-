import V185TrunkScan23Chunk1161

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6883992 : List Nat := [2, 1, 2, 4, 1, 1, 3, 2, 2, 1, 4]
def baseStart_6883992 : Nat := 118140960795 + 6883992 * 2 ^ 59
def prefixEnd_6883992 : Nat := 4983230072969 + 3 ^ 40 * 6883992 * 2
def baseEnd_6883992 : Nat := 3534796717705935583341103

theorem tailTrace_6883992 : CollatzResearch.WordTrace tailWord_6883992 prefixEnd_6883992 3534796717705935583341103 := by
  unfold tailWord_6883992
  simp only [CollatzResearch.WordTrace]
  refine ⟨125539907638240075538535115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167386543517653434051380153 125539907638240075538535115)
  ·
    refine ⟨188309861457360113307802673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125539907638240075538535115 188309861457360113307802673)
    ·
      refine ⟨141232396093020084980852005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188309861457360113307802673 141232396093020084980852005)
      ·
        refine ⟨26481074267441265933909751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141232396093020084980852005 26481074267441265933909751)
        ·
          refine ⟨39721611401161898900864627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26481074267441265933909751 39721611401161898900864627)
          ·
            refine ⟨59582417101742848351296941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39721611401161898900864627 59582417101742848351296941)
            ·
              refine ⟨22343406413153568131736353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59582417101742848351296941 22343406413153568131736353)
              ·
                refine ⟨16757554809865176098802265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22343406413153568131736353 16757554809865176098802265)
                ·
                  refine ⟨12568166107398882074101699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16757554809865176098802265 12568166107398882074101699)
                  ·
                    refine ⟨18852249161098323111152549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12568166107398882074101699 18852249161098323111152549)
                    ·
                      refine ⟨3534796717705935583341103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18852249161098323111152549 3534796717705935583341103)
                      ·
                        rfl

theorem cell23_6883992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_6883992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883992 prefixEnd_6883992 := by exact prefixLift 6883992
  have htrace : WordTrace (prefixWord ++ tailWord_6883992) baseStart_6883992 baseEnd_6883992 := by
    simpa [prefixWord, tailWord_6883992, baseEnd_6883992] using wordTrace_append hprefix tailTrace_6883992
  have hstable : (prefixWord ++ tailWord_6883992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883992).length < 2 ^ (prefixWord ++ tailWord_6883992).sum := by decide
  have hdescent : baseEnd_6883992 < baseStart_6883992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884029 : List Nat := [1, 4, 1, 2, 1, 4, 2, 1, 2, 2, 3]
def baseStart_6884029 : Nat := 118140960795 + 6884029 * 2 ^ 59
def prefixEnd_6884029 : Nat := 4983230072969 + 3 ^ 40 * 6884029 * 2
def baseEnd_6884029 : Nat := 3534815716490151938578433

theorem tailTrace_6884029 : CollatzResearch.WordTrace tailWord_6884029 prefixEnd_6884029 3534815716490151938578433 := by
  unfold tailWord_6884029
  simp only [CollatzResearch.WordTrace]
  refine ⟨251081164777346106396167141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167387443184897404264111427 251081164777346106396167141)
  ·
    refine ⟨47077718395752394949281339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251081164777346106396167141 47077718395752394949281339)
    ·
      refine ⟨70616577593628592423922009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47077718395752394949281339 70616577593628592423922009)
      ·
        refine ⟨52962433195221444317941507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70616577593628592423922009 52962433195221444317941507)
        ·
          refine ⟨79443649792832166476912261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52962433195221444317941507 79443649792832166476912261)
          ·
            refine ⟨14895684336156031214421049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79443649792832166476912261 14895684336156031214421049)
            ·
              refine ⟨11171763252117023410815787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14895684336156031214421049 11171763252117023410815787)
              ·
                refine ⟨16757644878175535116223681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11171763252117023410815787 16757644878175535116223681)
                ·
                  refine ⟨12568233658631651337167761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16757644878175535116223681 12568233658631651337167761)
                  ·
                    refine ⟨9426175243973738502875821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12568233658631651337167761 9426175243973738502875821)
                    ·
                      refine ⟨3534815716490151938578433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9426175243973738502875821 3534815716490151938578433)
                      ·
                        rfl

theorem cell23_6884029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_6884029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884029 prefixEnd_6884029 := by exact prefixLift 6884029
  have htrace : WordTrace (prefixWord ++ tailWord_6884029) baseStart_6884029 baseEnd_6884029 := by
    simpa [prefixWord, tailWord_6884029, baseEnd_6884029] using wordTrace_append hprefix tailTrace_6884029
  have hstable : (prefixWord ++ tailWord_6884029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884029).length < 2 ^ (prefixWord ++ tailWord_6884029).sum := by decide
  have hdescent : baseEnd_6884029 < baseStart_6884029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884053 : List Nat := [1, 3, 2, 5, 1, 1, 1, 4, 1, 4]
def baseStart_6884053 : Nat := 118140960795 + 6884053 * 2 ^ 59
def prefixEnd_6884053 : Nat := 4983230072969 + 3 ^ 40 * 6884053 * 2
def baseEnd_6884053 : Nat := 1178276013341953281559441

theorem tailTrace_6884053 : CollatzResearch.WordTrace tailWord_6884053 prefixEnd_6884053 1178276013341953281559441 := by
  unfold tailWord_6884053
  simp only [CollatzResearch.WordTrace]
  refine ⟨251082040129259158495040813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167388026752839438996693875 251082040129259158495040813)
  ·
    refine ⟨94155765048472184435640305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251082040129259158495040813 94155765048472184435640305)
    ·
      refine ⟨70616823786354138326730229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94155765048472184435640305 70616823786354138326730229)
      ·
        refine ⟨6620327229970700468130959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70616823786354138326730229 6620327229970700468130959)
        ·
          refine ⟨9930490844956050702196439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6620327229970700468130959 9930490844956050702196439)
          ·
            refine ⟨14895736267434076053294659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9930490844956050702196439 14895736267434076053294659)
            ·
              refine ⟨22343604401151114079941989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14895736267434076053294659 22343604401151114079941989)
              ·
                refine ⟨4189425825215833889989123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22343604401151114079941989 4189425825215833889989123)
                ·
                  refine ⟨6284138737823750834983685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4189425825215833889989123 6284138737823750834983685)
                  ·
                    refine ⟨1178276013341953281559441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6284138737823750834983685 1178276013341953281559441)
                    ·
                      rfl

theorem cell23_6884053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_6884053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884053 prefixEnd_6884053 := by exact prefixLift 6884053
  have htrace : WordTrace (prefixWord ++ tailWord_6884053) baseStart_6884053 baseEnd_6884053 := by
    simpa [prefixWord, tailWord_6884053, baseEnd_6884053] using wordTrace_append hprefix tailTrace_6884053
  have hstable : (prefixWord ++ tailWord_6884053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884053).length < 2 ^ (prefixWord ++ tailWord_6884053).sum := by decide
  have hdescent : baseEnd_6884053 < baseStart_6884053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884092 : List Nat := [2, 2, 2, 1, 3, 2, 2, 2, 1, 6]
def baseStart_6884092 : Nat := 118140960795 + 6884092 * 2 ^ 59
def prefixEnd_6884092 : Nat := 4983230072969 + 3 ^ 40 * 6884092 * 2
def baseEnd_6884092 : Nat := 1178282688590461730696881

theorem tailTrace_6884092 : CollatzResearch.WordTrace tailWord_6884092 prefixEnd_6884092 1178282688590461730696881 := by
  unfold tailWord_6884092
  simp only [CollatzResearch.WordTrace]
  refine ⟨125541731288058934077855265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167388975050745245437140353 125541731288058934077855265)
  ·
    refine ⟨94156298466044200558391449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125541731288058934077855265 94156298466044200558391449)
    ·
      refine ⟨70617223849533150418793587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94156298466044200558391449 70617223849533150418793587)
      ·
        refine ⟨105925835774299725628190381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70617223849533150418793587 105925835774299725628190381)
        ·
          refine ⟨39722188415362397110571393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105925835774299725628190381 39722188415362397110571393)
          ·
            refine ⟨29791641311521797832928545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39722188415362397110571393 29791641311521797832928545)
            ·
              refine ⟨22343730983641348374696409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29791641311521797832928545 22343730983641348374696409)
              ·
                refine ⟨16757798237731011281022307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22343730983641348374696409 16757798237731011281022307)
                ·
                  refine ⟨25136697356596516921533461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16757798237731011281022307 25136697356596516921533461)
                  ·
                    refine ⟨1178282688590461730696881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25136697356596516921533461 1178282688590461730696881)
                    ·
                      rfl

theorem cell23_6884092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_6884092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884092 prefixEnd_6884092 := by exact prefixLift 6884092
  have htrace : WordTrace (prefixWord ++ tailWord_6884092) baseStart_6884092 baseEnd_6884092 := by
    simpa [prefixWord, tailWord_6884092, baseEnd_6884092] using wordTrace_append hprefix tailTrace_6884092
  have hstable : (prefixWord ++ tailWord_6884092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884092).length < 2 ^ (prefixWord ++ tailWord_6884092).sum := by decide
  have hdescent : baseEnd_6884092 < baseStart_6884092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884095 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 6]
def baseStart_6884095 : Nat := 118140960795 + 6884095 * 2 ^ 59
def prefixEnd_6884095 : Nat := 4983230072969 + 3 ^ 40 * 6884095 * 2
def baseEnd_6884095 : Nat := 3534849606213348680353129

theorem tailTrace_6884095 : CollatzResearch.WordTrace tailWord_6884095 prefixEnd_6884095 3534849606213348680353129 := by
  unfold tailWord_6884095
  simp only [CollatzResearch.WordTrace]
  refine ⟨251083571995106999668069739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167389047996737999778713159 251083571995106999668069739)
  ·
    refine ⟨376625357992660499502104609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251083571995106999668069739 376625357992660499502104609)
    ·
      refine ⟨282469018494495374626578457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376625357992660499502104609 282469018494495374626578457)
      ·
        refine ⟨211851763870871530969933843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282469018494495374626578457 211851763870871530969933843)
        ·
          refine ⟨317777645806307296454900765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211851763870871530969933843 317777645806307296454900765)
          ·
            refine ⟨119166617177365236170587787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317777645806307296454900765 119166617177365236170587787)
            ·
              refine ⟨178749925766047854255881681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119166617177365236170587787 178749925766047854255881681)
              ·
                refine ⟨134062444324535890691911261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178749925766047854255881681 134062444324535890691911261)
                ·
                  refine ⟨50273416621700959009466723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134062444324535890691911261 50273416621700959009466723)
                  ·
                    refine ⟨75410124932551438514200085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50273416621700959009466723 75410124932551438514200085)
                    ·
                      refine ⟨3534849606213348680353129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75410124932551438514200085 3534849606213348680353129)
                      ·
                        rfl

theorem cell23_6884095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_6884095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884095 prefixEnd_6884095 := by exact prefixLift 6884095
  have htrace : WordTrace (prefixWord ++ tailWord_6884095) baseStart_6884095 baseEnd_6884095 := by
    simpa [prefixWord, tailWord_6884095, baseEnd_6884095] using wordTrace_append hprefix tailTrace_6884095
  have hstable : (prefixWord ++ tailWord_6884095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884095).length < 2 ^ (prefixWord ++ tailWord_6884095).sum := by decide
  have hdescent : baseEnd_6884095 < baseStart_6884095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884099 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 7, 2, 2]
def baseStart_6884099 : Nat := 118140960795 + 6884099 * 2 ^ 59
def prefixEnd_6884099 : Nat := 4983230072969 + 3 ^ 40 * 6884099 * 2
def baseEnd_6884099 : Nat := 3534851660135966664703111

theorem tailTrace_6884099 : CollatzResearch.WordTrace tailWord_6884099 prefixEnd_6884099 3534851660135966664703111 := by
  unfold tailWord_6884099
  simp only [CollatzResearch.WordTrace]
  refine ⟨251083717887092508351215351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167389145258061672234143567 251083717887092508351215351)
  ·
    refine ⟨376625576830638762526823027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251083717887092508351215351 376625576830638762526823027)
    ·
      refine ⟨564938365245958143790234541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376625576830638762526823027 564938365245958143790234541)
      ·
        refine ⟨211851886967234303921337953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 564938365245958143790234541 211851886967234303921337953)
        ·
          refine ⟨158888915225425727941003465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211851886967234303921337953 158888915225425727941003465)
          ·
            refine ⟨119166686419069295955752599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158888915225425727941003465 119166686419069295955752599)
            ·
              refine ⟨178750029628603943933628899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119166686419069295955752599 178750029628603943933628899)
              ·
                refine ⟨268125044442905915900443349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178750029628603943933628899 268125044442905915900443349)
                ·
                  refine ⟨6284180729130607403916641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 268125044442905915900443349 6284180729130607403916641)
                  ·
                    refine ⟨4713135546847955552937481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6284180729130607403916641 4713135546847955552937481)
                    ·
                      refine ⟨3534851660135966664703111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4713135546847955552937481 3534851660135966664703111)
                      ·
                        rfl

theorem cell23_6884099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 7, 2, 2].length) (baseStart_6884099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884099 prefixEnd_6884099 := by exact prefixLift 6884099
  have htrace : WordTrace (prefixWord ++ tailWord_6884099) baseStart_6884099 baseEnd_6884099 := by
    simpa [prefixWord, tailWord_6884099, baseEnd_6884099] using wordTrace_append hprefix tailTrace_6884099
  have hstable : (prefixWord ++ tailWord_6884099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884099).length < 2 ^ (prefixWord ++ tailWord_6884099).sum := by decide
  have hdescent : baseEnd_6884099 < baseStart_6884099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884119 : List Nat := [1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 5]
def baseStart_6884119 : Nat := 118140960795 + 6884119 * 2 ^ 59
def prefixEnd_6884119 : Nat := 4983230072969 + 3 ^ 40 * 6884119 * 2
def baseEnd_6884119 : Nat := 3534861929749056586453019

theorem tailTrace_6884119 : CollatzResearch.WordTrace tailWord_6884119 prefixEnd_6884119 3534861929749056586453019 := by
  unfold tailWord_6884119
  simp only [CollatzResearch.WordTrace]
  refine ⟨251084447347020051766943411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167389631564680034511295607 251084447347020051766943411)
  ·
    refine ⟨376626671020530077650415117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251084447347020051766943411 376626671020530077650415117)
    ·
      refine ⟨141235001632698779118905669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 376626671020530077650415117 141235001632698779118905669)
      ·
        refine ⟨26481562806131021084794813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141235001632698779118905669 26481562806131021084794813)
        ·
          refine ⟨9930586052299132906798055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26481562806131021084794813 9930586052299132906798055)
          ·
            refine ⟨14895879078448699360197083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9930586052299132906798055 14895879078448699360197083)
            ·
              refine ⟨22343818617673049040295625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14895879078448699360197083 22343818617673049040295625)
              ·
                refine ⟨16757863963254786780221719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22343818617673049040295625 16757863963254786780221719)
                ·
                  refine ⟨25136795944882180170332579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16757863963254786780221719 25136795944882180170332579)
                  ·
                    refine ⟨37705193917323270255498869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25136795944882180170332579 37705193917323270255498869)
                    ·
                      refine ⟨3534861929749056586453019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37705193917323270255498869 3534861929749056586453019)
                      ·
                        rfl

theorem cell23_6884119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_6884119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884119 prefixEnd_6884119 := by exact prefixLift 6884119
  have htrace : WordTrace (prefixWord ++ tailWord_6884119) baseStart_6884119 baseEnd_6884119 := by
    simpa [prefixWord, tailWord_6884119, baseEnd_6884119] using wordTrace_append hprefix tailTrace_6884119
  have hstable : (prefixWord ++ tailWord_6884119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884119).length < 2 ^ (prefixWord ++ tailWord_6884119).sum := by decide
  have hdescent : baseEnd_6884119 < baseStart_6884119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884136 : List Nat := [2, 1, 5, 1, 1, 1, 4, 2, 1, 2, 3]
def baseStart_6884136 : Nat := 118140960795 + 6884136 * 2 ^ 59
def prefixEnd_6884136 : Nat := 4983230072969 + 3 ^ 40 * 6884136 * 2
def baseEnd_6884136 : Nat := 3534870658920183019940441

theorem tailTrace_6884136 : CollatzResearch.WordTrace tailWord_6884136 prefixEnd_6884136 3534870658920183019940441 := by
  unfold tailWord_6884136
  simp only [CollatzResearch.WordTrace]
  refine ⟨125542533693979231835156131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167390044925305642446874841 125542533693979231835156131)
  ·
    refine ⟨188313800540968847752734197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125542533693979231835156131 188313800540968847752734197)
    ·
      refine ⟨17654418800715829476818831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188313800540968847752734197 17654418800715829476818831)
      ·
        refine ⟨26481628201073744215228247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17654418800715829476818831 26481628201073744215228247)
        ·
          refine ⟨39722442301610616322842371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26481628201073744215228247 39722442301610616322842371)
          ·
            refine ⟨59583663452415924484263557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39722442301610616322842371 59583663452415924484263557)
            ·
              refine ⟨11171936897327985840799417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59583663452415924484263557 11171936897327985840799417)
              ·
                refine ⟨8378952672995989380599563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11171936897327985840799417 8378952672995989380599563)
                ·
                  refine ⟨12568429009493984070899345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8378952672995989380599563 12568429009493984070899345)
                  ·
                    refine ⟨9426321757120488053174509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12568429009493984070899345 9426321757120488053174509)
                    ·
                      refine ⟨3534870658920183019940441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9426321757120488053174509 3534870658920183019940441)
                      ·
                        rfl

theorem cell23_6884136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_6884136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884136 prefixEnd_6884136 := by exact prefixLift 6884136
  have htrace : WordTrace (prefixWord ++ tailWord_6884136) baseStart_6884136 baseEnd_6884136 := by
    simpa [prefixWord, tailWord_6884136, baseEnd_6884136] using wordTrace_append hprefix tailTrace_6884136
  have hstable : (prefixWord ++ tailWord_6884136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884136).length < 2 ^ (prefixWord ++ tailWord_6884136).sum := by decide
  have hdescent : baseEnd_6884136 < baseStart_6884136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884183 : List Nat := [1, 1, 3, 2, 4, 1, 4, 1, 2, 1, 3]
def baseStart_6884183 : Nat := 118140960795 + 6884183 * 2 ^ 59
def prefixEnd_6884183 : Nat := 4983230072969 + 3 ^ 40 * 6884183 * 2
def baseEnd_6884183 : Nat := 3534894792510944336052725

theorem tailTrace_6884183 : CollatzResearch.WordTrace tailWord_6884183 prefixEnd_6884183 3534894792510944336052725 := by
  unfold tailWord_6884183
  simp only [CollatzResearch.WordTrace]
  refine ⟨251086781618788190697273203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167391187745858793798182135 251086781618788190697273203)
  ·
    refine ⟨376630172428182286045909805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251086781618788190697273203 376630172428182286045909805)
    ·
      refine ⟨141236314660568357267216177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 376630172428182286045909805 141236314660568357267216177)
      ·
        refine ⟨105927235995426267950412133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141236314660568357267216177 105927235995426267950412133)
        ·
          refine ⟨19861356749142425240702275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105927235995426267950412133 19861356749142425240702275)
          ·
            refine ⟨29792035123713637861053413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19861356749142425240702275 29792035123713637861053413)
            ·
              refine ⟨5586006585696307098947515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29792035123713637861053413 5586006585696307098947515)
              ·
                refine ⟨8379009878544460648421273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5586006585696307098947515 8379009878544460648421273)
                ·
                  refine ⟨6284257408908345486315955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8379009878544460648421273 6284257408908345486315955)
                  ·
                    refine ⟨9426386113362518229473933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6284257408908345486315955 9426386113362518229473933)
                    ·
                      refine ⟨3534894792510944336052725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9426386113362518229473933 3534894792510944336052725)
                      ·
                        rfl

theorem cell23_6884183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 2, 1, 3].length) (baseStart_6884183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884183 prefixEnd_6884183 := by exact prefixLift 6884183
  have htrace : WordTrace (prefixWord ++ tailWord_6884183) baseStart_6884183 baseEnd_6884183 := by
    simpa [prefixWord, tailWord_6884183, baseEnd_6884183] using wordTrace_append hprefix tailTrace_6884183
  have hstable : (prefixWord ++ tailWord_6884183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884183).length < 2 ^ (prefixWord ++ tailWord_6884183).sum := by decide
  have hdescent : baseEnd_6884183 < baseStart_6884183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884192 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 5]
def baseStart_6884192 : Nat := 118140960795 + 6884192 * 2 ^ 59
def prefixEnd_6884192 : Nat := 4983230072969 + 3 ^ 40 * 6884192 * 2
def baseEnd_6884192 : Nat := 3534899413836834800840183

theorem tailTrace_6884192 : CollatzResearch.WordTrace tailWord_6884192 prefixEnd_6884192 3534899413836834800840183 := by
  unfold tailWord_6884192
  simp only [CollatzResearch.WordTrace]
  refine ⟨125543554937877792617175415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167391406583837056822900553 125543554937877792617175415)
  ·
    refine ⟨188315332406816688925763123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125543554937877792617175415 188315332406816688925763123)
    ·
      refine ⟨282472998610225033388644685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188315332406816688925763123 282472998610225033388644685)
      ·
        refine ⟨105927374478834387520741757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282472998610225033388644685 105927374478834387520741757)
        ·
          refine ⟨39722765429562895320278159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105927374478834387520741757 39722765429562895320278159)
          ·
            refine ⟨59584148144344342980417239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39722765429562895320278159 59584148144344342980417239)
            ·
              refine ⟨89376222216516514470625859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59584148144344342980417239 89376222216516514470625859)
              ·
                refine ⟨134064333324774771705938789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89376222216516514470625859 134064333324774771705938789)
                ·
                  refine ⟨25137062498395269694863523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134064333324774771705938789 25137062498395269694863523)
                  ·
                    refine ⟨37705593747592904542295285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25137062498395269694863523 37705593747592904542295285)
                    ·
                      refine ⟨3534899413836834800840183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37705593747592904542295285 3534899413836834800840183)
                      ·
                        rfl

theorem cell23_6884192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_6884192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884192 prefixEnd_6884192 := by exact prefixLift 6884192
  have htrace : WordTrace (prefixWord ++ tailWord_6884192) baseStart_6884192 baseEnd_6884192 := by
    simpa [prefixWord, tailWord_6884192, baseEnd_6884192] using wordTrace_append hprefix tailTrace_6884192
  have hstable : (prefixWord ++ tailWord_6884192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884192).length < 2 ^ (prefixWord ++ tailWord_6884192).sum := by decide
  have hdescent : baseEnd_6884192 < baseStart_6884192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884249 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 4, 5, 2]
def baseStart_6884249 : Nat := 118140960795 + 6884249 * 2 ^ 59
def prefixEnd_6884249 : Nat := 4983230072969 + 3 ^ 40 * 6884249 * 2
def baseEnd_6884249 : Nat := 3534928682234141077827421

theorem tailTrace_6884249 : CollatzResearch.WordTrace tailWord_6884249 prefixEnd_6884249 3534928682234141077827421 := by
  unfold tailWord_6884249
  simp only [CollatzResearch.WordTrace]
  refine ⟨251089188836549083969175801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167392792557699389312783867 251089188836549083969175801)
  ·
    refine ⟨188316891627411812976881851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251089188836549083969175801 188316891627411812976881851)
    ·
      refine ⟨282475337441117719465322777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188316891627411812976881851 282475337441117719465322777)
      ·
        refine ⟨211856503080838289598992083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282475337441117719465322777 211856503080838289598992083)
        ·
          refine ⟨317784754621257434398488125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211856503080838289598992083 317784754621257434398488125)
          ·
            refine ⟨119169282982971537899433047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317784754621257434398488125 119169282982971537899433047)
            ·
              refine ⟨178753924474457306849149571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119169282982971537899433047 178753924474457306849149571)
              ·
                refine ⟨268130886711685960273724357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178753924474457306849149571 268130886711685960273724357)
                ·
                  refine ⟨50274541258441117551323317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 268130886711685960273724357 50274541258441117551323317)
                  ·
                    refine ⟨4713238242978854770436561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50274541258441117551323317 4713238242978854770436561)
                    ·
                      refine ⟨3534928682234141077827421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4713238242978854770436561 3534928682234141077827421)
                      ·
                        rfl

theorem cell23_6884249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 5, 2].length) (baseStart_6884249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884249 prefixEnd_6884249 := by exact prefixLift 6884249
  have htrace : WordTrace (prefixWord ++ tailWord_6884249) baseStart_6884249 baseEnd_6884249 := by
    simpa [prefixWord, tailWord_6884249, baseEnd_6884249] using wordTrace_append hprefix tailTrace_6884249
  have hstable : (prefixWord ++ tailWord_6884249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884249).length < 2 ^ (prefixWord ++ tailWord_6884249).sum := by decide
  have hdescent : baseEnd_6884249 < baseStart_6884249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884259 : List Nat := [1, 1, 1, 4, 1, 2, 5, 1, 2, 5]
def baseStart_6884259 : Nat := 118140960795 + 6884259 * 2 ^ 59
def prefixEnd_6884259 : Nat := 4983230072969 + 3 ^ 40 * 6884259 * 2
def baseEnd_6884259 : Nat := 1178311272346895346234125

theorem tailTrace_6884259 : CollatzResearch.WordTrace tailWord_6884259 prefixEnd_6884259 1178311272346895346234125 := by
  unfold tailWord_6884259
  simp only [CollatzResearch.WordTrace]
  refine ⟨251089553566512855677039831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167393035711008570451359887 251089553566512855677039831)
  ·
    refine ⟨376634330349769283515559747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251089553566512855677039831 376634330349769283515559747)
    ·
      refine ⟨564951495524653925273339621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376634330349769283515559747 564951495524653925273339621)
      ·
        refine ⟨105928405410872610988751179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 564951495524653925273339621 105928405410872610988751179)
        ·
          refine ⟨158892608116308916483126769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105928405410872610988751179 158892608116308916483126769)
          ·
            refine ⟨119169456087231687362345077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158892608116308916483126769 119169456087231687362345077)
            ·
              refine ⟨11172136508177970690219851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119169456087231687362345077 11172136508177970690219851)
              ·
                refine ⟨16758204762266956035329777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11172136508177970690219851 16758204762266956035329777)
                ·
                  refine ⟨12568653571700217026497333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16758204762266956035329777 12568653571700217026497333)
                  ·
                    refine ⟨1178311272346895346234125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12568653571700217026497333 1178311272346895346234125)
                    ·
                      rfl

theorem cell23_6884259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 5].length) (baseStart_6884259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884259 prefixEnd_6884259 := by exact prefixLift 6884259
  have htrace : WordTrace (prefixWord ++ tailWord_6884259) baseStart_6884259 baseEnd_6884259 := by
    simpa [prefixWord, tailWord_6884259, baseEnd_6884259] using wordTrace_append hprefix tailTrace_6884259
  have hstable : (prefixWord ++ tailWord_6884259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884259).length < 2 ^ (prefixWord ++ tailWord_6884259).sum := by decide
  have hdescent : baseEnd_6884259 < baseStart_6884259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884263 : List Nat := [1, 1, 6, 1, 3, 1, 2, 3, 5]
def baseStart_6884263 : Nat := 118140960795 + 6884263 * 2 ^ 59
def prefixEnd_6884263 : Nat := 4983230072969 + 3 ^ 40 * 6884263 * 2
def baseEnd_6884263 : Nat := 392770652329256002561373

theorem tailTrace_6884263 : CollatzResearch.WordTrace tailWord_6884263 prefixEnd_6884263 392770652329256002561373 := by
  unfold tailWord_6884263
  simp only [CollatzResearch.WordTrace]
  refine ⟨251089699458498364360185443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167393132972332242906790295 251089699458498364360185443)
  ·
    refine ⟨376634549187747546540278165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251089699458498364360185443 376634549187747546540278165)
    ·
      refine ⟨17654744493175666244075539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 376634549187747546540278165 17654744493175666244075539)
      ·
        refine ⟨26482116739763499366113309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17654744493175666244075539 26482116739763499366113309)
        ·
          refine ⟨9930793777411312262292491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26482116739763499366113309 9930793777411312262292491)
          ·
            refine ⟨14896190666116968393438737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9930793777411312262292491 14896190666116968393438737)
            ·
              refine ⟨11172142999587726295079053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14896190666116968393438737 11172142999587726295079053)
              ·
                refine ⟨4189553624845397360654645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11172142999587726295079053 4189553624845397360654645)
                ·
                  refine ⟨392770652329256002561373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4189553624845397360654645 392770652329256002561373)
                  ·
                    rfl

theorem cell23_6884263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 3, 5].length) (baseStart_6884263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884263 prefixEnd_6884263 := by exact prefixLift 6884263
  have htrace : WordTrace (prefixWord ++ tailWord_6884263) baseStart_6884263 baseEnd_6884263 := by
    simpa [prefixWord, tailWord_6884263, baseEnd_6884263] using wordTrace_append hprefix tailTrace_6884263
  have hstable : (prefixWord ++ tailWord_6884263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884263).length < 2 ^ (prefixWord ++ tailWord_6884263).sum := by decide
  have hdescent : baseEnd_6884263 < baseStart_6884263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884279 : List Nat := [1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 4]
def baseStart_6884279 : Nat := 118140960795 + 6884279 * 2 ^ 59
def prefixEnd_6884279 : Nat := 4983230072969 + 3 ^ 40 * 6884279 * 2
def baseEnd_6884279 : Nat := 3534944086653775960452283

theorem tailTrace_6884279 : CollatzResearch.WordTrace tailWord_6884279 prefixEnd_6884279 3534944086653775960452283 := by
  unfold tailWord_6884279
  simp only [CollatzResearch.WordTrace]
  refine ⟨251090283026440399092767891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167393522017626932728511927 251090283026440399092767891)
  ·
    refine ⟨376635424539660598639151837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251090283026440399092767891 376635424539660598639151837)
    ·
      refine ⟨141238284202372724489681939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 376635424539660598639151837 141238284202372724489681939)
      ·
        refine ⟨211857426303559086734522909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141238284202372724489681939 211857426303559086734522909)
        ·
          refine ⟨79446534863834657525446091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211857426303559086734522909 79446534863834657525446091)
          ·
            refine ⟨119169802295751986288169137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79446534863834657525446091 119169802295751986288169137)
            ·
              refine ⟨89377351721813989716126853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119169802295751986288169137 89377351721813989716126853)
              ·
                refine ⟨16758253447840123071773785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89377351721813989716126853 16758253447840123071773785)
                ·
                  refine ⟨12568690085880092303830339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16758253447840123071773785 12568690085880092303830339)
                  ·
                    refine ⟨18853035128820138455745509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12568690085880092303830339 18853035128820138455745509)
                    ·
                      refine ⟨3534944086653775960452283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18853035128820138455745509 3534944086653775960452283)
                      ·
                        rfl

theorem cell23_6884279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_6884279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884279 prefixEnd_6884279 := by exact prefixLift 6884279
  have htrace : WordTrace (prefixWord ++ tailWord_6884279) baseStart_6884279 baseEnd_6884279 := by
    simpa [prefixWord, tailWord_6884279, baseEnd_6884279] using wordTrace_append hprefix tailTrace_6884279
  have hstable : (prefixWord ++ tailWord_6884279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884279).length < 2 ^ (prefixWord ++ tailWord_6884279).sum := by decide
  have hdescent : baseEnd_6884279 < baseStart_6884279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884299 : List Nat := [1, 1, 1, 1, 3, 5, 1, 2, 1, 4, 3]
def baseStart_6884299 : Nat := 118140960795 + 6884299 * 2 ^ 59
def prefixEnd_6884299 : Nat := 4983230072969 + 3 ^ 40 * 6884299 * 2
def baseEnd_6884299 : Nat := 3534954356266865882202191

theorem tailTrace_6884299 : CollatzResearch.WordTrace tailWord_6884299 prefixEnd_6884299 3534954356266865882202191 := by
  unfold tailWord_6884299
  simp only [CollatzResearch.WordTrace]
  refine ⟨251091012486367942508495951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167394008324245295005663967 251091012486367942508495951)
  ·
    refine ⟨376636518729551913762743927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251091012486367942508495951 376636518729551913762743927)
    ·
      refine ⟨564954778094327870644115891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376636518729551913762743927 564954778094327870644115891)
      ·
        refine ⟨847432167141491805966173837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564954778094327870644115891 847432167141491805966173837)
        ·
          refine ⟨317787062678059427237315189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 847432167141491805966173837 317787062678059427237315189)
          ·
            refine ⟨29792537126068071303498299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 317787062678059427237315189 29792537126068071303498299)
            ·
              refine ⟨44688805689102106955247449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29792537126068071303498299 44688805689102106955247449)
              ·
                refine ⟨33516604266826580216435587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44688805689102106955247449 33516604266826580216435587)
                ·
                  refine ⟨50274906400239870324653381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33516604266826580216435587 50274906400239870324653381)
                  ·
                    refine ⟨9426544950044975685872509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50274906400239870324653381 9426544950044975685872509)
                    ·
                      refine ⟨3534954356266865882202191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9426544950044975685872509 3534954356266865882202191)
                      ·
                        rfl

theorem cell23_6884299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 4, 3].length) (baseStart_6884299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884299 prefixEnd_6884299 := by exact prefixLift 6884299
  have htrace : WordTrace (prefixWord ++ tailWord_6884299) baseStart_6884299 baseEnd_6884299 := by
    simpa [prefixWord, tailWord_6884299, baseEnd_6884299] using wordTrace_append hprefix tailTrace_6884299
  have hstable : (prefixWord ++ tailWord_6884299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884299).length < 2 ^ (prefixWord ++ tailWord_6884299).sum := by decide
  have hdescent : baseEnd_6884299 < baseStart_6884299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884349 : List Nat := [1, 4, 1, 1, 1, 2, 1, 4, 3, 5]
def baseStart_6884349 : Nat := 118140960795 + 6884349 * 2 ^ 59
def prefixEnd_6884349 : Nat := 4983230072969 + 3 ^ 40 * 6884349 * 2
def baseEnd_6884349 : Nat := 1178326676766530228858987

theorem tailTrace_6884349 : CollatzResearch.WordTrace tailWord_6884349 prefixEnd_6884349 1178326676766530228858987 := by
  unfold tailWord_6884349
  simp only [CollatzResearch.WordTrace]
  refine ⟨251092836136186801047816101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167395224090791200698544067 251092836136186801047816101)
  ·
    refine ⟨47079906775535025196465519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251092836136186801047816101 47079906775535025196465519)
    ·
      refine ⟨70619860163302537794698279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47079906775535025196465519 70619860163302537794698279)
      ·
        refine ⟨105929790244953806692047419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70619860163302537794698279 105929790244953806692047419)
        ·
          refine ⟨158894685367430710038071129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105929790244953806692047419 158894685367430710038071129)
          ·
            refine ⟨119171014025573032528553347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158894685367430710038071129 119171014025573032528553347)
            ·
              refine ⟨178756521038359548792830021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119171014025573032528553347 178756521038359548792830021)
              ·
                refine ⟨33516847694692415398655629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 178756521038359548792830021 33516847694692415398655629)
                ·
                  refine ⟨12568817885509655774495861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33516847694692415398655629 12568817885509655774495861)
                  ·
                    refine ⟨1178326676766530228858987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12568817885509655774495861 1178326676766530228858987)
                    ·
                      rfl

theorem cell23_6884349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_6884349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884349 prefixEnd_6884349 := by exact prefixLift 6884349
  have htrace : WordTrace (prefixWord ++ tailWord_6884349) baseStart_6884349 baseEnd_6884349 := by
    simpa [prefixWord, tailWord_6884349, baseEnd_6884349] using wordTrace_append hprefix tailTrace_6884349
  have hstable : (prefixWord ++ tailWord_6884349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884349).length < 2 ^ (prefixWord ++ tailWord_6884349).sum := by decide
  have hdescent : baseEnd_6884349 < baseStart_6884349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884353 : List Nat := [1, 2, 4, 1, 2, 4, 2, 1, 6]
def baseStart_6884353 : Nat := 118140960795 + 6884353 * 2 ^ 59
def prefixEnd_6884353 : Nat := 4983230072969 + 3 ^ 40 * 6884353 * 2
def baseEnd_6884353 : Nat := 392775787135800963436327

theorem tailTrace_6884353 : CollatzResearch.WordTrace tailWord_6884353 prefixEnd_6884353 392775787135800963436327 := by
  unfold tailWord_6884353
  simp only [CollatzResearch.WordTrace]
  refine ⟨251092982028172309730961713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167395321352114873153974475 251092982028172309730961713)
  ·
    refine ⟨188319736521129232298221285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251092982028172309730961713 188319736521129232298221285)
    ·
      refine ⟨35309950597711731055916491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188319736521129232298221285 35309950597711731055916491)
      ·
        refine ⟨52964925896567596583874737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35309950597711731055916491 52964925896567596583874737)
        ·
          refine ⟨39723694422425697437906053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52964925896567596583874737 39723694422425697437906053)
          ·
            refine ⟨7448192704204818269607385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39723694422425697437906053 7448192704204818269607385)
            ·
              refine ⟨5586144528153613702205539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7448192704204818269607385 5586144528153613702205539)
              ·
                refine ⟨8379216792230420553308309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5586144528153613702205539 8379216792230420553308309)
                ·
                  refine ⟨392775787135800963436327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8379216792230420553308309 392775787135800963436327)
                  ·
                    rfl

theorem cell23_6884353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 6].length) (baseStart_6884353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884353 prefixEnd_6884353 := by exact prefixLift 6884353
  have htrace : WordTrace (prefixWord ++ tailWord_6884353) baseStart_6884353 baseEnd_6884353 := by
    simpa [prefixWord, tailWord_6884353, baseEnd_6884353] using wordTrace_append hprefix tailTrace_6884353
  have hstable : (prefixWord ++ tailWord_6884353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884353).length < 2 ^ (prefixWord ++ tailWord_6884353).sum := by decide
  have hdescent : baseEnd_6884353 < baseStart_6884353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884366 : List Nat := [4, 1, 1, 2, 2, 3, 1, 1, 3, 5]
def baseStart_6884366 : Nat := 118140960795 + 6884366 * 2 ^ 59
def prefixEnd_6884366 : Nat := 4983230072969 + 3 ^ 40 * 6884366 * 2
def baseEnd_6884366 : Nat := 1178329586490239040021461

theorem tailTrace_6884366 : CollatzResearch.WordTrace tailWord_6884366 prefixEnd_6884366 1178329586490239040021461 := by
  unfold tailWord_6884366
  simp only [CollatzResearch.WordTrace]
  refine ⟨31386682022140651618898119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167395637451416808634123301 31386682022140651618898119)
  ·
    refine ⟨47080023033210977428347179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31386682022140651618898119 47080023033210977428347179)
    ·
      refine ⟨70620034549816466142520769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47080023033210977428347179 70620034549816466142520769)
      ·
        refine ⟨52965025912362349606890577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70620034549816466142520769 52965025912362349606890577)
        ·
          refine ⟨39723769434271762205167933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52965025912362349606890577 39723769434271762205167933)
          ·
            refine ⟨14896413537851910826937975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39723769434271762205167933 14896413537851910826937975)
            ·
              refine ⟨22344620306777866240406963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14896413537851910826937975 22344620306777866240406963)
              ·
                refine ⟨33516930460166799360610445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22344620306777866240406963 33516930460166799360610445)
                ·
                  refine ⟨12568848922562549760228917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33516930460166799360610445 12568848922562549760228917)
                  ·
                    refine ⟨1178329586490239040021461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12568848922562549760228917 1178329586490239040021461)
                    ·
                      rfl

theorem cell23_6884366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_6884366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884366 prefixEnd_6884366 := by exact prefixLift 6884366
  have htrace : WordTrace (prefixWord ++ tailWord_6884366) baseStart_6884366 baseEnd_6884366 := by
    simpa [prefixWord, tailWord_6884366, baseEnd_6884366] using wordTrace_append hprefix tailTrace_6884366
  have hstable : (prefixWord ++ tailWord_6884366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884366).length < 2 ^ (prefixWord ++ tailWord_6884366).sum := by decide
  have hdescent : baseEnd_6884366 < baseStart_6884366 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884373 : List Nat := [1, 3, 2, 1, 4, 1, 1, 3, 2, 3, 2]
def baseStart_6884373 : Nat := 118140960795 + 6884373 * 2 ^ 59
def prefixEnd_6884373 : Nat := 4983230072969 + 3 ^ 40 * 6884373 * 2
def baseEnd_6884373 : Nat := 3534992353835298592676851

theorem tailTrace_6884373 : CollatzResearch.WordTrace tailWord_6884373 prefixEnd_6884373 3534992353835298592676851 := by
  unfold tailWord_6884373
  simp only [CollatzResearch.WordTrace]
  refine ⟨251093711488099853146689773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167395807658733235431126515 251093711488099853146689773)
  ·
    refine ⟨94160141808037444930008665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251093711488099853146689773 94160141808037444930008665)
    ·
      refine ⟨70620106356028083697506499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94160141808037444930008665 70620106356028083697506499)
      ·
        refine ⟨105930159534042125546259749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70620106356028083697506499 105930159534042125546259749)
        ·
          refine ⟨19861904912632898539923703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105930159534042125546259749 19861904912632898539923703)
          ·
            refine ⟨29792857368949347809885555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19861904912632898539923703 29792857368949347809885555)
            ·
              refine ⟨44689286053424021714828333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29792857368949347809885555 44689286053424021714828333)
              ·
                refine ⟨16758482270034008143060625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44689286053424021714828333 16758482270034008143060625)
                ·
                  refine ⟨12568861702525506107295469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16758482270034008143060625 12568861702525506107295469)
                  ·
                    refine ⟨4713323138447064790235801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12568861702525506107295469 4713323138447064790235801)
                    ·
                      refine ⟨3534992353835298592676851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4713323138447064790235801 3534992353835298592676851)
                      ·
                        rfl

theorem cell23_6884373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 3, 2].length) (baseStart_6884373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884373 prefixEnd_6884373 := by exact prefixLift 6884373
  have htrace : WordTrace (prefixWord ++ tailWord_6884373) baseStart_6884373 baseEnd_6884373 := by
    simpa [prefixWord, tailWord_6884373, baseEnd_6884373] using wordTrace_append hprefix tailTrace_6884373
  have hstable : (prefixWord ++ tailWord_6884373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884373).length < 2 ^ (prefixWord ++ tailWord_6884373).sum := by decide
  have hdescent : baseEnd_6884373 < baseStart_6884373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884383 : List Nat := [1, 1, 2, 4, 1, 4, 3, 1, 1, 5]
def baseStart_6884383 : Nat := 118140960795 + 6884383 * 2 ^ 59
def prefixEnd_6884383 : Nat := 4983230072969 + 3 ^ 40 * 6884383 * 2
def baseEnd_6884383 : Nat := 1178332496213947851183935

theorem tailTrace_6884383 : CollatzResearch.WordTrace tailWord_6884383 prefixEnd_6884383 1178332496213947851183935 := by
  unfold tailWord_6884383
  simp only [CollatzResearch.WordTrace]
  refine ⟨251094076218063624854553803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167396050812042416569702535 251094076218063624854553803)
  ·
    refine ⟨376641114327095437281830705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251094076218063624854553803 376641114327095437281830705)
    ·
      refine ⟨282480835745321577961373029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376641114327095437281830705 282480835745321577961373029)
      ·
        refine ⟨52965156702247795867757443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 282480835745321577961373029 52965156702247795867757443)
        ·
          refine ⟨79447735053371693801636165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52965156702247795867757443 79447735053371693801636165)
          ·
            refine ⟨14896450322507192587806781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79447735053371693801636165 14896450322507192587806781)
            ·
              refine ⟨5586168870940197220427543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14896450322507192587806781 5586168870940197220427543)
              ·
                refine ⟨8379253306410295830641315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5586168870940197220427543 8379253306410295830641315)
                ·
                  refine ⟨12568879959615443745961973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8379253306410295830641315 12568879959615443745961973)
                  ·
                    refine ⟨1178332496213947851183935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12568879959615443745961973 1178332496213947851183935)
                    ·
                      rfl

theorem cell23_6884383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 1, 5].length) (baseStart_6884383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884383 prefixEnd_6884383 := by exact prefixLift 6884383
  have htrace : WordTrace (prefixWord ++ tailWord_6884383) baseStart_6884383 baseEnd_6884383 := by
    simpa [prefixWord, tailWord_6884383, baseEnd_6884383] using wordTrace_append hprefix tailTrace_6884383
  have hstable : (prefixWord ++ tailWord_6884383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884383).length < 2 ^ (prefixWord ++ tailWord_6884383).sum := by decide
  have hdescent : baseEnd_6884383 < baseStart_6884383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884403 : List Nat := [1, 1, 1, 2, 4, 1, 1, 5, 3, 2, 2]
def baseStart_6884403 : Nat := 118140960795 + 6884403 * 2 ^ 59
def prefixEnd_6884403 : Nat := 4983230072969 + 3 ^ 40 * 6884403 * 2
def baseEnd_6884403 : Nat := 3535007758254933475301713

theorem tailTrace_6884403 : CollatzResearch.WordTrace tailWord_6884403 prefixEnd_6884403 3535007758254933475301713 := by
  unfold tailWord_6884403
  simp only [CollatzResearch.WordTrace]
  refine ⟨251094805677991168270281863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167396537118660778846854575 251094805677991168270281863)
  ·
    refine ⟨376642208516986752405422795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251094805677991168270281863 376642208516986752405422795)
    ·
      refine ⟨564963312775480128608134193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376642208516986752405422795 564963312775480128608134193)
      ·
        refine ⟨423722484581610096456100645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 564963312775480128608134193 423722484581610096456100645)
        ·
          refine ⟨79447965859051893085518871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 423722484581610096456100645 79447965859051893085518871)
          ·
            refine ⟨119171948788577839628278307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79447965859051893085518871 119171948788577839628278307)
            ·
              refine ⟨178757923182866759442417461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119171948788577839628278307 178757923182866759442417461)
              ·
                refine ⟨16758555298393758697726637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 178757923182866759442417461 16758555298393758697726637)
                ·
                  refine ⟨6284458236897659511647489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16758555298393758697726637 6284458236897659511647489)
                  ·
                    refine ⟨4713343677673244633735617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6284458236897659511647489 4713343677673244633735617)
                    ·
                      refine ⟨3535007758254933475301713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4713343677673244633735617 3535007758254933475301713)
                      ·
                        rfl

theorem cell23_6884403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 3, 2, 2].length) (baseStart_6884403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884403 prefixEnd_6884403 := by exact prefixLift 6884403
  have htrace : WordTrace (prefixWord ++ tailWord_6884403) baseStart_6884403 baseEnd_6884403 := by
    simpa [prefixWord, tailWord_6884403, baseEnd_6884403] using wordTrace_append hprefix tailTrace_6884403
  have hstable : (prefixWord ++ tailWord_6884403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884403).length < 2 ^ (prefixWord ++ tailWord_6884403).sum := by decide
  have hdescent : baseEnd_6884403 < baseStart_6884403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884413 : List Nat := [1, 4, 1, 3, 1, 2, 2, 3, 2, 4]
def baseStart_6884413 : Nat := 118140960795 + 6884413 * 2 ^ 59
def prefixEnd_6884413 : Nat := 4983230072969 + 3 ^ 40 * 6884413 * 2
def baseEnd_6884413 : Nat := 1178337631020492812058889

theorem tailTrace_6884413 : CollatzResearch.WordTrace tailWord_6884413 prefixEnd_6884413 1178337631020492812058889 := by
  unfold tailWord_6884413
  simp only [CollatzResearch.WordTrace]
  refine ⟨251095170407954939978145893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167396780271969959985430595 251095170407954939978145893)
  ·
    refine ⟨47080344451491551245902355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251095170407954939978145893 47080344451491551245902355)
    ·
      refine ⟨70620516677237326868853533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47080344451491551245902355 70620516677237326868853533)
      ·
        refine ⟨26482693753963997575820075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70620516677237326868853533 26482693753963997575820075)
        ·
          refine ⟨39724040630945996363730113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26482693753963997575820075 39724040630945996363730113)
          ·
            refine ⟨29793030473209497272797585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39724040630945996363730113 29793030473209497272797585)
            ·
              refine ⟨22344772854907122954598189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29793030473209497272797585 22344772854907122954598189)
              ·
                refine ⟨8379289820590171107974321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22344772854907122954598189 8379289820590171107974321)
                ·
                  refine ⟨6284467365442628330980741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8379289820590171107974321 6284467365442628330980741)
                  ·
                    refine ⟨1178337631020492812058889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6284467365442628330980741 1178337631020492812058889)
                    ·
                      rfl

theorem cell23_6884413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_6884413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884413 prefixEnd_6884413 := by exact prefixLift 6884413
  have htrace : WordTrace (prefixWord ++ tailWord_6884413) baseStart_6884413 baseEnd_6884413 := by
    simpa [prefixWord, tailWord_6884413, baseEnd_6884413] using wordTrace_append hprefix tailTrace_6884413
  have hstable : (prefixWord ++ tailWord_6884413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884413).length < 2 ^ (prefixWord ++ tailWord_6884413).sum := by decide
  have hdescent : baseEnd_6884413 < baseStart_6884413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884416 : List Nat := [2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 4]
def baseStart_6884416 : Nat := 118140960795 + 6884416 * 2 ^ 59
def prefixEnd_6884416 : Nat := 4983230072969 + 3 ^ 40 * 6884416 * 2
def baseEnd_6884416 : Nat := 3535014433503441924439153

theorem tailTrace_6884416 : CollatzResearch.WordTrace tailWord_6884416 prefixEnd_6884416 3535014433503441924439153 := by
  unfold tailWord_6884416
  simp only [CollatzResearch.WordTrace]
  refine ⟨125547639913472035745252551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167396853217962714327003401 125547639913472035745252551)
  ·
    refine ⟨188321459870208053617878827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125547639913472035745252551 188321459870208053617878827)
    ·
      refine ⟨282482189805312080426818241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188321459870208053617878827 282482189805312080426818241)
      ·
        refine ⟨211861642353984060320113681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282482189805312080426818241 211861642353984060320113681)
        ·
          refine ⟨158896231765488045240085261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211861642353984060320113681 158896231765488045240085261)
          ·
            refine ⟨59586086912058016965031973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158896231765488045240085261 59586086912058016965031973)
            ·
              refine ⟨11172391296010878180943495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59586086912058016965031973 11172391296010878180943495)
              ·
                refine ⟨16758586944016317271415243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11172391296010878180943495 16758586944016317271415243)
                ·
                  refine ⟨25137880416024475907122865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16758586944016317271415243 25137880416024475907122865)
                  ·
                    refine ⟨18853410312018356930342149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25137880416024475907122865 18853410312018356930342149)
                    ·
                      refine ⟨3535014433503441924439153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18853410312018356930342149 3535014433503441924439153)
                      ·
                        rfl

theorem cell23_6884416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 4].length) (baseStart_6884416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884416 prefixEnd_6884416 := by exact prefixLift 6884416
  have htrace : WordTrace (prefixWord ++ tailWord_6884416) baseStart_6884416 baseEnd_6884416 := by
    simpa [prefixWord, tailWord_6884416, baseEnd_6884416] using wordTrace_append hprefix tailTrace_6884416
  have hstable : (prefixWord ++ tailWord_6884416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884416).length < 2 ^ (prefixWord ++ tailWord_6884416).sum := by decide
  have hdescent : baseEnd_6884416 < baseStart_6884416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884437 : List Nat := [1, 3, 2, 2, 1, 2, 4, 3, 1, 2, 2]
def baseStart_6884437 : Nat := 118140960795 + 6884437 * 2 ^ 59
def prefixEnd_6884437 : Nat := 4983230072969 + 3 ^ 40 * 6884437 * 2
def baseEnd_6884437 : Nat := 3535025216597186342276557

theorem tailTrace_6884437 : CollatzResearch.WordTrace tailWord_6884437 prefixEnd_6884437 3535025216597186342276557 := by
  unfold tailWord_6884437
  simp only [CollatzResearch.WordTrace]
  refine ⟨251096045759867992077019565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167397363839911994718013043 251096045759867992077019565)
  ·
    refine ⟨94161017159950497028882337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251096045759867992077019565 94161017159950497028882337)
    ·
      refine ⟨70620762869962872771661753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94161017159950497028882337 70620762869962872771661753)
      ·
        refine ⟨52965572152472154578746315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70620762869962872771661753 52965572152472154578746315)
        ·
          refine ⟨79448358228708231868119473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52965572152472154578746315 79448358228708231868119473)
          ·
            refine ⟨59586268671531173901089605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79448358228708231868119473 59586268671531173901089605)
            ·
              refine ⟨11172425375912095106454301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59586268671531173901089605 11172425375912095106454301)
              ·
                refine ⟨4189659515967035664920363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11172425375912095106454301 4189659515967035664920363)
                ·
                  refine ⟨6284489273950553497380545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4189659515967035664920363 6284489273950553497380545)
                  ·
                    refine ⟨4713366955462915123035409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6284489273950553497380545 4713366955462915123035409)
                    ·
                      refine ⟨3535025216597186342276557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4713366955462915123035409 3535025216597186342276557)
                      ·
                        rfl

theorem cell23_6884437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_6884437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884437 prefixEnd_6884437 := by exact prefixLift 6884437
  have htrace : WordTrace (prefixWord ++ tailWord_6884437) baseStart_6884437 baseEnd_6884437 := by
    simpa [prefixWord, tailWord_6884437, baseEnd_6884437] using wordTrace_append hprefix tailTrace_6884437
  have hstable : (prefixWord ++ tailWord_6884437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884437).length < 2 ^ (prefixWord ++ tailWord_6884437).sum := by decide
  have hdescent : baseEnd_6884437 < baseStart_6884437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884453 : List Nat := [1, 3, 1, 3, 2, 1, 3, 1, 4, 1, 3]
def baseStart_6884453 : Nat := 118140960795 + 6884453 * 2 ^ 59
def prefixEnd_6884453 : Nat := 4983230072969 + 3 ^ 40 * 6884453 * 2
def baseEnd_6884453 : Nat := 3535033432287658279676483

theorem tailTrace_6884453 : CollatzResearch.WordTrace tailWord_6884453 prefixEnd_6884453 3535033432287658279676483 := by
  unfold tailWord_6884453
  simp only [CollatzResearch.WordTrace]
  refine ⟨251096629327810026809602013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167397752885206684539734675 251096629327810026809602013)
  ·
    refine ⟨94161235997928760053600755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251096629327810026809602013 94161235997928760053600755)
    ·
      refine ⟨141241853996893140080401133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94161235997928760053600755 141241853996893140080401133)
      ·
        refine ⟨52965695248834927530150425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141241853996893140080401133 52965695248834927530150425)
        ·
          refine ⟨39724271436626195647612819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52965695248834927530150425 39724271436626195647612819)
          ·
            refine ⟨59586407154939293471419229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39724271436626195647612819 59586407154939293471419229)
            ·
              refine ⟨22344902683102235051782211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59586407154939293471419229 22344902683102235051782211)
              ·
                refine ⟨33517354024653352577673317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22344902683102235051782211 33517354024653352577673317)
                ·
                  refine ⟨6284503879622503608313747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33517354024653352577673317 6284503879622503608313747)
                  ·
                    refine ⟨9426755819433755412470621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6284503879622503608313747 9426755819433755412470621)
                    ·
                      refine ⟨3535033432287658279676483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9426755819433755412470621 3535033432287658279676483)
                      ·
                        rfl

theorem cell23_6884453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_6884453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884453 prefixEnd_6884453 := by exact prefixLift 6884453
  have htrace : WordTrace (prefixWord ++ tailWord_6884453) baseStart_6884453 baseEnd_6884453 := by
    simpa [prefixWord, tailWord_6884453, baseEnd_6884453] using wordTrace_append hprefix tailTrace_6884453
  have hstable : (prefixWord ++ tailWord_6884453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884453).length < 2 ^ (prefixWord ++ tailWord_6884453).sum := by decide
  have hdescent : baseEnd_6884453 < baseStart_6884453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884479 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 5]
def baseStart_6884479 : Nat := 118140960795 + 6884479 * 2 ^ 59
def prefixEnd_6884479 : Nat := 4983230072969 + 3 ^ 40 * 6884479 * 2
def baseEnd_6884479 : Nat := 3535046782784675177951363

theorem tailTrace_6884479 : CollatzResearch.WordTrace tailWord_6884479 prefixEnd_6884479 3535046782784675177951363 := by
  unfold tailWord_6884479
  simp only [CollatzResearch.WordTrace]
  refine ⟨251097577625715833250048491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167398385083810555500032327 251097577625715833250048491)
  ·
    refine ⟨376646366438573749875072737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251097577625715833250048491 376646366438573749875072737)
    ·
      refine ⟨282484774828930312406304553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376646366438573749875072737 282484774828930312406304553)
      ·
        refine ⟨211863581121697734304728415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282484774828930312406304553 211863581121697734304728415)
        ·
          refine ⟨317795371682546601457092623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211863581121697734304728415 317795371682546601457092623)
          ·
            refine ⟨476693057523819902185638935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317795371682546601457092623 476693057523819902185638935)
            ·
              refine ⟨715039586285729853278458403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476693057523819902185638935 715039586285729853278458403)
              ·
                refine ⟨1072559379428594779917687605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 715039586285729853278458403 1072559379428594779917687605)
                ·
                  refine ⟨100552441821430760617283213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1072559379428594779917687605 100552441821430760617283213)
                  ·
                    refine ⟨37707165683036535231481205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100552441821430760617283213 37707165683036535231481205)
                    ·
                      refine ⟨3535046782784675177951363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37707165683036535231481205 3535046782784675177951363)
                      ·
                        rfl

theorem cell23_6884479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_6884479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884479 prefixEnd_6884479 := by exact prefixLift 6884479
  have htrace : WordTrace (prefixWord ++ tailWord_6884479) baseStart_6884479 baseEnd_6884479 := by
    simpa [prefixWord, tailWord_6884479, baseEnd_6884479] using wordTrace_append hprefix tailTrace_6884479
  have hstable : (prefixWord ++ tailWord_6884479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884479).length < 2 ^ (prefixWord ++ tailWord_6884479).sum := by decide
  have hdescent : baseEnd_6884479 < baseStart_6884479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884499 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 9]
def baseStart_6884499 : Nat := 118140960795 + 6884499 * 2 ^ 59
def prefixEnd_6884499 : Nat := 4983230072969 + 3 ^ 40 * 6884499 * 2
def baseEnd_6884499 : Nat := 392784116933085011077919

theorem tailTrace_6884499 : CollatzResearch.WordTrace tailWord_6884499 prefixEnd_6884499 392784116933085011077919 := by
  unfold tailWord_6884499
  simp only [CollatzResearch.WordTrace]
  refine ⟨251098307085643376665776551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167398871390428917777184367 251098307085643376665776551)
  ·
    refine ⟨376647460628465064998664827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251098307085643376665776551 376647460628465064998664827)
    ·
      refine ⟨564971190942697597497997241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376647460628465064998664827 564971190942697597497997241)
      ·
        refine ⟨423728393207023198123497931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 564971190942697597497997241 423728393207023198123497931)
        ·
          refine ⟨635592589810534797185246897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423728393207023198123497931 635592589810534797185246897)
          ·
            refine ⟨476694442357901097888935173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 635592589810534797185246897 476694442357901097888935173)
            ·
              refine ⟨89380207942106455854175345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 476694442357901097888935173 89380207942106455854175345)
              ·
                refine ⟨67035155956579841890631509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89380207942106455854175345 67035155956579841890631509)
                ·
                  refine ⟨392784116933085011077919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67035155956579841890631509 392784116933085011077919)
                  ·
                    rfl

theorem cell23_6884499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 9].length) (baseStart_6884499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884499 prefixEnd_6884499 := by exact prefixLift 6884499
  have htrace : WordTrace (prefixWord ++ tailWord_6884499) baseStart_6884499 baseEnd_6884499 := by
    simpa [prefixWord, tailWord_6884499, baseEnd_6884499] using wordTrace_append hprefix tailTrace_6884499
  have hstable : (prefixWord ++ tailWord_6884499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884499).length < 2 ^ (prefixWord ++ tailWord_6884499).sum := by decide
  have hdescent : baseEnd_6884499 < baseStart_6884499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884527 : List Nat := [1, 1, 2, 1, 2, 3, 6, 1, 2, 2, 2]
def baseStart_6884527 : Nat := 118140960795 + 6884527 * 2 ^ 59
def prefixEnd_6884527 : Nat := 4983230072969 + 3 ^ 40 * 6884527 * 2
def baseEnd_6884527 : Nat := 3535071429856090990151143

theorem tailTrace_6884527 : CollatzResearch.WordTrace tailWord_6884527 prefixEnd_6884527 3535071429856090990151143 := by
  unfold tailWord_6884527
  simp only [CollatzResearch.WordTrace]
  refine ⟨251099328329541937447795835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167399552219694624965197223 251099328329541937447795835)
  ·
    refine ⟨376648992494312906171693753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251099328329541937447795835 376648992494312906171693753)
    ·
      refine ⟨282486744370734679628770315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376648992494312906171693753 282486744370734679628770315)
      ·
        refine ⟨423730116556102019443155473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282486744370734679628770315 423730116556102019443155473)
        ·
          refine ⟨317797587417076514582366605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423730116556102019443155473 317797587417076514582366605)
          ·
            refine ⟨119174095281403692968387477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317797587417076514582366605 119174095281403692968387477)
            ·
              refine ⟨5586285716315798107893163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 119174095281403692968387477 5586285716315798107893163)
              ·
                refine ⟨8379428574473697161839745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5586285716315798107893163 8379428574473697161839745)
                ·
                  refine ⟨6284571430855272871379809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8379428574473697161839745 6284571430855272871379809)
                  ·
                    refine ⟨4713428573141454653534857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6284571430855272871379809 4713428573141454653534857)
                    ·
                      refine ⟨3535071429856090990151143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4713428573141454653534857 3535071429856090990151143)
                      ·
                        rfl

theorem cell23_6884527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 2, 2, 2].length) (baseStart_6884527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884527 prefixEnd_6884527 := by exact prefixLift 6884527
  have htrace : WordTrace (prefixWord ++ tailWord_6884527) baseStart_6884527 baseEnd_6884527 := by
    simpa [prefixWord, tailWord_6884527, baseEnd_6884527] using wordTrace_append hprefix tailTrace_6884527
  have hstable : (prefixWord ++ tailWord_6884527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884527).length < 2 ^ (prefixWord ++ tailWord_6884527).sum := by decide
  have hdescent : baseEnd_6884527 < baseStart_6884527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884670 : List Nat := [4, 2, 1, 2, 1, 1, 1, 5, 1, 5]
def baseStart_6884670 : Nat := 118140960795 + 6884670 * 2 ^ 59
def prefixEnd_6884670 : Nat := 4983230072969 + 3 ^ 40 * 6884670 * 2
def baseEnd_6884670 : Nat := 1178381619196561310220995

theorem tailTrace_6884670 : CollatzResearch.WordTrace tailWord_6884670 prefixEnd_6884670 1178381619196561310220995 := by
  unfold tailWord_6884670
  simp only [CollatzResearch.WordTrace]
  refine ⟨31388067996002984108781433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167403029312015915246834309 31388067996002984108781433)
  ·
    refine ⟨23541050997002238081586075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31388067996002984108781433 23541050997002238081586075)
    ·
      refine ⟨35311576495503357122379113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23541050997002238081586075 35311576495503357122379113)
      ·
        refine ⟨26483682371627517841784335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35311576495503357122379113 26483682371627517841784335)
        ·
          refine ⟨39725523557441276762676503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26483682371627517841784335 39725523557441276762676503)
          ·
            refine ⟨59588285336161915144014755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39725523557441276762676503 59588285336161915144014755)
            ·
              refine ⟨89382428004242872716022133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59588285336161915144014755 89382428004242872716022133)
              ·
                refine ⟨8379602625397769317127075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89382428004242872716022133 8379602625397769317127075)
                ·
                  refine ⟨12569403938096653975690613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8379602625397769317127075 12569403938096653975690613)
                  ·
                    refine ⟨1178381619196561310220995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12569403938096653975690613 1178381619196561310220995)
                    ·
                      rfl

theorem cell23_6884670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_6884670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884670 prefixEnd_6884670 := by exact prefixLift 6884670
  have htrace : WordTrace (prefixWord ++ tailWord_6884670) baseStart_6884670 baseEnd_6884670 := by
    simpa [prefixWord, tailWord_6884670, baseEnd_6884670] using wordTrace_append hprefix tailTrace_6884670
  have hstable : (prefixWord ++ tailWord_6884670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884670).length < 2 ^ (prefixWord ++ tailWord_6884670).sum := by decide
  have hdescent : baseEnd_6884670 < baseStart_6884670 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884678 : List Nat := [6, 1, 1, 3, 2, 1, 1, 1, 3, 4]
def baseStart_6884678 : Nat := 118140960795 + 6884678 * 2 ^ 59
def prefixEnd_6884678 : Nat := 4983230072969 + 3 ^ 40 * 6884678 * 2
def baseEnd_6884678 : Nat := 1178382988478306633120983

theorem tailTrace_6884678 : CollatzResearch.WordTrace tailWord_6884678 prefixEnd_6884678 1178382988478306633120983 := by
  unfold tailWord_6884678
  simp only [CollatzResearch.WordTrace]
  refine ⟨7847026117249840319891959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 167403223834663260157695125 7847026117249840319891959)
  ·
    refine ⟨11770539175874760479837939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7847026117249840319891959 11770539175874760479837939)
    ·
      refine ⟨17655808763812140719756909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11770539175874760479837939 17655808763812140719756909)
      ·
        refine ⟨6620928286429552769908841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17655808763812140719756909 6620928286429552769908841)
        ·
          refine ⟨4965696214822164577431631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6620928286429552769908841 4965696214822164577431631)
          ·
            refine ⟨7448544322233246866147447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4965696214822164577431631 7448544322233246866147447)
            ·
              refine ⟨11172816483349870299221171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7448544322233246866147447 11172816483349870299221171)
              ·
                refine ⟨16759224725024805448831757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11172816483349870299221171 16759224725024805448831757)
                ·
                  refine ⟨6284709271884302043311909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16759224725024805448831757 6284709271884302043311909)
                  ·
                    refine ⟨1178382988478306633120983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6284709271884302043311909 1178382988478306633120983)
                    ·
                      rfl

theorem cell23_6884678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_6884678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884678 prefixEnd_6884678 := by exact prefixLift 6884678
  have htrace : WordTrace (prefixWord ++ tailWord_6884678) baseStart_6884678 baseEnd_6884678 := by
    simpa [prefixWord, tailWord_6884678, baseEnd_6884678] using wordTrace_append hprefix tailTrace_6884678
  have hstable : (prefixWord ++ tailWord_6884678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884678).length < 2 ^ (prefixWord ++ tailWord_6884678).sum := by decide
  have hdescent : baseEnd_6884678 < baseStart_6884678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884703 : List Nat := [1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 4]
def baseStart_6884703 : Nat := 118140960795 + 6884703 * 2 ^ 59
def prefixEnd_6884703 : Nat := 4983230072969 + 3 ^ 40 * 6884703 * 2
def baseEnd_6884703 : Nat := 3535161802451282301550333

theorem tailTrace_6884703 : CollatzResearch.WordTrace tailWord_6884703 prefixEnd_6884703 3535161802451282301550333 := by
  unfold tailWord_6884703
  simp only [CollatzResearch.WordTrace]
  refine ⟨251105747576904319506202763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167403831717936213004135175 251105747576904319506202763)
  ·
    refine ⟨376658621365356479259304145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251105747576904319506202763 376658621365356479259304145)
    ·
      refine ⟨282493966024017359444478109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376658621365356479259304145 282493966024017359444478109)
      ·
        refine ⟨105935237259006509791679291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282493966024017359444478109 105935237259006509791679291)
        ·
          refine ⟨158902855888509764687518937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105935237259006509791679291 158902855888509764687518937)
          ·
            refine ⟨119177141916382323515639203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158902855888509764687518937 119177141916382323515639203)
            ·
              refine ⟨178765712874573485273458805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119177141916382323515639203 178765712874573485273458805)
              ·
                refine ⟨16759285581991264244386763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 178765712874573485273458805 16759285581991264244386763)
                ·
                  refine ⟨25138928372986896366580145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16759285581991264244386763 25138928372986896366580145)
                  ·
                    refine ⟨18854196279740172274935109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25138928372986896366580145 18854196279740172274935109)
                    ·
                      refine ⟨3535161802451282301550333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18854196279740172274935109 3535161802451282301550333)
                      ·
                        rfl

theorem cell23_6884703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_6884703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884703 prefixEnd_6884703 := by exact prefixLift 6884703
  have htrace : WordTrace (prefixWord ++ tailWord_6884703) baseStart_6884703 baseEnd_6884703 := by
    simpa [prefixWord, tailWord_6884703, baseEnd_6884703] using wordTrace_append hprefix tailTrace_6884703
  have hstable : (prefixWord ++ tailWord_6884703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884703).length < 2 ^ (prefixWord ++ tailWord_6884703).sum := by decide
  have hdescent : baseEnd_6884703 < baseStart_6884703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884707 : List Nat := [1, 1, 1, 5, 2, 4, 1, 2, 1, 1, 4]
def baseStart_6884707 : Nat := 118140960795 + 6884707 * 2 ^ 59
def prefixEnd_6884707 : Nat := 4983230072969 + 3 ^ 40 * 6884707 * 2
def baseEnd_6884707 : Nat := 3535163856373900285900315

theorem tailTrace_6884707 : CollatzResearch.WordTrace tailWord_6884707 prefixEnd_6884707 3535163856373900285900315 := by
  unfold tailWord_6884707
  simp only [CollatzResearch.WordTrace]
  refine ⟨251105893468889828189348375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167403928979259885459565583 251105893468889828189348375)
  ·
    refine ⟨376658840203334742284022563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251105893468889828189348375 376658840203334742284022563)
    ·
      refine ⟨564988260305002113426033845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376658840203334742284022563 564988260305002113426033845)
      ·
        refine ⟨52967649403593948133690673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 564988260305002113426033845 52967649403593948133690673)
        ·
          refine ⟨39725737052695461100268005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52967649403593948133690673 39725737052695461100268005)
          ·
            refine ⟨7448575697380398956300251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39725737052695461100268005 7448575697380398956300251)
            ·
              refine ⟨11172863546070598434450377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7448575697380398956300251 11172863546070598434450377)
              ·
                refine ⟨8379647659552948825837783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11172863546070598434450377 8379647659552948825837783)
                ·
                  refine ⟨12569471489329423238756675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8379647659552948825837783 12569471489329423238756675)
                  ·
                    refine ⟨18854207233994134858135013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12569471489329423238756675 18854207233994134858135013)
                    ·
                      refine ⟨3535163856373900285900315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18854207233994134858135013 3535163856373900285900315)
                      ·
                        rfl

theorem cell23_6884707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_6884707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884707 prefixEnd_6884707 := by exact prefixLift 6884707
  have htrace : WordTrace (prefixWord ++ tailWord_6884707) baseStart_6884707 baseEnd_6884707 := by
    simpa [prefixWord, tailWord_6884707, baseEnd_6884707] using wordTrace_append hprefix tailTrace_6884707
  have hstable : (prefixWord ++ tailWord_6884707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884707).length < 2 ^ (prefixWord ++ tailWord_6884707).sum := by decide
  have hdescent : baseEnd_6884707 < baseStart_6884707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884727 : List Nat := [1, 1, 3, 1, 1, 2, 7, 1, 1, 2, 3]
def baseStart_6884727 : Nat := 118140960795 + 6884727 * 2 ^ 59
def prefixEnd_6884727 : Nat := 4983230072969 + 3 ^ 40 * 6884727 * 2
def baseEnd_6884727 : Nat := 3535174125986990207650223

theorem tailTrace_6884727 : CollatzResearch.WordTrace tailWord_6884727 prefixEnd_6884727 3535174125986990207650223 := by
  unfold tailWord_6884727
  simp only [CollatzResearch.WordTrace]
  refine ⟨251106622928817371605076435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167404415285878247736717623 251106622928817371605076435)
  ·
    refine ⟨376659934393226057407614653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251106622928817371605076435 376659934393226057407614653)
    ·
      refine ⟨141247475397459771527855495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 376659934393226057407614653 141247475397459771527855495)
      ·
        refine ⟨211871213096189657291783243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141247475397459771527855495 211871213096189657291783243)
        ·
          refine ⟨317806819644284485937674865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211871213096189657291783243 317806819644284485937674865)
          ·
            refine ⟨238355114733213364453256149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317806819644284485937674865 238355114733213364453256149)
            ·
              refine ⟨5586448001559688229373191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 238355114733213364453256149 5586448001559688229373191)
              ·
                refine ⟨8379672002339532344059787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5586448001559688229373191 8379672002339532344059787)
                ·
                  refine ⟨12569508003509298516089681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8379672002339532344059787 12569508003509298516089681)
                  ·
                    refine ⟨9427131002631973887067261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12569508003509298516089681 9427131002631973887067261)
                    ·
                      refine ⟨3535174125986990207650223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9427131002631973887067261 3535174125986990207650223)
                      ·
                        rfl

theorem cell23_6884727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 1, 2, 3].length) (baseStart_6884727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884727 prefixEnd_6884727 := by exact prefixLift 6884727
  have htrace : WordTrace (prefixWord ++ tailWord_6884727) baseStart_6884727 baseEnd_6884727 := by
    simpa [prefixWord, tailWord_6884727, baseEnd_6884727] using wordTrace_append hprefix tailTrace_6884727
  have hstable : (prefixWord ++ tailWord_6884727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884727).length < 2 ^ (prefixWord ++ tailWord_6884727).sum := by decide
  have hdescent : baseEnd_6884727 < baseStart_6884727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884741 : List Nat := [1, 3, 1, 1, 3, 1, 6, 2, 1, 2, 2]
def baseStart_6884741 : Nat := 118140960795 + 6884741 * 2 ^ 59
def prefixEnd_6884741 : Nat := 4983230072969 + 3 ^ 40 * 6884741 * 2
def baseEnd_6884741 : Nat := 3535181314716153152875159

theorem tailTrace_6884741 : CollatzResearch.WordTrace tailWord_6884741 prefixEnd_6884741 3535181314716153152875159 := by
  unfold tailWord_6884741
  simp only [CollatzResearch.WordTrace]
  refine ⟨251107133550766651996086077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167404755700511101330724051 251107133550766651996086077)
  ·
    refine ⟨94165175081537494498532279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251107133550766651996086077 94165175081537494498532279)
    ·
      refine ⟨141247762622306241747798419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94165175081537494498532279 141247762622306241747798419)
      ·
        refine ⟨211871643933459362621697629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141247762622306241747798419 211871643933459362621697629)
        ·
          refine ⟨79451866475047260983136611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211871643933459362621697629 79451866475047260983136611)
          ·
            refine ⟨119177799712570891474704917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79451866475047260983136611 119177799712570891474704917)
            ·
              refine ⟨5586459361526760537876793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 119177799712570891474704917 5586459361526760537876793)
              ·
                refine ⟨4189844521145070403407595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5586459361526760537876793 4189844521145070403407595)
                ·
                  refine ⟨6284766781717605605111393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4189844521145070403407595 6284766781717605605111393)
                  ·
                    refine ⟨4713575086288204203833545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6284766781717605605111393 4713575086288204203833545)
                    ·
                      refine ⟨3535181314716153152875159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4713575086288204203833545 3535181314716153152875159)
                      ·
                        rfl

theorem cell23_6884741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 2, 1, 2, 2].length) (baseStart_6884741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884741 prefixEnd_6884741 := by exact prefixLift 6884741
  have htrace : WordTrace (prefixWord ++ tailWord_6884741) baseStart_6884741 baseEnd_6884741 := by
    simpa [prefixWord, tailWord_6884741, baseEnd_6884741] using wordTrace_append hprefix tailTrace_6884741
  have hstable : (prefixWord ++ tailWord_6884741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884741).length < 2 ^ (prefixWord ++ tailWord_6884741).sum := by decide
  have hdescent : baseEnd_6884741 < baseStart_6884741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884743 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 2, 7]
def baseStart_6884743 : Nat := 118140960795 + 6884743 * 2 ^ 59
def prefixEnd_6884743 : Nat := 4983230072969 + 3 ^ 40 * 6884743 * 2
def baseEnd_6884743 : Nat := 1178394113892487381683383

theorem tailTrace_6884743 : CollatzResearch.WordTrace tailWord_6884743 prefixEnd_6884743 1178394113892487381683383 := by
  unfold tailWord_6884743
  simp only [CollatzResearch.WordTrace]
  refine ⟨251107206496759406337658883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167404804331172937558439255 251107206496759406337658883)
  ·
    refine ⟨376660809745139109506488325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251107206496759406337658883 376660809745139109506488325)
    ·
      refine ⟨70623901827213583032466561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 376660809745139109506488325 70623901827213583032466561)
      ·
        refine ⟨52967926370410187274349921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70623901827213583032466561 52967926370410187274349921)
        ·
          refine ⟨39725944777807640455762441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52967926370410187274349921 39725944777807640455762441)
          ·
            refine ⟨29794458583355730341821831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39725944777807640455762441 29794458583355730341821831)
            ·
              refine ⟨44691687875033595512732747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29794458583355730341821831 44691687875033595512732747)
              ·
                refine ⟨67037531812550393269099121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44691687875033595512732747 67037531812550393269099121)
                ·
                  refine ⟨50278148859412794951824341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67037531812550393269099121 50278148859412794951824341)
                  ·
                    refine ⟨1178394113892487381683383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50278148859412794951824341 1178394113892487381683383)
                    ·
                      rfl

theorem cell23_6884743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_6884743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884743 prefixEnd_6884743 := by exact prefixLift 6884743
  have htrace : WordTrace (prefixWord ++ tailWord_6884743) baseStart_6884743 baseEnd_6884743 := by
    simpa [prefixWord, tailWord_6884743, baseEnd_6884743] using wordTrace_append hprefix tailTrace_6884743
  have hstable : (prefixWord ++ tailWord_6884743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884743).length < 2 ^ (prefixWord ++ tailWord_6884743).sum := by decide
  have hdescent : baseEnd_6884743 < baseStart_6884743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884754 : List Nat := [3, 2, 3, 3, 1, 1, 2, 1, 1, 2, 4]
def baseStart_6884754 : Nat := 118140960795 + 6884754 * 2 ^ 59
def prefixEnd_6884754 : Nat := 4983230072969 + 3 ^ 40 * 6884754 * 2
def baseEnd_6884754 : Nat := 3535187989964661602012599

theorem tailTrace_6884754 : CollatzResearch.WordTrace tailWord_6884754 prefixEnd_6884754 3535187989964661602012599 := by
  unfold tailWord_6884754
  simp only [CollatzResearch.WordTrace]
  refine ⟨62776901924929888804077329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167405071799813036810872877 62776901924929888804077329)
  ·
    refine ⟨47082676443697416603057997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62776901924929888804077329 47082676443697416603057997)
    ·
      refine ⟨17656003666386531226146749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47082676443697416603057997 17656003666386531226146749)
      ·
        refine ⟨6621001374894949209805031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17656003666386531226146749 6621001374894949209805031)
        ·
          refine ⟨9931502062342423814707547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6621001374894949209805031 9931502062342423814707547)
          ·
            refine ⟨14897253093513635722061321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9931502062342423814707547 14897253093513635722061321)
            ·
              refine ⟨11172939820135226791545991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14897253093513635722061321 11172939820135226791545991)
              ·
                refine ⟨16759409730202840187318987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11172939820135226791545991 16759409730202840187318987)
                ·
                  refine ⟨25139114595304260280978481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16759409730202840187318987 25139114595304260280978481)
                  ·
                    refine ⟨18854335946478195210733861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25139114595304260280978481 18854335946478195210733861)
                    ·
                      refine ⟨3535187989964661602012599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18854335946478195210733861 3535187989964661602012599)
                      ·
                        rfl

theorem cell23_6884754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_6884754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884754 prefixEnd_6884754 := by exact prefixLift 6884754
  have htrace : WordTrace (prefixWord ++ tailWord_6884754) baseStart_6884754 baseEnd_6884754 := by
    simpa [prefixWord, tailWord_6884754, baseEnd_6884754] using wordTrace_append hprefix tailTrace_6884754
  have hstable : (prefixWord ++ tailWord_6884754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884754).length < 2 ^ (prefixWord ++ tailWord_6884754).sum := by decide
  have hdescent : baseEnd_6884754 < baseStart_6884754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884757 : List Nat := [1, 3, 2, 1, 1, 2, 4, 3, 2, 1, 3]
def baseStart_6884757 : Nat := 118140960795 + 6884757 * 2 ^ 59
def prefixEnd_6884757 : Nat := 4983230072969 + 3 ^ 40 * 6884757 * 2
def baseEnd_6884757 : Nat := 3535189530406625090275085

theorem tailTrace_6884757 : CollatzResearch.WordTrace tailWord_6884757 prefixEnd_6884757 3535189530406625090275085 := by
  unfold tailWord_6884757
  simp only [CollatzResearch.WordTrace]
  refine ⟨251107717118708686728668525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167405144745805791152445683 251107717118708686728668525)
  ·
    refine ⟨94165393919515757523250697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251107717118708686728668525 94165393919515757523250697)
    ·
      refine ⟨70624045439636818142438023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94165393919515757523250697 70624045439636818142438023)
      ·
        refine ⟨105936068159455227213657035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70624045439636818142438023 105936068159455227213657035)
        ·
          refine ⟨158904102239182840820485553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105936068159455227213657035 158904102239182840820485553)
          ·
            refine ⟨119178076679387130615364165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158904102239182840820485553 119178076679387130615364165)
            ·
              refine ⟨22345889377385086990380781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119178076679387130615364165 22345889377385086990380781)
              ·
                refine ⟨8379708516519407621392793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22345889377385086990380781 8379708516519407621392793)
                ·
                  refine ⟨6284781387389555716044595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8379708516519407621392793 6284781387389555716044595)
                  ·
                    refine ⟨9427172081084333574066893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6284781387389555716044595 9427172081084333574066893)
                    ·
                      refine ⟨3535189530406625090275085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9427172081084333574066893 3535189530406625090275085)
                      ·
                        rfl

theorem cell23_6884757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_6884757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884757 prefixEnd_6884757 := by exact prefixLift 6884757
  have htrace : WordTrace (prefixWord ++ tailWord_6884757) baseStart_6884757 baseEnd_6884757 := by
    simpa [prefixWord, tailWord_6884757, baseEnd_6884757] using wordTrace_append hprefix tailTrace_6884757
  have hstable : (prefixWord ++ tailWord_6884757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884757).length < 2 ^ (prefixWord ++ tailWord_6884757).sum := by decide
  have hdescent : baseEnd_6884757 < baseStart_6884757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884767 : List Nat := [1, 1, 2, 5, 1, 2, 2, 1, 3, 3, 2]
def baseStart_6884767 : Nat := 118140960795 + 6884767 * 2 ^ 59
def prefixEnd_6884767 : Nat := 4983230072969 + 3 ^ 40 * 6884767 * 2
def baseEnd_6884767 : Nat := 3535194665213170051150039

theorem tailTrace_6884767 : CollatzResearch.WordTrace tailWord_6884767 prefixEnd_6884767 3535194665213170051150039 := by
  unfold tailWord_6884767
  simp only [CollatzResearch.WordTrace]
  refine ⟨251108081848672458436532555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167405387899114972291021703 251108081848672458436532555)
  ·
    refine ⟨376662122773008687654798833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251108081848672458436532555 376662122773008687654798833)
    ·
      refine ⟨282496592079756515741099125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376662122773008687654798833 282496592079756515741099125)
      ·
        refine ⟨26484055507477173350728043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 282496592079756515741099125 26484055507477173350728043)
        ·
          refine ⟨39726083261215760026092065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26484055507477173350728043 39726083261215760026092065)
          ·
            refine ⟨29794562445911820019569049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39726083261215760026092065 29794562445911820019569049)
            ·
              refine ⟨22345921834433865014676787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29794562445911820019569049 22345921834433865014676787)
              ·
                refine ⟨33518882751650797522015181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22345921834433865014676787 33518882751650797522015181)
                ·
                  refine ⟨12569581031869049070755693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33518882751650797522015181 12569581031869049070755693)
                  ·
                    refine ⟨4713592886950893401533385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12569581031869049070755693 4713592886950893401533385)
                    ·
                      refine ⟨3535194665213170051150039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4713592886950893401533385 3535194665213170051150039)
                      ·
                        rfl

theorem cell23_6884767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_6884767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884767 prefixEnd_6884767 := by exact prefixLift 6884767
  have htrace : WordTrace (prefixWord ++ tailWord_6884767) baseStart_6884767 baseEnd_6884767 := by
    simpa [prefixWord, tailWord_6884767, baseEnd_6884767] using wordTrace_append hprefix tailTrace_6884767
  have hstable : (prefixWord ++ tailWord_6884767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884767).length < 2 ^ (prefixWord ++ tailWord_6884767).sum := by decide
  have hdescent : baseEnd_6884767 < baseStart_6884767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884783 : List Nat := [1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 5]
def baseStart_6884783 : Nat := 118140960795 + 6884783 * 2 ^ 59
def prefixEnd_6884783 : Nat := 4983230072969 + 3 ^ 40 * 6884783 * 2
def baseEnd_6884783 : Nat := 3535202880903641988549965

theorem tailTrace_6884783 : CollatzResearch.WordTrace tailWord_6884783 prefixEnd_6884783 3535202880903641988549965 := by
  unfold tailWord_6884783
  simp only [CollatzResearch.WordTrace]
  refine ⟨251108665416614493169115003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167405776944409662112743335 251108665416614493169115003)
  ·
    refine ⟨376662998124921739753672505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251108665416614493169115003 376662998124921739753672505)
    ·
      refine ⟨282497248593691304815254379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376662998124921739753672505 282497248593691304815254379)
      ·
        refine ⟨423745872890536957222881569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282497248593691304815254379 423745872890536957222881569)
        ·
          refine ⟨317809404667902717917161177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423745872890536957222881569 317809404667902717917161177)
          ·
            refine ⟨238357053500927038437870883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317809404667902717917161177 238357053500927038437870883)
            ·
              refine ⟨357535580251390557656806325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238357053500927038437870883 357535580251390557656806325)
              ·
                refine ⟨33518960648567864780325593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 357535580251390557656806325 33518960648567864780325593)
                ·
                  refine ⟨25139220486425898585244195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33518960648567864780325593 25139220486425898585244195)
                  ·
                    refine ⟨37708830729638847877866293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25139220486425898585244195 37708830729638847877866293)
                    ·
                      refine ⟨3535202880903641988549965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37708830729638847877866293 3535202880903641988549965)
                      ·
                        rfl

theorem cell23_6884783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 5].length) (baseStart_6884783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884783 prefixEnd_6884783 := by exact prefixLift 6884783
  have htrace : WordTrace (prefixWord ++ tailWord_6884783) baseStart_6884783 baseEnd_6884783 := by
    simpa [prefixWord, tailWord_6884783, baseEnd_6884783] using wordTrace_append hprefix tailTrace_6884783
  have hstable : (prefixWord ++ tailWord_6884783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884783).length < 2 ^ (prefixWord ++ tailWord_6884783).sum := by decide
  have hdescent : baseEnd_6884783 < baseStart_6884783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884803 : List Nat := [1, 1, 1, 3, 1, 1, 5, 3, 7]
def baseStart_6884803 : Nat := 118140960795 + 6884803 * 2 ^ 59
def prefixEnd_6884803 : Nat := 4983230072969 + 3 ^ 40 * 6884803 * 2
def baseEnd_6884803 : Nat := 392801461168525767811097

theorem tailTrace_6884803 : CollatzResearch.WordTrace tailWord_6884803 prefixEnd_6884803 392801461168525767811097 := by
  unfold tailWord_6884803
  simp only [CollatzResearch.WordTrace]
  refine ⟨251109394876542036584843063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167406263251028024389895375 251109394876542036584843063)
  ·
    refine ⟨376664092314813054877264595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251109394876542036584843063 376664092314813054877264595)
    ·
      refine ⟨564996138472219582315896893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376664092314813054877264595 564996138472219582315896893)
      ·
        refine ⟨211873551927082343368461335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 564996138472219582315896893 211873551927082343368461335)
        ·
          refine ⟨317810327890623515052692003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211873551927082343368461335 317810327890623515052692003)
          ·
            refine ⟨476715491835935272579038005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317810327890623515052692003 476715491835935272579038005)
            ·
              refine ⟨44692077359618931804284813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 476715491835935272579038005 44692077359618931804284813)
              ·
                refine ⟨16759529009857099426606805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44692077359618931804284813 16759529009857099426606805)
                ·
                  refine ⟨392801461168525767811097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16759529009857099426606805 392801461168525767811097)
                  ·
                    rfl

theorem cell23_6884803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 7].length) (baseStart_6884803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884803 prefixEnd_6884803 := by exact prefixLift 6884803
  have htrace : WordTrace (prefixWord ++ tailWord_6884803) baseStart_6884803 baseEnd_6884803 := by
    simpa [prefixWord, tailWord_6884803, baseEnd_6884803] using wordTrace_append hprefix tailTrace_6884803
  have hstable : (prefixWord ++ tailWord_6884803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884803).length < 2 ^ (prefixWord ++ tailWord_6884803).sum := by decide
  have hdescent : baseEnd_6884803 < baseStart_6884803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884810 : List Nat := [3, 1, 2, 1, 2, 3, 2, 1, 2, 2, 4]
def baseStart_6884810 : Nat := 118140960795 + 6884810 * 2 ^ 59
def prefixEnd_6884810 : Nat := 4983230072969 + 3 ^ 40 * 6884810 * 2
def baseEnd_6884810 : Nat := 3535216744881313382912341

theorem tailTrace_6884810 : CollatzResearch.WordTrace tailWord_6884810 prefixEnd_6884810 3535216744881313382912341 := by
  unfold tailWord_6884810
  simp only [CollatzResearch.WordTrace]
  refine ⟨62777412546879169195086971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167406433458344451186898589 62777412546879169195086971)
  ·
    refine ⟨94166118820318753792630457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62777412546879169195086971 94166118820318753792630457)
    ·
      refine ⟨70624589115239065344472843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94166118820318753792630457 70624589115239065344472843)
      ·
        refine ⟨105936883672858598016709265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70624589115239065344472843 105936883672858598016709265)
        ·
          refine ⟨79452662754643948512531949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105936883672858598016709265 79452662754643948512531949)
          ·
            refine ⟨29794748532991480692199481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79452662754643948512531949 29794748532991480692199481)
            ·
              refine ⟨22346061399743610519149611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29794748532991480692199481 22346061399743610519149611)
              ·
                refine ⟨33519092099615415778724417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22346061399743610519149611 33519092099615415778724417)
                ·
                  refine ⟨25139319074711561834043313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33519092099615415778724417 25139319074711561834043313)
                  ·
                    refine ⟨18854489306033671375532485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25139319074711561834043313 18854489306033671375532485)
                    ·
                      refine ⟨3535216744881313382912341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18854489306033671375532485 3535216744881313382912341)
                      ·
                        rfl

theorem cell23_6884810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_6884810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884810 prefixEnd_6884810 := by exact prefixLift 6884810
  have htrace : WordTrace (prefixWord ++ tailWord_6884810) baseStart_6884810 baseEnd_6884810 := by
    simpa [prefixWord, tailWord_6884810, baseEnd_6884810] using wordTrace_append hprefix tailTrace_6884810
  have hstable : (prefixWord ++ tailWord_6884810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884810).length < 2 ^ (prefixWord ++ tailWord_6884810).sum := by decide
  have hdescent : baseEnd_6884810 < baseStart_6884810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884814 : List Nat := [4, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2]
def baseStart_6884814 : Nat := 118140960795 + 6884814 * 2 ^ 59
def prefixEnd_6884814 : Nat := 4983230072969 + 3 ^ 40 * 6884814 * 2
def baseEnd_6884814 : Nat := 3535218798803931367262323

theorem tailTrace_6884814 : CollatzResearch.WordTrace tailWord_6884814 prefixEnd_6884814 3535218798803931367262323 := by
  unfold tailWord_6884814
  simp only [CollatzResearch.WordTrace]
  refine ⟨31388724509937773182936687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167406530719668123642328997 31388724509937773182936687)
  ·
    refine ⟨47083086764906659774405031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31388724509937773182936687 47083086764906659774405031)
    ·
      refine ⟨70624630147359989661607547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47083086764906659774405031 70624630147359989661607547)
      ·
        refine ⟨105936945221039984492411321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70624630147359989661607547 105936945221039984492411321)
        ·
          refine ⟨79452708915779988369308491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105936945221039984492411321 79452708915779988369308491)
          ·
            refine ⟨119179063373669982553962737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79452708915779988369308491 119179063373669982553962737)
            ·
              refine ⟨89384297530252486915472053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119179063373669982553962737 89384297530252486915472053)
              ·
                refine ⟨8379777893461170648325505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89384297530252486915472053 8379777893461170648325505)
                ·
                  refine ⟨6284833420095877986244129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8379777893461170648325505 6284833420095877986244129)
                  ·
                    refine ⟨4713625065071908489683097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6284833420095877986244129 4713625065071908489683097)
                    ·
                      refine ⟨3535218798803931367262323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4713625065071908489683097 3535218798803931367262323)
                      ·
                        rfl

theorem cell23_6884814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2].length) (baseStart_6884814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884814 prefixEnd_6884814 := by exact prefixLift 6884814
  have htrace : WordTrace (prefixWord ++ tailWord_6884814) baseStart_6884814 baseEnd_6884814 := by
    simpa [prefixWord, tailWord_6884814, baseEnd_6884814] using wordTrace_append hprefix tailTrace_6884814
  have hstable : (prefixWord ++ tailWord_6884814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884814).length < 2 ^ (prefixWord ++ tailWord_6884814).sum := by decide
  have hdescent : baseEnd_6884814 < baseStart_6884814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884863 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 2, 8]
def baseStart_6884863 : Nat := 118140960795 + 6884863 * 2 ^ 59
def prefixEnd_6884863 : Nat := 4983230072969 + 3 ^ 40 * 6884863 * 2
def baseEnd_6884863 : Nat := 1178414653118667225183199

theorem tailTrace_6884863 : CollatzResearch.WordTrace tailWord_6884863 prefixEnd_6884863 1178414653118667225183199 := by
  unfold tailWord_6884863
  simp only [CollatzResearch.WordTrace]
  refine ⟨251111583256324666832027243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167407722170883111221351495 251111583256324666832027243)
  ·
    refine ⟨376667374884487000248040865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251111583256324666832027243 376667374884487000248040865)
    ·
      refine ⟨282500531163365250186030649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376667374884487000248040865 282500531163365250186030649)
      ·
        refine ⟨211875398372523937639522987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282500531163365250186030649 211875398372523937639522987)
        ·
          refine ⟨317813097558785906459284481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211875398372523937639522987 317813097558785906459284481)
          ·
            refine ⟨238359823169089429844463361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317813097558785906459284481 238359823169089429844463361)
            ·
              refine ⟨178769867376817072383347521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238359823169089429844463361 178769867376817072383347521)
              ·
                refine ⟨134077400532612804287510641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178769867376817072383347521 134077400532612804287510641)
                ·
                  refine ⟨100558050399459603215632981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134077400532612804287510641 100558050399459603215632981)
                  ·
                    refine ⟨1178414653118667225183199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100558050399459603215632981 1178414653118667225183199)
                    ·
                      rfl

theorem cell23_6884863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 8].length) (baseStart_6884863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884863 prefixEnd_6884863 := by exact prefixLift 6884863
  have htrace : WordTrace (prefixWord ++ tailWord_6884863) baseStart_6884863 baseEnd_6884863 := by
    simpa [prefixWord, tailWord_6884863, baseEnd_6884863] using wordTrace_append hprefix tailTrace_6884863
  have hstable : (prefixWord ++ tailWord_6884863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884863).length < 2 ^ (prefixWord ++ tailWord_6884863).sum := by decide
  have hdescent : baseEnd_6884863 < baseStart_6884863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884865 : List Nat := [1, 2, 4, 1, 5, 1, 2, 1, 2, 2, 2]
def baseStart_6884865 : Nat := 118140960795 + 6884865 * 2 ^ 59
def prefixEnd_6884865 : Nat := 4983230072969 + 3 ^ 40 * 6884865 * 2
def baseEnd_6884865 : Nat := 3535244986317310667724589

theorem tailTrace_6884865 : CollatzResearch.WordTrace tailWord_6884865 prefixEnd_6884865 3535244986317310667724589 := by
  unfold tailWord_6884865
  simp only [CollatzResearch.WordTrace]
  refine ⟨251111656202317421173600049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167407770801544947449066699 251111656202317421173600049)
  ·
    refine ⟨188333742151738065880200037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251111656202317421173600049 188333742151738065880200037)
    ·
      refine ⟨35312576653450887352537507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188333742151738065880200037 35312576653450887352537507)
      ·
        refine ⟨52968864980176331028806261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35312576653450887352537507 52968864980176331028806261)
        ·
          refine ⟨4965831091891531033950587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52968864980176331028806261 4965831091891531033950587)
          ·
            refine ⟨7448746637837296550925881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4965831091891531033950587 7448746637837296550925881)
            ·
              refine ⟨5586559978377972413194411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7448746637837296550925881 5586559978377972413194411)
              ·
                refine ⟨8379839967566958619791617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5586559978377972413194411 8379839967566958619791617)
                ·
                  refine ⟨6284879975675218964843713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8379839967566958619791617 6284879975675218964843713)
                  ·
                    refine ⟨4713659981756414223632785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6284879975675218964843713 4713659981756414223632785)
                    ·
                      refine ⟨3535244986317310667724589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4713659981756414223632785 3535244986317310667724589)
                      ·
                        rfl

theorem cell23_6884865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_6884865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884865 prefixEnd_6884865 := by exact prefixLift 6884865
  have htrace : WordTrace (prefixWord ++ tailWord_6884865) baseStart_6884865 baseEnd_6884865 := by
    simpa [prefixWord, tailWord_6884865, baseEnd_6884865] using wordTrace_append hprefix tailTrace_6884865
  have hstable : (prefixWord ++ tailWord_6884865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884865).length < 2 ^ (prefixWord ++ tailWord_6884865).sum := by decide
  have hdescent : baseEnd_6884865 < baseStart_6884865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6884947 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 8, 3, 2]
def baseStart_6884947 : Nat := 118140960795 + 6884947 * 2 ^ 59
def prefixEnd_6884947 : Nat := 4983230072969 + 3 ^ 40 * 6884947 * 2
def baseEnd_6884947 : Nat := 3535287091730979346899211

theorem tailTrace_6884947 : CollatzResearch.WordTrace tailWord_6884947 prefixEnd_6884947 3535287091730979346899211 := by
  unfold tailWord_6884947
  simp only [CollatzResearch.WordTrace]
  refine ⟨251114646988020349178085095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167409764658680232785390063 251114646988020349178085095)
  ·
    refine ⟨376671970482030523767127643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251114646988020349178085095 376671970482030523767127643)
    ·
      refine ⟨565007955723045785650691465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376671970482030523767127643 565007955723045785650691465)
      ·
        refine ⟨423755966792284339238018599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 565007955723045785650691465 423755966792284339238018599)
        ·
          refine ⟨635633950188426508857027899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423755966792284339238018599 635633950188426508857027899)
          ·
            refine ⟨953450925282639763285541849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635633950188426508857027899 953450925282639763285541849)
            ·
              refine ⟨715088193961979822464156387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 953450925282639763285541849 715088193961979822464156387)
              ·
                refine ⟨1072632290942969733696234581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 715088193961979822464156387 1072632290942969733696234581)
                ·
                  refine ⟨12569909659487926566752749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1072632290942969733696234581 12569909659487926566752749)
                  ·
                    refine ⟨4713716122307972462532281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12569909659487926566752749 4713716122307972462532281)
                    ·
                      refine ⟨3535287091730979346899211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4713716122307972462532281 3535287091730979346899211)
                      ·
                        rfl

theorem cell23_6884947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 3, 2].length) (baseStart_6884947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6884947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6884947 prefixEnd_6884947 := by exact prefixLift 6884947
  have htrace : WordTrace (prefixWord ++ tailWord_6884947) baseStart_6884947 baseEnd_6884947 := by
    simpa [prefixWord, tailWord_6884947, baseEnd_6884947] using wordTrace_append hprefix tailTrace_6884947
  have hstable : (prefixWord ++ tailWord_6884947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6884947).length < 2 ^ (prefixWord ++ tailWord_6884947).sum := by decide
  have hdescent : baseEnd_6884947 < baseStart_6884947 := by decide
  rcases family_descends (prefixWord ++ tailWord_6884947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885028 : List Nat := [2, 3, 1, 2, 2, 4, 1, 1, 3, 2, 2]
def baseStart_6885028 : Nat := 118140960795 + 6885028 * 2 ^ 59
def prefixEnd_6885028 : Nat := 4983230072969 + 3 ^ 40 * 6885028 * 2
def baseEnd_6885028 : Nat := 3535328683663993529986339

theorem tailTrace_6885028 : CollatzResearch.WordTrace tailWord_6885028 prefixEnd_6885028 3535328683663993529986339 := by
  unfold tailWord_6885028
  simp only [CollatzResearch.WordTrace]
  refine ⟨125558800650363450005891869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167411734200484600007855825 125558800650363450005891869)
  ·
    refine ⟨47084550243886293752209451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125558800650363450005891869 47084550243886293752209451)
    ·
      refine ⟨70626825365829440628314177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47084550243886293752209451 70626825365829440628314177)
      ·
        refine ⟨52970119024372080471235633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70626825365829440628314177 52970119024372080471235633)
        ·
          refine ⟨39727589268279060353426725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52970119024372080471235633 39727589268279060353426725)
          ·
            refine ⟨7448922987802323816267511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39727589268279060353426725 7448922987802323816267511)
            ·
              refine ⟨11173384481703485724401267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7448922987802323816267511 11173384481703485724401267)
              ·
                refine ⟨16760076722555228586601901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11173384481703485724401267 16760076722555228586601901)
                ·
                  refine ⟨6285028770958210719975713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16760076722555228586601901 6285028770958210719975713)
                  ·
                    refine ⟨4713771578218658039981785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6285028770958210719975713 4713771578218658039981785)
                    ·
                      refine ⟨3535328683663993529986339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4713771578218658039981785 3535328683663993529986339)
                      ·
                        rfl

theorem cell23_6885028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_6885028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885028 prefixEnd_6885028 := by exact prefixLift 6885028
  have htrace : WordTrace (prefixWord ++ tailWord_6885028) baseStart_6885028 baseEnd_6885028 := by
    simpa [prefixWord, tailWord_6885028, baseEnd_6885028] using wordTrace_append hprefix tailTrace_6885028
  have hstable : (prefixWord ++ tailWord_6885028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885028).length < 2 ^ (prefixWord ++ tailWord_6885028).sum := by decide
  have hdescent : baseEnd_6885028 < baseStart_6885028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885037 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_6885037 : Nat := 118140960795 + 6885037 * 2 ^ 59
def prefixEnd_6885037 : Nat := 4983230072969 + 3 ^ 40 * 6885037 * 2
def baseEnd_6885037 : Nat := 3535333304989883994773797

theorem tailTrace_6885037 : CollatzResearch.WordTrace tailWord_6885037 prefixEnd_6885037 3535333304989883994773797 := by
  unfold tailWord_6885037
  simp only [CollatzResearch.WordTrace]
  refine ⟨251117929557694294548861365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167411953038462863032574243 251117929557694294548861365)
  ·
    refine ⟨23542305896033840113955753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 251117929557694294548861365 23542305896033840113955753)
    ·
      refine ⟨17656729422025380085466815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23542305896033840113955753 17656729422025380085466815)
      ·
        refine ⟨26485094133038070128200223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17656729422025380085466815 26485094133038070128200223)
        ·
          refine ⟨39727641199557105192300335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26485094133038070128200223 39727641199557105192300335)
          ·
            refine ⟨59591461799335657788450503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39727641199557105192300335 59591461799335657788450503)
            ·
              refine ⟨89387192699003486682675755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59591461799335657788450503 89387192699003486682675755)
              ·
                refine ⟨134080789048505230024013633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89387192699003486682675755 134080789048505230024013633)
                ·
                  refine ⟨100560591786378922518010225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134080789048505230024013633 100560591786378922518010225)
                  ·
                    refine ⟨75420443839784191888507669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100560591786378922518010225 75420443839784191888507669)
                    ·
                      refine ⟨3535333304989883994773797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75420443839784191888507669 3535333304989883994773797)
                      ·
                        rfl

theorem cell23_6885037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_6885037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885037 prefixEnd_6885037 := by exact prefixLift 6885037
  have htrace : WordTrace (prefixWord ++ tailWord_6885037) baseStart_6885037 baseEnd_6885037 := by
    simpa [prefixWord, tailWord_6885037, baseEnd_6885037] using wordTrace_append hprefix tailTrace_6885037
  have hstable : (prefixWord ++ tailWord_6885037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885037).length < 2 ^ (prefixWord ++ tailWord_6885037).sum := by decide
  have hdescent : baseEnd_6885037 < baseStart_6885037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885038 : List Nat := [4, 1, 4, 1, 2, 1, 1, 3, 2, 4]
def baseStart_6885038 : Nat := 118140960795 + 6885038 * 2 ^ 59
def prefixEnd_6885038 : Nat := 4983230072969 + 3 ^ 40 * 6885038 * 2
def baseEnd_6885038 : Nat := 1178444606156846163620431

theorem tailTrace_6885038 : CollatzResearch.WordTrace tailWord_6885038 prefixEnd_6885038 1178444606156846163620431 := by
  unfold tailWord_6885038
  simp only [CollatzResearch.WordTrace]
  refine ⟨31389745753836333964955971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167411977353793781146431845 31389745753836333964955971)
  ·
    refine ⟨47084618630754500947433957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31389745753836333964955971 47084618630754500947433957)
    ·
      refine ⟨8828365993266468927643867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47084618630754500947433957 8828365993266468927643867)
      ·
        refine ⟨13242548989899703391465801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8828365993266468927643867 13242548989899703391465801)
        ·
          refine ⟨9931911742424777543599351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13242548989899703391465801 9931911742424777543599351)
          ·
            refine ⟨14897867613637166315399027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9931911742424777543599351 14897867613637166315399027)
            ·
              refine ⟨22346801420455749473098541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14897867613637166315399027 22346801420455749473098541)
              ·
                refine ⟨8380050532670906052411953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22346801420455749473098541 8380050532670906052411953)
                ·
                  refine ⟨6285037899503179539308965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8380050532670906052411953 6285037899503179539308965)
                  ·
                    refine ⟨1178444606156846163620431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6285037899503179539308965 1178444606156846163620431)
                    ·
                      rfl

theorem cell23_6885038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_6885038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885038 prefixEnd_6885038 := by exact prefixLift 6885038
  have htrace : WordTrace (prefixWord ++ tailWord_6885038) baseStart_6885038 baseEnd_6885038 := by
    simpa [prefixWord, tailWord_6885038, baseEnd_6885038] using wordTrace_append hprefix tailTrace_6885038
  have hstable : (prefixWord ++ tailWord_6885038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885038).length < 2 ^ (prefixWord ++ tailWord_6885038).sum := by decide
  have hdescent : baseEnd_6885038 < baseStart_6885038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885087 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 1, 6, 3]
def baseStart_6885087 : Nat := 118140960795 + 6885087 * 2 ^ 59
def prefixEnd_6885087 : Nat := 4983230072969 + 3 ^ 40 * 6885087 * 2
def baseEnd_6885087 : Nat := 3535358979022608799148567

theorem tailTrace_6885087 : CollatzResearch.WordTrace tailWord_6885087 prefixEnd_6885087 3535358979022608799148567 := by
  unfold tailWord_6885087
  simp only [CollatzResearch.WordTrace]
  refine ⟨251119753207513153088181515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167413168805008768725454343 251119753207513153088181515)
  ·
    refine ⟨376679629811269729632272273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251119753207513153088181515 376679629811269729632272273)
    ·
      refine ⟨282509722358452297224204205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376679629811269729632272273 282509722358452297224204205)
      ·
        refine ⟨105941145884419611459076577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282509722358452297224204205 105941145884419611459076577)
        ·
          refine ⟨79455859413314708594307433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105941145884419611459076577 79455859413314708594307433)
          ·
            refine ⟨59591894559986031445730575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79455859413314708594307433 59591894559986031445730575)
            ·
              refine ⟨89387841839979047168595863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59591894559986031445730575 89387841839979047168595863)
              ·
                refine ⟨134081762759968570752893795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89387841839979047168595863 134081762759968570752893795)
                ·
                  refine ⟨201122644139952856129340693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134081762759968570752893795 201122644139952856129340693)
                  ·
                    refine ⟨9427623944060290131062845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 201122644139952856129340693 9427623944060290131062845)
                    ·
                      refine ⟨3535358979022608799148567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9427623944060290131062845 3535358979022608799148567)
                      ·
                        rfl

theorem cell23_6885087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_6885087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885087 prefixEnd_6885087 := by exact prefixLift 6885087
  have htrace : WordTrace (prefixWord ++ tailWord_6885087) baseStart_6885087 baseEnd_6885087 := by
    simpa [prefixWord, tailWord_6885087, baseEnd_6885087] using wordTrace_append hprefix tailTrace_6885087
  have hstable : (prefixWord ++ tailWord_6885087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885087).length < 2 ^ (prefixWord ++ tailWord_6885087).sum := by decide
  have hdescent : baseEnd_6885087 < baseStart_6885087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885101 : List Nat := [1, 5, 1, 2, 1, 2, 1, 3, 1, 4, 2]
def baseStart_6885101 : Nat := 118140960795 + 6885101 * 2 ^ 59
def prefixEnd_6885101 : Nat := 4983230072969 + 3 ^ 40 * 6885101 * 2
def baseEnd_6885101 : Nat := 3535366167751771744373503

theorem tailTrace_6885101 : CollatzResearch.WordTrace tailWord_6885101 prefixEnd_6885101 3535366167751771744373503 := by
  unfold tailWord_6885101
  simp only [CollatzResearch.WordTrace]
  refine ⟨251120263829462433479191157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167413509219641622319460771 251120263829462433479191157)
  ·
    refine ⟨23542524734012103138674171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 251120263829462433479191157 23542524734012103138674171)
    ·
      refine ⟨35313787101018154708011257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23542524734012103138674171 35313787101018154708011257)
      ·
        refine ⟨26485340325763616031008443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35313787101018154708011257 26485340325763616031008443)
        ·
          refine ⟨39728010488645424046512665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26485340325763616031008443 39728010488645424046512665)
          ·
            refine ⟨29796007866484068034884499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39728010488645424046512665 29796007866484068034884499)
            ·
              refine ⟨44694011799726102052326749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29796007866484068034884499 44694011799726102052326749)
              ·
                refine ⟨16760254424897288269622531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44694011799726102052326749 16760254424897288269622531)
                ·
                  refine ⟨25140381637345932404433797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16760254424897288269622531 25140381637345932404433797)
                  ·
                    refine ⟨4713821557002362325831337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25140381637345932404433797 4713821557002362325831337)
                    ·
                      refine ⟨3535366167751771744373503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4713821557002362325831337 3535366167751771744373503)
                      ·
                        rfl

theorem cell23_6885101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_6885101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885101 prefixEnd_6885101 := by exact prefixLift 6885101
  have htrace : WordTrace (prefixWord ++ tailWord_6885101) baseStart_6885101 baseEnd_6885101 := by
    simpa [prefixWord, tailWord_6885101, baseEnd_6885101] using wordTrace_append hprefix tailTrace_6885101
  have hstable : (prefixWord ++ tailWord_6885101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885101).length < 2 ^ (prefixWord ++ tailWord_6885101).sum := by decide
  have hdescent : baseEnd_6885101 < baseStart_6885101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885134 : List Nat := [4, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3]
def baseStart_6885134 : Nat := 118140960795 + 6885134 * 2 ^ 59
def prefixEnd_6885134 : Nat := 4983230072969 + 3 ^ 40 * 6885134 * 2
def baseEnd_6885134 : Nat := 3535383112613370115260851

theorem tailTrace_6885134 : CollatzResearch.WordTrace tailWord_6885134 prefixEnd_6885134 3535383112613370115260851 := by
  unfold tailWord_6885134
  simp only [CollatzResearch.WordTrace]
  refine ⟨31390183429792860014392807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167414311625561920076761637 31390183429792860014392807)
  ·
    refine ⟨47085275144689290021589211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31390183429792860014392807 47085275144689290021589211)
    ·
      refine ⟨70627912717033935032383817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47085275144689290021589211 70627912717033935032383817)
      ·
        refine ⟨52970934537775451274287863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70627912717033935032383817 52970934537775451274287863)
        ·
          refine ⟨79456401806663176911431795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52970934537775451274287863 79456401806663176911431795)
          ·
            refine ⟨119184602709994765367147693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79456401806663176911431795 119184602709994765367147693)
            ·
              refine ⟨44694226016248037012680385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119184602709994765367147693 44694226016248037012680385)
              ·
                refine ⟨33520669512186027759510289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44694226016248037012680385 33520669512186027759510289)
                ·
                  refine ⟨25140502134139520819632717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33520669512186027759510289 25140502134139520819632717)
                  ·
                    refine ⟨9427688300302320307362269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25140502134139520819632717 9427688300302320307362269)
                    ·
                      refine ⟨3535383112613370115260851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9427688300302320307362269 3535383112613370115260851)
                      ·
                        rfl

theorem cell23_6885134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_6885134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885134 prefixEnd_6885134 := by exact prefixLift 6885134
  have htrace : WordTrace (prefixWord ++ tailWord_6885134) baseStart_6885134 baseEnd_6885134 := by
    simpa [prefixWord, tailWord_6885134, baseEnd_6885134] using wordTrace_append hprefix tailTrace_6885134
  have hstable : (prefixWord ++ tailWord_6885134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885134).length < 2 ^ (prefixWord ++ tailWord_6885134).sum := by decide
  have hdescent : baseEnd_6885134 < baseStart_6885134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885137 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 4, 5]
def baseStart_6885137 : Nat := 118140960795 + 6885137 * 2 ^ 59
def prefixEnd_6885137 : Nat := 4983230072969 + 3 ^ 40 * 6885137 * 2
def baseEnd_6885137 : Nat := 1178461551018444534507779

theorem tailTrace_6885137 : CollatzResearch.WordTrace tailWord_6885137 prefixEnd_6885137 1178461551018444534507779 := by
  unfold tailWord_6885137
  simp only [CollatzResearch.WordTrace]
  refine ⟨251121576857332011627501665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167414384571554674418334443 251121576857332011627501665)
  ·
    refine ⟨188341182642999008720626249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251121576857332011627501665 188341182642999008720626249)
    ·
      refine ⟨141255886982249256540469687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188341182642999008720626249 141255886982249256540469687)
      ·
        refine ⟨211883830473373884810704531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141255886982249256540469687 211883830473373884810704531)
        ·
          refine ⟨317825745710060827216056797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211883830473373884810704531 317825745710060827216056797)
          ·
            refine ⟨119184654641272810206021299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317825745710060827216056797 119184654641272810206021299)
            ·
              refine ⟨178776981961909215309031949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119184654641272810206021299 178776981961909215309031949)
              ·
                refine ⟨67041368235715955740886981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178776981961909215309031949 67041368235715955740886981)
                ·
                  refine ⟨12570256544196741701416309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67041368235715955740886981 12570256544196741701416309)
                  ·
                    refine ⟨1178461551018444534507779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12570256544196741701416309 1178461551018444534507779)
                    ·
                      rfl

theorem cell23_6885137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 5].length) (baseStart_6885137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885137 prefixEnd_6885137 := by exact prefixLift 6885137
  have htrace : WordTrace (prefixWord ++ tailWord_6885137) baseStart_6885137 baseEnd_6885137 := by
    simpa [prefixWord, tailWord_6885137, baseEnd_6885137] using wordTrace_append hprefix tailTrace_6885137
  have hstable : (prefixWord ++ tailWord_6885137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885137).length < 2 ^ (prefixWord ++ tailWord_6885137).sum := by decide
  have hdescent : baseEnd_6885137 < baseStart_6885137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885144 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 1, 7, 2]
def baseStart_6885144 : Nat := 118140960795 + 6885144 * 2 ^ 59
def prefixEnd_6885144 : Nat := 4983230072969 + 3 ^ 40 * 6885144 * 2
def baseEnd_6885144 : Nat := 3535388247419915076135805

theorem tailTrace_6885144 : CollatzResearch.WordTrace tailWord_6885144 prefixEnd_6885144 3535388247419915076135805 := by
  unfold tailWord_6885144
  simp only [CollatzResearch.WordTrace]
  refine ⟨125560916084153325911503243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167414554778871101215337657 125560916084153325911503243)
  ·
    refine ⟨188341374126229988867254865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125560916084153325911503243 188341374126229988867254865)
    ·
      refine ⟨141256030594672491650441149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188341374126229988867254865 141256030594672491650441149)
      ·
        refine ⟨52971011473002184368915431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141256030594672491650441149 52971011473002184368915431)
        ·
          refine ⟨79456517209503276553373147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52971011473002184368915431 79456517209503276553373147)
          ·
            refine ⟨119184775814254914830059721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79456517209503276553373147 119184775814254914830059721)
            ·
              refine ⟨89388581860691186122544791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119184775814254914830059721 89388581860691186122544791)
              ·
                refine ⟨134082872791036779183817187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89388581860691186122544791 134082872791036779183817187)
                ·
                  refine ⟨201124309186555168775725781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134082872791036779183817187 201124309186555168775725781)
                  ·
                    refine ⟨4713850996559886768181073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 201124309186555168775725781 4713850996559886768181073)
                    ·
                      refine ⟨3535388247419915076135805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4713850996559886768181073 3535388247419915076135805)
                      ·
                        rfl

theorem cell23_6885144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_6885144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885144 prefixEnd_6885144 := by exact prefixLift 6885144
  have htrace : WordTrace (prefixWord ++ tailWord_6885144) baseStart_6885144 baseEnd_6885144 := by
    simpa [prefixWord, tailWord_6885144, baseEnd_6885144] using wordTrace_append hprefix tailTrace_6885144
  have hstable : (prefixWord ++ tailWord_6885144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885144).length < 2 ^ (prefixWord ++ tailWord_6885144).sum := by decide
  have hdescent : baseEnd_6885144 < baseStart_6885144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885201 : List Nat := [1, 2, 2, 1, 5, 1, 3, 1, 3, 4]
def baseStart_6885201 : Nat := 118140960795 + 6885201 * 2 ^ 59
def prefixEnd_6885201 : Nat := 4983230072969 + 3 ^ 40 * 6885201 * 2
def baseEnd_6885201 : Nat := 1178472505272407117707681

theorem tailTrace_6885201 : CollatzResearch.WordTrace tailWord_6885201 prefixEnd_6885201 1178472505272407117707681 := by
  unfold tailWord_6885201
  simp only [CollatzResearch.WordTrace]
  refine ⟨251123911129100150557831457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167415940752733433705220971 251123911129100150557831457)
  ·
    refine ⟨188342933346825112918373593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251123911129100150557831457 188342933346825112918373593)
    ·
      refine ⟨141257200010118834688780195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188342933346825112918373593 141257200010118834688780195)
      ·
        refine ⟨211885800015178252033170293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141257200010118834688780195 211885800015178252033170293)
        ·
          refine ⟨19864293751422961128109715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 211885800015178252033170293 19864293751422961128109715)
          ·
            refine ⟨29796440627134441692164573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19864293751422961128109715 29796440627134441692164573)
            ·
              refine ⟨11173665235175415634561715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29796440627134441692164573 11173665235175415634561715)
              ·
                refine ⟨16760497852763123451842573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11173665235175415634561715 16760497852763123451842573)
                ·
                  refine ⟨6285186694786171294440965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16760497852763123451842573 6285186694786171294440965)
                  ·
                    refine ⟨1178472505272407117707681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6285186694786171294440965 1178472505272407117707681)
                    ·
                      rfl

theorem cell23_6885201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 3, 4].length) (baseStart_6885201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885201 prefixEnd_6885201 := by exact prefixLift 6885201
  have htrace : WordTrace (prefixWord ++ tailWord_6885201) baseStart_6885201 baseEnd_6885201 := by
    simpa [prefixWord, tailWord_6885201, baseEnd_6885201] using wordTrace_append hprefix tailTrace_6885201
  have hstable : (prefixWord ++ tailWord_6885201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885201).length < 2 ^ (prefixWord ++ tailWord_6885201).sum := by decide
  have hdescent : baseEnd_6885201 < baseStart_6885201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885264 : List Nat := [2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 4]
def baseStart_6885264 : Nat := 118140960795 + 6885264 * 2 ^ 59
def prefixEnd_6885264 : Nat := 4983230072969 + 3 ^ 40 * 6885264 * 2
def baseEnd_6885264 : Nat := 3535449865098454606635253

theorem tailTrace_6885264 : CollatzResearch.WordTrace tailWord_6885264 prefixEnd_6885264 3535449865098454606635253 := by
  unfold tailWord_6885264
  simp only [CollatzResearch.WordTrace]
  refine ⟨125563104463935956158687423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167417472618581274878249897 125563104463935956158687423)
  ·
    refine ⟨188344656695903934238031135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125563104463935956158687423 188344656695903934238031135)
    ·
      refine ⟨282516985043855901357046703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188344656695903934238031135 282516985043855901357046703)
      ·
        refine ⟨423775477565783852035570055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282516985043855901357046703 423775477565783852035570055)
        ·
          refine ⟨635663216348675778053355083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423775477565783852035570055 635663216348675778053355083)
          ·
            refine ⟨953494824523013667080032625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635663216348675778053355083 953494824523013667080032625)
            ·
              refine ⟨715121118392260250310024469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 953494824523013667080032625 715121118392260250310024469)
              ·
                refine ⟨33521302424637199233282397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 715121118392260250310024469 33521302424637199233282397)
                ·
                  refine ⟨12570488409238949712480899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33521302424637199233282397 12570488409238949712480899)
                  ·
                    refine ⟨18855732613858424568721349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12570488409238949712480899 18855732613858424568721349)
                    ·
                      refine ⟨3535449865098454606635253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18855732613858424568721349 3535449865098454606635253)
                      ·
                        rfl

theorem cell23_6885264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 4].length) (baseStart_6885264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885264 prefixEnd_6885264 := by exact prefixLift 6885264
  have htrace : WordTrace (prefixWord ++ tailWord_6885264) baseStart_6885264 baseEnd_6885264 := by
    simpa [prefixWord, tailWord_6885264, baseEnd_6885264] using wordTrace_append hprefix tailTrace_6885264
  have hstable : (prefixWord ++ tailWord_6885264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885264).length < 2 ^ (prefixWord ++ tailWord_6885264).sum := by decide
  have hdescent : baseEnd_6885264 < baseStart_6885264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885338 : List Nat := [3, 1, 1, 2, 5, 2, 2, 7]
def baseStart_6885338 : Nat := 118140960795 + 6885338 * 2 ^ 59
def prefixEnd_6885338 : Nat := 4983230072969 + 3 ^ 40 * 6885338 * 2
def baseEnd_6885338 : Nat := 130943994913588419152219

theorem tailTrace_6885338 : CollatzResearch.WordTrace tailWord_6885338 prefixEnd_6885338 130943994913588419152219 := by
  unfold tailWord_6885338
  simp only [CollatzResearch.WordTrace]
  refine ⟨62782226982400955738892167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167419271953069215303712445 62782226982400955738892167)
  ·
    refine ⟨94173340473601433608338251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62782226982400955738892167 94173340473601433608338251)
    ·
      refine ⟨141260010710402150412507377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94173340473601433608338251 141260010710402150412507377)
      ·
        refine ⟨105945008032801612809380533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141260010710402150412507377 105945008032801612809380533)
        ·
          refine ⟨9932344503075151200879425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105945008032801612809380533 9932344503075151200879425)
          ·
            refine ⟨7449258377306363400659569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9932344503075151200879425 7449258377306363400659569)
            ·
              refine ⟨5586943782979772550494677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7449258377306363400659569 5586943782979772550494677)
              ·
                refine ⟨130943994913588419152219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5586943782979772550494677 130943994913588419152219)
                ·
                  rfl

theorem cell23_6885338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 7].length) (baseStart_6885338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885338 prefixEnd_6885338 := by exact prefixLift 6885338
  have htrace : WordTrace (prefixWord ++ tailWord_6885338) baseStart_6885338 baseEnd_6885338 := by
    simpa [prefixWord, tailWord_6885338, baseEnd_6885338] using wordTrace_append hprefix tailTrace_6885338
  have hstable : (prefixWord ++ tailWord_6885338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885338).length < 2 ^ (prefixWord ++ tailWord_6885338).sum := by decide
  have hdescent : baseEnd_6885338 < baseStart_6885338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885366 : List Nat := [5, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2]
def baseStart_6885366 : Nat := 118140960795 + 6885366 * 2 ^ 59
def prefixEnd_6885366 : Nat := 4983230072969 + 3 ^ 40 * 6885366 * 2
def baseEnd_6885366 : Nat := 3535502240125213207559785

theorem tailTrace_6885366 : CollatzResearch.WordTrace tailWord_6885366 prefixEnd_6885366 3535502240125213207559785 := by
  unfold tailWord_6885366
  simp only [CollatzResearch.WordTrace]
  refine ⟨15695620573343898983599247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167419952782334922491725301 15695620573343898983599247)
  ·
    refine ⟨23543430860015848475398871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15695620573343898983599247 23543430860015848475398871)
    ·
      refine ⟨35315146290023772713098307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23543430860015848475398871 35315146290023772713098307)
      ·
        refine ⟨52972719435035659069647461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35315146290023772713098307 52972719435035659069647461)
        ·
          refine ⟨9932384894069186075558899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52972719435035659069647461 9932384894069186075558899)
          ·
            refine ⟨14898577341103779113338349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9932384894069186075558899 14898577341103779113338349)
            ·
              refine ⟨5586966502913917167501881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14898577341103779113338349 5586966502913917167501881)
              ·
                refine ⟨4190224877185437875626411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5586966502913917167501881 4190224877185437875626411)
                ·
                  refine ⟨6285337315778156813439617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4190224877185437875626411 6285337315778156813439617)
                  ·
                    refine ⟨4714002986833617610079713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6285337315778156813439617 4714002986833617610079713)
                    ·
                      refine ⟨3535502240125213207559785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4714002986833617610079713 3535502240125213207559785)
                      ·
                        rfl

theorem cell23_6885366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_6885366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885366 prefixEnd_6885366 := by exact prefixLift 6885366
  have htrace : WordTrace (prefixWord ++ tailWord_6885366) baseStart_6885366 baseEnd_6885366 := by
    simpa [prefixWord, tailWord_6885366, baseEnd_6885366] using wordTrace_append hprefix tailTrace_6885366
  have hstable : (prefixWord ++ tailWord_6885366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885366).length < 2 ^ (prefixWord ++ tailWord_6885366).sum := by decide
  have hdescent : baseEnd_6885366 < baseStart_6885366 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885388 : List Nat := [2, 2, 1, 2, 3, 1, 2, 3, 1, 4, 2]
def baseStart_6885388 : Nat := 118140960795 + 6885388 * 2 ^ 59
def prefixEnd_6885388 : Nat := 4983230072969 + 3 ^ 40 * 6885388 * 2
def baseEnd_6885388 : Nat := 3535513536699612121484683

theorem tailTrace_6885388 : CollatzResearch.WordTrace tailWord_6885388 prefixEnd_6885388 3535513536699612121484683 := by
  unfold tailWord_6885388
  simp only [CollatzResearch.WordTrace]
  refine ⟨125565365789711340747444409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167420487719615120996592545 125565365789711340747444409)
  ·
    refine ⟨94174024342283505560583307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125565365789711340747444409 94174024342283505560583307)
    ·
      refine ⟨141261036513425258340874961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94174024342283505560583307 141261036513425258340874961)
      ·
        refine ⟨105945777385068943755656221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141261036513425258340874961 105945777385068943755656221)
        ·
          refine ⟨39729666519400853908371083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105945777385068943755656221 39729666519400853908371083)
          ·
            refine ⟨59594499779101280862556625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39729666519400853908371083 59594499779101280862556625)
            ·
              refine ⟨44695874834325960646917469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59594499779101280862556625 44695874834325960646917469)
              ·
                refine ⟨16760953062872235242594051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44695874834325960646917469 16760953062872235242594051)
                ·
                  refine ⟨25141429594308352863891077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16760953062872235242594051 25141429594308352863891077)
                  ·
                    refine ⟨4714018048932816161979577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25141429594308352863891077 4714018048932816161979577)
                    ·
                      refine ⟨3535513536699612121484683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4714018048932816161979577 3535513536699612121484683)
                      ·
                        rfl

theorem cell23_6885388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 1, 4, 2].length) (baseStart_6885388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885388 prefixEnd_6885388 := by exact prefixLift 6885388
  have htrace : WordTrace (prefixWord ++ tailWord_6885388) baseStart_6885388 baseEnd_6885388 := by
    simpa [prefixWord, tailWord_6885388, baseEnd_6885388] using wordTrace_append hprefix tailTrace_6885388
  have hstable : (prefixWord ++ tailWord_6885388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885388).length < 2 ^ (prefixWord ++ tailWord_6885388).sum := by decide
  have hdescent : baseEnd_6885388 < baseStart_6885388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885405 : List Nat := [1, 4, 2, 2, 2, 2, 1, 2, 1, 4, 2]
def baseStart_6885405 : Nat := 118140960795 + 6885405 * 2 ^ 59
def prefixEnd_6885405 : Nat := 4983230072969 + 3 ^ 40 * 6885405 * 2
def baseEnd_6885405 : Nat := 3535522265870738554972105

theorem tailTrace_6885405 : CollatzResearch.WordTrace tailWord_6885405 prefixEnd_6885405 3535522265870738554972105 := by
  unfold tailWord_6885405
  simp only [CollatzResearch.WordTrace]
  refine ⟨251131351620361093398257669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167420901080240728932171779 251131351620361093398257669)
  ·
    refine ⟨47087128428817705012173313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251131351620361093398257669 47087128428817705012173313)
    ·
      refine ⟨35315346321613278759129985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47087128428817705012173313 35315346321613278759129985)
      ·
        refine ⟨26486509741209959069347489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35315346321613278759129985 26486509741209959069347489)
        ·
          refine ⟨19864882305907469302010617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26486509741209959069347489 19864882305907469302010617)
          ·
            refine ⟨14898661729430601976507963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19864882305907469302010617 14898661729430601976507963)
            ·
              refine ⟨22347992594145902964761945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14898661729430601976507963 22347992594145902964761945)
              ·
                refine ⟨16760994445609427223571459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22347992594145902964761945 16760994445609427223571459)
                ·
                  refine ⟨25141491668414140835357189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16760994445609427223571459 25141491668414140835357189)
                  ·
                    refine ⟨4714029687827651406629473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25141491668414140835357189 4714029687827651406629473)
                    ·
                      refine ⟨3535522265870738554972105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4714029687827651406629473 3535522265870738554972105)
                      ·
                        rfl

theorem cell23_6885405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_6885405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885405 prefixEnd_6885405 := by exact prefixLift 6885405
  have htrace : WordTrace (prefixWord ++ tailWord_6885405) baseStart_6885405 baseEnd_6885405 := by
    simpa [prefixWord, tailWord_6885405, baseEnd_6885405] using wordTrace_append hprefix tailTrace_6885405
  have hstable : (prefixWord ++ tailWord_6885405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885405).length < 2 ^ (prefixWord ++ tailWord_6885405).sum := by decide
  have hdescent : baseEnd_6885405 < baseStart_6885405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885422 : List Nat := [4, 1, 3, 1, 1, 2, 1, 4, 2, 2, 2]
def baseStart_6885422 : Nat := 118140960795 + 6885422 * 2 ^ 59
def prefixEnd_6885422 : Nat := 4983230072969 + 3 ^ 40 * 6885422 * 2
def baseEnd_6885422 : Nat := 3535530995041864988459527

theorem tailTrace_6885422 : CollatzResearch.WordTrace tailWord_6885422 prefixEnd_6885422 3535530995041864988459527 := by
  unfold tailWord_6885422
  simp only [CollatzResearch.WordTrace]
  refine ⟨31391496457662438162703315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167421314440866336867751013 31391496457662438162703315)
  ·
    refine ⟨47087244686493657244054973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31391496457662438162703315 47087244686493657244054973)
    ·
      refine ⟨17657716757435121466520615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47087244686493657244054973 17657716757435121466520615)
      ·
        refine ⟨26486575136152682199780923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17657716757435121466520615 26486575136152682199780923)
        ·
          refine ⟨39729862704229023299671385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26486575136152682199780923 39729862704229023299671385)
          ·
            refine ⟨29797397028171767474753539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39729862704229023299671385 29797397028171767474753539)
            ·
              refine ⟨44696095542257651212130309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29797397028171767474753539 44696095542257651212130309)
              ·
                refine ⟨8380517914173309602274433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44696095542257651212130309 8380517914173309602274433)
                ·
                  refine ⟨6285388435629982201705825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8380517914173309602274433 6285388435629982201705825)
                  ·
                    refine ⟨4714041326722486651279369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6285388435629982201705825 4714041326722486651279369)
                    ·
                      refine ⟨3535530995041864988459527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4714041326722486651279369 3535530995041864988459527)
                      ·
                        rfl

theorem cell23_6885422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_6885422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885422 prefixEnd_6885422 := by exact prefixLift 6885422
  have htrace : WordTrace (prefixWord ++ tailWord_6885422) baseStart_6885422 baseEnd_6885422 := by
    simpa [prefixWord, tailWord_6885422, baseEnd_6885422] using wordTrace_append hprefix tailTrace_6885422
  have hstable : (prefixWord ++ tailWord_6885422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885422).length < 2 ^ (prefixWord ++ tailWord_6885422).sum := by decide
  have hdescent : baseEnd_6885422 < baseStart_6885422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885458 : List Nat := [3, 2, 2, 1, 4, 1, 1, 1, 1, 7]
def baseStart_6885458 : Nat := 118140960795 + 6885458 * 2 ^ 59
def prefixEnd_6885458 : Nat := 4983230072969 + 3 ^ 40 * 6885458 * 2
def baseEnd_6885458 : Nat := 1178516493448475615869787

theorem tailTrace_6885458 : CollatzResearch.WordTrace tailWord_6885458 prefixEnd_6885458 1178516493448475615869787 := by
  unfold tailWord_6885458
  simp only [CollatzResearch.WordTrace]
  refine ⟨62783321172292270862484257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167422189792779388966624685 62783321172292270862484257)
  ·
    refine ⟨47087490879219203146863193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62783321172292270862484257 47087490879219203146863193)
    ·
      refine ⟨35315618159414402360147395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47087490879219203146863193 35315618159414402360147395)
      ·
        refine ⟨52973427239121603540221093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35315618159414402360147395 52973427239121603540221093)
        ·
          refine ⟨9932517607335300663791455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52973427239121603540221093 9932517607335300663791455)
          ·
            refine ⟨14898776411002950995687183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9932517607335300663791455 14898776411002950995687183)
            ·
              refine ⟨22348164616504426493530775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14898776411002950995687183 22348164616504426493530775)
              ·
                refine ⟨33522246924756639740296163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22348164616504426493530775 33522246924756639740296163)
                ·
                  refine ⟨50283370387134959610444245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33522246924756639740296163 50283370387134959610444245)
                  ·
                    refine ⟨1178516493448475615869787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50283370387134959610444245 1178516493448475615869787)
                    ·
                      rfl

theorem cell23_6885458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_6885458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885458 prefixEnd_6885458 := by exact prefixLift 6885458
  have htrace : WordTrace (prefixWord ++ tailWord_6885458) baseStart_6885458 baseEnd_6885458 := by
    simpa [prefixWord, tailWord_6885458, baseEnd_6885458] using wordTrace_append hprefix tailTrace_6885458
  have hstable : (prefixWord ++ tailWord_6885458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885458).length < 2 ^ (prefixWord ++ tailWord_6885458).sum := by decide
  have hdescent : baseEnd_6885458 < baseStart_6885458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885462 : List Nat := [5, 2, 2, 1, 1, 1, 1, 5, 5]
def baseStart_6885462 : Nat := 118140960795 + 6885462 * 2 ^ 59
def prefixEnd_6885462 : Nat := 4983230072969 + 3 ^ 40 * 6885462 * 2
def baseEnd_6885462 : Nat := 392839059363116092439927

theorem tailTrace_6885462 : CollatzResearch.WordTrace tailWord_6885462 prefixEnd_6885462 392839059363116092439927 := by
  unfold tailWord_6885462
  simp only [CollatzResearch.WordTrace]
  refine ⟨15695839411322162008317665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167422287054103061422055093 15695839411322162008317665)
  ·
    refine ⟨11771879558491621506238249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15695839411322162008317665 11771879558491621506238249)
    ·
      refine ⟨8828909668868716129678687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11771879558491621506238249 8828909668868716129678687)
      ·
        refine ⟨13243364503303074194518031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8828909668868716129678687 13243364503303074194518031)
        ·
          refine ⟨19865046754954611291777047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13243364503303074194518031 19865046754954611291777047)
          ·
            refine ⟨29797570132431916937665571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19865046754954611291777047 29797570132431916937665571)
            ·
              refine ⟨44696355198647875406498357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29797570132431916937665571 44696355198647875406498357)
              ·
                refine ⟨4190283299873238319359221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44696355198647875406498357 4190283299873238319359221)
                ·
                  refine ⟨392839059363116092439927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4190283299873238319359221 392839059363116092439927)
                  ·
                    rfl

theorem cell23_6885462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_6885462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885462 prefixEnd_6885462 := by exact prefixLift 6885462
  have htrace : WordTrace (prefixWord ++ tailWord_6885462) baseStart_6885462 baseEnd_6885462 := by
    simpa [prefixWord, tailWord_6885462, baseEnd_6885462] using wordTrace_append hprefix tailTrace_6885462
  have hstable : (prefixWord ++ tailWord_6885462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885462).length < 2 ^ (prefixWord ++ tailWord_6885462).sum := by decide
  have hdescent : baseEnd_6885462 < baseStart_6885462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885488 : List Nat := [2, 1, 1, 1, 5, 2, 1, 3, 3, 4]
def baseStart_6885488 : Nat := 118140960795 + 6885488 * 2 ^ 59
def prefixEnd_6885488 : Nat := 4983230072969 + 3 ^ 40 * 6885488 * 2
def baseEnd_6885488 : Nat := 1178521628255020576744741

theorem tailTrace_6885488 : CollatzResearch.WordTrace tailWord_6885488 prefixEnd_6885488 1178521628255020576744741 := by
  unfold tailWord_6885488
  simp only [CollatzResearch.WordTrace]
  refine ⟨125567189439530199286764559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167422919252706932382352745 125567189439530199286764559)
  ·
    refine ⟨188350784159295298930146839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125567189439530199286764559 188350784159295298930146839)
    ·
      refine ⟨282526176238942948395220259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188350784159295298930146839 282526176238942948395220259)
      ·
        refine ⟨423789264358414422592830389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282526176238942948395220259 423789264358414422592830389)
        ·
          refine ⟨39730243533601352118077849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 423789264358414422592830389 39730243533601352118077849)
          ·
            refine ⟨29797682650201014088558387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39730243533601352118077849 29797682650201014088558387)
            ·
              refine ⟨44696523975301521132837581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29797682650201014088558387 44696523975301521132837581)
              ·
                refine ⟨16761196490738070424814093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44696523975301521132837581 16761196490738070424814093)
                ·
                  refine ⟨6285448684026776409305285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16761196490738070424814093 6285448684026776409305285)
                  ·
                    refine ⟨1178521628255020576744741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6285448684026776409305285 1178521628255020576744741)
                    ·
                      rfl

theorem cell23_6885488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 3, 4].length) (baseStart_6885488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885488 prefixEnd_6885488 := by exact prefixLift 6885488
  have htrace : WordTrace (prefixWord ++ tailWord_6885488) baseStart_6885488 baseEnd_6885488 := by
    simpa [prefixWord, tailWord_6885488, baseEnd_6885488] using wordTrace_append hprefix tailTrace_6885488
  have hstable : (prefixWord ++ tailWord_6885488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885488).length < 2 ^ (prefixWord ++ tailWord_6885488).sum := by decide
  have hdescent : baseEnd_6885488 < baseStart_6885488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885526 : List Nat := [5, 3, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_6885526 : Nat := 118140960795 + 6885526 * 2 ^ 59
def prefixEnd_6885526 : Nat := 4983230072969 + 3 ^ 40 * 6885526 * 2
def baseEnd_6885526 : Nat := 1178528132343310860519683

theorem tailTrace_6885526 : CollatzResearch.WordTrace tailWord_6885526 prefixEnd_6885526 1178528132343310860519683 := by
  unfold tailWord_6885526
  simp only [CollatzResearch.WordTrace]
  refine ⟨15695985303307670691463277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167423843235281820708941621 15695985303307670691463277)
  ·
    refine ⟨5885994488740376509298729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15695985303307670691463277 5885994488740376509298729)
    ·
      refine ⟨4414495866555282381974047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5885994488740376509298729 4414495866555282381974047)
      ·
        refine ⟨6621743799832923572961071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4414495866555282381974047 6621743799832923572961071)
        ·
          refine ⟨9932615699749385359441607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6621743799832923572961071 9932615699749385359441607)
          ·
            refine ⟨14898923549624078039162411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9932615699749385359441607 14898923549624078039162411)
            ·
              refine ⟨22348385324436117058743617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14898923549624078039162411 22348385324436117058743617)
              ·
                refine ⟨16761288993327087794057713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22348385324436117058743617 16761288993327087794057713)
                ·
                  refine ⟨12570966744995315845543285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16761288993327087794057713 12570966744995315845543285)
                  ·
                    refine ⟨1178528132343310860519683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12570966744995315845543285 1178528132343310860519683)
                    ·
                      rfl

theorem cell23_6885526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_6885526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885526 prefixEnd_6885526 := by exact prefixLift 6885526
  have htrace : WordTrace (prefixWord ++ tailWord_6885526) baseStart_6885526 baseEnd_6885526 := by
    simpa [prefixWord, tailWord_6885526, baseEnd_6885526] using wordTrace_append hprefix tailTrace_6885526
  have hstable : (prefixWord ++ tailWord_6885526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885526).length < 2 ^ (prefixWord ++ tailWord_6885526).sum := by decide
  have hdescent : baseEnd_6885526 < baseStart_6885526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885551 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 4]
def baseStart_6885551 : Nat := 118140960795 + 6885551 * 2 ^ 59
def prefixEnd_6885551 : Nat := 4983230072969 + 3 ^ 40 * 6885551 * 2
def baseEnd_6885551 : Nat := 3535597234046294983746433

theorem tailTrace_6885551 : CollatzResearch.WordTrace tailWord_6885551 prefixEnd_6885551 3535597234046294983746433 := by
  unfold tailWord_6885551
  simp only [CollatzResearch.WordTrace]
  refine ⟨251136676677832160333072507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167424451118554773555381671 251136676677832160333072507)
  ·
    refine ⟨376705015016748240499608761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251136676677832160333072507 376705015016748240499608761)
    ·
      refine ⟨282528761262561180374706571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376705015016748240499608761 282528761262561180374706571)
      ·
        refine ⟨423793141893841770562059857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282528761262561180374706571 423793141893841770562059857)
        ·
          refine ⟨317844856420381327921544893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423793141893841770562059857 317844856420381327921544893)
          ·
            refine ⟨119191821157642997970579335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317844856420381327921544893 119191821157642997970579335)
            ·
              refine ⟨178787731736464496955869003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119191821157642997970579335 178787731736464496955869003)
              ·
                refine ⟨268181597604696745433803505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178787731736464496955869003 268181597604696745433803505)
                ·
                  refine ⟨201136198203522559075352629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 268181597604696745433803505 201136198203522559075352629)
                  ·
                    refine ⟨18856518581580239913314309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 201136198203522559075352629 18856518581580239913314309)
                    ·
                      refine ⟨3535597234046294983746433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18856518581580239913314309 3535597234046294983746433)
                      ·
                        rfl

theorem cell23_6885551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 4].length) (baseStart_6885551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885551 prefixEnd_6885551 := by exact prefixLift 6885551
  have htrace : WordTrace (prefixWord ++ tailWord_6885551) baseStart_6885551 baseEnd_6885551 := by
    simpa [prefixWord, tailWord_6885551, baseEnd_6885551] using wordTrace_append hprefix tailTrace_6885551
  have hstable : (prefixWord ++ tailWord_6885551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885551).length < 2 ^ (prefixWord ++ tailWord_6885551).sum := by decide
  have hdescent : baseEnd_6885551 < baseStart_6885551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885572 : List Nat := [2, 3, 3, 1, 2, 1, 1, 3, 2, 3, 2]
def baseStart_6885572 : Nat := 118140960795 + 6885572 * 2 ^ 59
def prefixEnd_6885572 : Nat := 4983230072969 + 3 ^ 40 * 6885572 * 2
def baseEnd_6885572 : Nat := 3535608017140039401583837

theorem tailTrace_6885572 : CollatzResearch.WordTrace tailWord_6885572 prefixEnd_6885572 3535608017140039401583837 := by
  unfold tailWord_6885572
  simp only [CollatzResearch.WordTrace]
  refine ⟨125568721305378040459793485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167424961740504053946391313 125568721305378040459793485)
  ·
    refine ⟨47088270489516765172422557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125568721305378040459793485 47088270489516765172422557)
    ·
      refine ⟨17658101433568786939658459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47088270489516765172422557 17658101433568786939658459)
      ·
        refine ⟨26487152150353180409487689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17658101433568786939658459 26487152150353180409487689)
        ·
          refine ⟨19865364112764885307115767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26487152150353180409487689 19865364112764885307115767)
          ·
            refine ⟨29798046169147327960673651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19865364112764885307115767 29798046169147327960673651)
            ·
              refine ⟨44697069253720991941010477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29798046169147327960673651 44697069253720991941010477)
              ·
                refine ⟨16761400970145371977878929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44697069253720991941010477 16761400970145371977878929)
                ·
                  refine ⟨12571050727609028983409197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16761400970145371977878929 12571050727609028983409197)
                  ·
                    refine ⟨4714144022853385868778449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12571050727609028983409197 4714144022853385868778449)
                    ·
                      refine ⟨3535608017140039401583837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4714144022853385868778449 3535608017140039401583837)
                      ·
                        rfl

theorem cell23_6885572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_6885572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885572 prefixEnd_6885572 := by exact prefixLift 6885572
  have htrace : WordTrace (prefixWord ++ tailWord_6885572) baseStart_6885572 baseEnd_6885572 := by
    simpa [prefixWord, tailWord_6885572, baseEnd_6885572] using wordTrace_append hprefix tailTrace_6885572
  have hstable : (prefixWord ++ tailWord_6885572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885572).length < 2 ^ (prefixWord ++ tailWord_6885572).sum := by decide
  have hdescent : baseEnd_6885572 < baseStart_6885572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885578 : List Nat := [3, 1, 2, 1, 3, 1, 3, 2, 1, 6]
def baseStart_6885578 : Nat := 118140960795 + 6885578 * 2 ^ 59
def prefixEnd_6885578 : Nat := 4983230072969 + 3 ^ 40 * 6885578 * 2
def baseEnd_6885578 : Nat := 1178537032674655459369603

theorem tailTrace_6885578 : CollatzResearch.WordTrace tailWord_6885578 prefixEnd_6885578 1178537032674655459369603 := by
  unfold tailWord_6885578
  simp only [CollatzResearch.WordTrace]
  refine ⟨62784415362183585986076347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167425107632489562629536925 62784415362183585986076347)
  ·
    refine ⟨94176623043275378979114521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62784415362183585986076347 94176623043275378979114521)
    ·
      refine ⟨70632467282456534234335891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94176623043275378979114521 70632467282456534234335891)
      ·
        refine ⟨105948700923684801351503837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70632467282456534234335891 105948700923684801351503837)
        ·
          refine ⟨39730762846381800506813939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105948700923684801351503837 39730762846381800506813939)
          ·
            refine ⟨59596144269572700760220909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39730762846381800506813939 59596144269572700760220909)
            ·
              refine ⟨22348554101089762785082841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59596144269572700760220909 22348554101089762785082841)
              ·
                refine ⟨16761415575817322088812131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22348554101089762785082841 16761415575817322088812131)
                ·
                  refine ⟨25142123363725983133218197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16761415575817322088812131 25142123363725983133218197)
                  ·
                    refine ⟨1178537032674655459369603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25142123363725983133218197 1178537032674655459369603)
                    ·
                      rfl

theorem cell23_6885578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_6885578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885578 prefixEnd_6885578 := by exact prefixLift 6885578
  have htrace : WordTrace (prefixWord ++ tailWord_6885578) baseStart_6885578 baseEnd_6885578 := by
    simpa [prefixWord, tailWord_6885578, baseEnd_6885578] using wordTrace_append hprefix tailTrace_6885578
  have hstable : (prefixWord ++ tailWord_6885578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885578).length < 2 ^ (prefixWord ++ tailWord_6885578).sum := by decide
  have hdescent : baseEnd_6885578 < baseStart_6885578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885582 : List Nat := [4, 1, 1, 1, 4, 2, 3, 1, 1, 5]
def baseStart_6885582 : Nat := 118140960795 + 6885582 * 2 ^ 59
def prefixEnd_6885582 : Nat := 4983230072969 + 3 ^ 40 * 6885582 * 2
def baseEnd_6885582 : Nat := 1178537717315528120819597

theorem tailTrace_6885582 : CollatzResearch.WordTrace tailWord_6885582 prefixEnd_6885582 1178537717315528120819597 := by
  unfold tailWord_6885582
  simp only [CollatzResearch.WordTrace]
  refine ⟨31392225917589981578431375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167425204893813235084967333 31392225917589981578431375)
  ·
    refine ⟨47088338876384972367647063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31392225917589981578431375 47088338876384972367647063)
    ·
      refine ⟨70632508314577458551470595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47088338876384972367647063 70632508314577458551470595)
      ·
        refine ⟨105948762471866187827205893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70632508314577458551470595 105948762471866187827205893)
        ·
          refine ⟨19865392963474910217601105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105948762471866187827205893 19865392963474910217601105)
          ·
            refine ⟨14899044722606182663200829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19865392963474910217601105 14899044722606182663200829)
            ·
              refine ⟨5587141770977318498700311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14899044722606182663200829 5587141770977318498700311)
              ·
                refine ⟨8380712656465977748050467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5587141770977318498700311 8380712656465977748050467)
                ·
                  refine ⟨12571068984698966622075701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8380712656465977748050467 12571068984698966622075701)
                  ·
                    refine ⟨1178537717315528120819597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12571068984698966622075701 1178537717315528120819597)
                    ·
                      rfl

theorem cell23_6885582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_6885582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885582 prefixEnd_6885582 := by exact prefixLift 6885582
  have htrace : WordTrace (prefixWord ++ tailWord_6885582) baseStart_6885582 baseEnd_6885582 := by
    simpa [prefixWord, tailWord_6885582, baseEnd_6885582] using wordTrace_append hprefix tailTrace_6885582
  have hstable : (prefixWord ++ tailWord_6885582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885582).length < 2 ^ (prefixWord ++ tailWord_6885582).sum := by decide
  have hdescent : baseEnd_6885582 < baseStart_6885582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885605 : List Nat := [1, 3, 1, 4, 2, 1, 1, 2, 3, 2, 3]
def baseStart_6885605 : Nat := 118140960795 + 6885605 * 2 ^ 59
def prefixEnd_6885605 : Nat := 4983230072969 + 3 ^ 40 * 6885605 * 2
def baseEnd_6885605 : Nat := 3535624962001637772471185

theorem tailTrace_6885605 : CollatzResearch.WordTrace tailWord_6885605 prefixEnd_6885605 3535624962001637772471185 := by
  unfold tailWord_6885605
  simp only [CollatzResearch.WordTrace]
  refine ⟨251138646219636527555538269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167425764146424351703692179 251138646219636527555538269)
  ·
    refine ⟨94176992332363697833326851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251138646219636527555538269 94176992332363697833326851)
    ·
      refine ⟨141265488498545546749990277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94176992332363697833326851 141265488498545546749990277)
      ·
        refine ⟨26487279093477290015623177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141265488498545546749990277 26487279093477290015623177)
        ·
          refine ⟨19865459320107967511717383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26487279093477290015623177 19865459320107967511717383)
          ·
            refine ⟨29798188980161951267576075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19865459320107967511717383 29798188980161951267576075)
            ·
              refine ⟨44697283470242926901364113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29798188980161951267576075 44697283470242926901364113)
              ·
                refine ⟨33522962602682195176023085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44697283470242926901364113 33522962602682195176023085)
                ·
                  refine ⟨12571110976005823191008657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33522962602682195176023085 12571110976005823191008657)
                  ·
                    refine ⟨9428333232004367393256493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12571110976005823191008657 9428333232004367393256493)
                    ·
                      refine ⟨3535624962001637772471185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9428333232004367393256493 3535624962001637772471185)
                      ·
                        rfl

theorem cell23_6885605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_6885605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885605 prefixEnd_6885605 := by exact prefixLift 6885605
  have htrace : WordTrace (prefixWord ++ tailWord_6885605) baseStart_6885605 baseEnd_6885605 := by
    simpa [prefixWord, tailWord_6885605, baseEnd_6885605] using wordTrace_append hprefix tailTrace_6885605
  have hstable : (prefixWord ++ tailWord_6885605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885605).length < 2 ^ (prefixWord ++ tailWord_6885605).sum := by decide
  have hdescent : baseEnd_6885605 < baseStart_6885605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885608 : List Nat := [2, 1, 4, 1, 2, 2, 3, 8]
def baseStart_6885608 : Nat := 118140960795 + 6885608 * 2 ^ 59
def prefixEnd_6885608 : Nat := 4983230072969 + 3 ^ 40 * 6885608 * 2
def baseEnd_6885608 : Nat := 130949129720133380027173

theorem tailTrace_6885608 : CollatzResearch.WordTrace tailWord_6885608 prefixEnd_6885608 130949129720133380027173 := by
  unfold tailWord_6885608
  simp only [CollatzResearch.WordTrace]
  refine ⟨125569377819312829533948739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167425837092417106045264985 125569377819312829533948739)
  ·
    refine ⟨188354066728969244300923109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125569377819312829533948739 188354066728969244300923109)
    ·
      refine ⟨35316387511681733306423083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188354066728969244300923109 35316387511681733306423083)
      ·
        refine ⟨52974581267522599959634625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35316387511681733306423083 52974581267522599959634625)
        ·
          refine ⟨39730935950641949969725969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52974581267522599959634625 39730935950641949969725969)
          ·
            refine ⟨29798201962981462477294477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39730935950641949969725969 29798201962981462477294477)
            ·
              refine ⟨11174325736118048428985429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29798201962981462477294477 11174325736118048428985429)
              ·
                refine ⟨130949129720133380027173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11174325736118048428985429 130949129720133380027173)
                ·
                  rfl

theorem cell23_6885608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 8].length) (baseStart_6885608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885608 prefixEnd_6885608 := by exact prefixLift 6885608
  have htrace : WordTrace (prefixWord ++ tailWord_6885608) baseStart_6885608 baseEnd_6885608 := by
    simpa [prefixWord, tailWord_6885608, baseEnd_6885608] using wordTrace_append hprefix tailTrace_6885608
  have hstable : (prefixWord ++ tailWord_6885608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885608).length < 2 ^ (prefixWord ++ tailWord_6885608).sum := by decide
  have hdescent : baseEnd_6885608 < baseStart_6885608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885615 : List Nat := [1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 4]
def baseStart_6885615 : Nat := 118140960795 + 6885615 * 2 ^ 59
def prefixEnd_6885615 : Nat := 4983230072969 + 3 ^ 40 * 6885615 * 2
def baseEnd_6885615 : Nat := 3535630096808182733346139

theorem tailTrace_6885615 : CollatzResearch.WordTrace tailWord_6885615 prefixEnd_6885615 3535630096808182733346139 := by
  unfold tailWord_6885615
  simp only [CollatzResearch.WordTrace]
  refine ⟨251139010949600299263402299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167426007299733532842268199 251139010949600299263402299)
  ·
    refine ⟨376708516424400448895103449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251139010949600299263402299 376708516424400448895103449)
    ·
      refine ⟨282531387318300336671327587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376708516424400448895103449 282531387318300336671327587)
      ·
        refine ⟨423797080977450505006991381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282531387318300336671327587 423797080977450505006991381)
        ·
          refine ⟨19865488170817992422202721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 423797080977450505006991381 19865488170817992422202721)
          ·
            refine ⟨14899116128113494316652041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19865488170817992422202721 14899116128113494316652041)
            ·
              refine ⟨11174337096085120737489031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14899116128113494316652041 11174337096085120737489031)
              ·
                refine ⟨16761505644127681106233547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11174337096085120737489031 16761505644127681106233547)
                ·
                  refine ⟨25142258466191521659350321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16761505644127681106233547 25142258466191521659350321)
                  ·
                    refine ⟨18856693849643641244512741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25142258466191521659350321 18856693849643641244512741)
                    ·
                      refine ⟨3535630096808182733346139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18856693849643641244512741 3535630096808182733346139)
                      ·
                        rfl

theorem cell23_6885615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 4].length) (baseStart_6885615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885615 prefixEnd_6885615 := by exact prefixLift 6885615
  have htrace : WordTrace (prefixWord ++ tailWord_6885615) baseStart_6885615 baseEnd_6885615 := by
    simpa [prefixWord, tailWord_6885615, baseEnd_6885615] using wordTrace_append hprefix tailTrace_6885615
  have hstable : (prefixWord ++ tailWord_6885615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885615).length < 2 ^ (prefixWord ++ tailWord_6885615).sum := by decide
  have hdescent : baseEnd_6885615 < baseStart_6885615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885635 : List Nat := [1, 1, 1, 3, 2, 3, 2, 2, 4, 1, 3]
def baseStart_6885635 : Nat := 118140960795 + 6885635 * 2 ^ 59
def prefixEnd_6885635 : Nat := 4983230072969 + 3 ^ 40 * 6885635 * 2
def baseEnd_6885635 : Nat := 3535640366421272655096047

theorem tailTrace_6885635 : CollatzResearch.WordTrace tailWord_6885635 prefixEnd_6885635 3535640366421272655096047 := by
  unfold tailWord_6885635
  simp only [CollatzResearch.WordTrace]
  refine ⟨251139740409527842679130359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167426493606351895119420239 251139740409527842679130359)
  ·
    refine ⟨376709610614291764018695539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251139740409527842679130359 376709610614291764018695539)
    ·
      refine ⟨565064415921437646028043309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376709610614291764018695539 565064415921437646028043309)
      ·
        refine ⟨211899155970539117260516241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 565064415921437646028043309 211899155970539117260516241)
        ·
          refine ⟨158924366977904337945387181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211899155970539117260516241 158924366977904337945387181)
          ·
            refine ⟨59596637616714126729520193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158924366977904337945387181 59596637616714126729520193)
            ·
              refine ⟨44697478212535595047140145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59596637616714126729520193 44697478212535595047140145)
              ·
                refine ⟨33523108659401696285355109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44697478212535595047140145 33523108659401696285355109)
                ·
                  refine ⟨6285582873637818053504083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33523108659401696285355109 6285582873637818053504083)
                  ·
                    refine ⟨9428374310456727080256125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6285582873637818053504083 9428374310456727080256125)
                    ·
                      refine ⟨3535640366421272655096047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9428374310456727080256125 3535640366421272655096047)
                      ·
                        rfl

theorem cell23_6885635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 4, 1, 3].length) (baseStart_6885635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885635 prefixEnd_6885635 := by exact prefixLift 6885635
  have htrace : WordTrace (prefixWord ++ tailWord_6885635) baseStart_6885635 baseEnd_6885635 := by
    simpa [prefixWord, tailWord_6885635, baseEnd_6885635] using wordTrace_append hprefix tailTrace_6885635
  have hstable : (prefixWord ++ tailWord_6885635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885635).length < 2 ^ (prefixWord ++ tailWord_6885635).sum := by decide
  have hdescent : baseEnd_6885635 < baseStart_6885635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885636 : List Nat := [2, 3, 2, 2, 4, 1, 2, 1, 1, 1, 4]
def baseStart_6885636 : Nat := 118140960795 + 6885636 * 2 ^ 59
def prefixEnd_6885636 : Nat := 4983230072969 + 3 ^ 40 * 6885636 * 2
def baseEnd_6885636 : Nat := 3535640879901927151183543

theorem tailTrace_6885636 : CollatzResearch.WordTrace tailWord_6885636 prefixEnd_6885636 3535640879901927151183543 := by
  unfold tailWord_6885636
  simp only [CollatzResearch.WordTrace]
  refine ⟨125569888441262109924958381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167426517921682813233277841 125569888441262109924958381)
  ·
    refine ⟨47088708165473291221859393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125569888441262109924958381 47088708165473291221859393)
    ·
      refine ⟨35316531124104968416394545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47088708165473291221859393 35316531124104968416394545)
      ·
        refine ⟨26487398343078726312295909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35316531124104968416394545 26487398343078726312295909)
        ·
          refine ⟨4966387189327261183555483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26487398343078726312295909 4966387189327261183555483)
          ·
            refine ⟨7449580783990891775333225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4966387189327261183555483 7449580783990891775333225)
            ·
              refine ⟨5587185587993168831499919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7449580783990891775333225 5587185587993168831499919)
              ·
                refine ⟨8380778381989753247249879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5587185587993168831499919 8380778381989753247249879)
                ·
                  refine ⟨12571167572984629870874819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8380778381989753247249879 12571167572984629870874819)
                  ·
                    refine ⟨18856751359476944806312229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12571167572984629870874819 18856751359476944806312229)
                    ·
                      refine ⟨3535640879901927151183543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18856751359476944806312229 3535640879901927151183543)
                      ·
                        rfl

theorem cell23_6885636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_6885636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885636 prefixEnd_6885636 := by exact prefixLift 6885636
  have htrace : WordTrace (prefixWord ++ tailWord_6885636) baseStart_6885636 baseEnd_6885636 := by
    simpa [prefixWord, tailWord_6885636, baseEnd_6885636] using wordTrace_append hprefix tailTrace_6885636
  have hstable : (prefixWord ++ tailWord_6885636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885636).length < 2 ^ (prefixWord ++ tailWord_6885636).sum := by decide
  have hdescent : baseEnd_6885636 < baseStart_6885636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885639 : List Nat := [1, 1, 4, 5, 1, 1, 1, 3, 1, 2, 3]
def baseStart_6885639 : Nat := 118140960795 + 6885639 * 2 ^ 59
def prefixEnd_6885639 : Nat := 4983230072969 + 3 ^ 40 * 6885639 * 2
def baseEnd_6885639 : Nat := 3535642420343890639446029

theorem tailTrace_6885639 : CollatzResearch.WordTrace tailWord_6885639 prefixEnd_6885639 3535642420343890639446029 := by
  unfold tailWord_6885639
  simp only [CollatzResearch.WordTrace]
  refine ⟨251139886301513351362275971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167426590867675567574850647 251139886301513351362275971)
  ·
    refine ⟨376709829452270027043413957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251139886301513351362275971 376709829452270027043413957)
    ·
      refine ⟨70633093022300630070640117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 376709829452270027043413957 70633093022300630070640117)
      ·
        refine ⟨6621852470840684069122511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70633093022300630070640117 6621852470840684069122511)
        ·
          refine ⟨9932778706261026103683767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6621852470840684069122511 9932778706261026103683767)
          ·
            refine ⟨14899168059391539155525651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9932778706261026103683767 14899168059391539155525651)
            ·
              refine ⟨22348752089087308733288477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14899168059391539155525651 22348752089087308733288477)
              ·
                refine ⟨8380782033407740774983179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22348752089087308733288477 8380782033407740774983179)
                ·
                  refine ⟨12571173050111611162474769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8380782033407740774983179 12571173050111611162474769)
                  ·
                    refine ⟨9428379787583708371856077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12571173050111611162474769 9428379787583708371856077)
                    ·
                      refine ⟨3535642420343890639446029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9428379787583708371856077 3535642420343890639446029)
                      ·
                        rfl

theorem cell23_6885639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_6885639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885639 prefixEnd_6885639 := by exact prefixLift 6885639
  have htrace : WordTrace (prefixWord ++ tailWord_6885639) baseStart_6885639 baseEnd_6885639 := by
    simpa [prefixWord, tailWord_6885639, baseEnd_6885639] using wordTrace_append hprefix tailTrace_6885639
  have hstable : (prefixWord ++ tailWord_6885639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885639).length < 2 ^ (prefixWord ++ tailWord_6885639).sum := by decide
  have hdescent : baseEnd_6885639 < baseStart_6885639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885669 : List Nat := [1, 3, 1, 2, 6, 1, 1, 1, 1, 3, 3]
def baseStart_6885669 : Nat := 118140960795 + 6885669 * 2 ^ 59
def prefixEnd_6885669 : Nat := 4983230072969 + 3 ^ 40 * 6885669 * 2
def baseEnd_6885669 : Nat := 3535657824763525522070891

theorem tailTrace_6885669 : CollatzResearch.WordTrace tailWord_6885669 prefixEnd_6885669 3535657824763525522070891 := by
  unfold tailWord_6885669
  simp only [CollatzResearch.WordTrace]
  refine ⟨251140980491404666485868061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167427320327603110990578707 251140980491404666485868061)
  ·
    refine ⟨94177867684276749932200523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251140980491404666485868061 94177867684276749932200523)
    ·
      refine ⟨141266801526415124898300785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94177867684276749932200523 141266801526415124898300785)
      ·
        refine ⟨105950101144811343673725589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141266801526415124898300785 105950101144811343673725589)
        ·
          refine ⟨4966410991163031734705887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 105950101144811343673725589 4966410991163031734705887)
          ·
            refine ⟨7449616486744547602058831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4966410991163031734705887 7449616486744547602058831)
            ·
              refine ⟨11174424730116821403088247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7449616486744547602058831 11174424730116821403088247)
              ·
                refine ⟨16761637095175232104632371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11174424730116821403088247 16761637095175232104632371)
                ·
                  refine ⟨25142455642762848156948557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16761637095175232104632371 25142455642762848156948557)
                  ·
                    refine ⟨9428420866036068058855709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25142455642762848156948557 9428420866036068058855709)
                    ·
                      refine ⟨3535657824763525522070891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9428420866036068058855709 3535657824763525522070891)
                      ·
                        rfl

theorem cell23_6885669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 1, 3, 3].length) (baseStart_6885669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885669 prefixEnd_6885669 := by exact prefixLift 6885669
  have htrace : WordTrace (prefixWord ++ tailWord_6885669) baseStart_6885669 baseEnd_6885669 := by
    simpa [prefixWord, tailWord_6885669, baseEnd_6885669] using wordTrace_append hprefix tailTrace_6885669
  have hstable : (prefixWord ++ tailWord_6885669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885669).length < 2 ^ (prefixWord ++ tailWord_6885669).sum := by decide
  have hdescent : baseEnd_6885669 < baseStart_6885669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885688 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 1, 4, 4]
def baseStart_6885688 : Nat := 118140960795 + 6885688 * 2 ^ 59
def prefixEnd_6885688 : Nat := 4983230072969 + 3 ^ 40 * 6885688 * 2
def baseEnd_6885688 : Nat := 3535667580895960947733303

theorem tailTrace_6885688 : CollatzResearch.WordTrace tailWord_6885688 prefixEnd_6885688 3535667580895960947733303 := by
  unfold tailWord_6885688
  simp only [CollatzResearch.WordTrace]
  refine ⟨125570836739167916365404859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167427782318890555153873145 125570836739167916365404859)
  ·
    refine ⟨188356255108751874548107289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125570836739167916365404859 188356255108751874548107289)
    ·
      refine ⟨141267191331563905911080467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188356255108751874548107289 141267191331563905911080467)
      ·
        refine ⟨211900786997345858866620701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141267191331563905911080467 211900786997345858866620701)
        ·
          refine ⟨79462795124004697074982763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211900786997345858866620701 79462795124004697074982763)
          ·
            refine ⟨119194192686007045612474145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79462795124004697074982763 119194192686007045612474145)
            ·
              refine ⟨89395644514505284209355609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119194192686007045612474145 89395644514505284209355609)
              ·
                refine ⟨67046733385878963157016707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89395644514505284209355609 67046733385878963157016707)
                ·
                  refine ⟨100570100078818444735525061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67046733385878963157016707 100570100078818444735525061)
                  ·
                    refine ⟨18856893764778458387910949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100570100078818444735525061 18856893764778458387910949)
                    ·
                      refine ⟨3535667580895960947733303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18856893764778458387910949 3535667580895960947733303)
                      ·
                        rfl

theorem cell23_6885688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_6885688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885688 prefixEnd_6885688 := by exact prefixLift 6885688
  have htrace : WordTrace (prefixWord ++ tailWord_6885688) baseStart_6885688 baseEnd_6885688 := by
    simpa [prefixWord, tailWord_6885688, baseEnd_6885688] using wordTrace_append hprefix tailTrace_6885688
  have hstable : (prefixWord ++ tailWord_6885688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885688).length < 2 ^ (prefixWord ++ tailWord_6885688).sum := by decide
  have hdescent : baseEnd_6885688 < baseStart_6885688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885692 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 6, 2, 2]
def baseStart_6885692 : Nat := 118140960795 + 6885692 * 2 ^ 59
def prefixEnd_6885692 : Nat := 4983230072969 + 3 ^ 40 * 6885692 * 2
def baseEnd_6885692 : Nat := 3535669634818578932083285

theorem tailTrace_6885692 : CollatzResearch.WordTrace tailWord_6885692 prefixEnd_6885692 3535669634818578932083285 := by
  unfold tailWord_6885692
  simp only [CollatzResearch.WordTrace]
  refine ⟨125570909685160670706977665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167427879580214227609303553 125570909685160670706977665)
  ·
    refine ⟨94178182263870503030233249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125570909685160670706977665 94178182263870503030233249)
    ·
      refine ⟨70633636697902877272674937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94178182263870503030233249 70633636697902877272674937)
      ·
        refine ⟨52975227523427157954506203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70633636697902877272674937 52975227523427157954506203)
        ·
          refine ⟨79462841285140736931759305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52975227523427157954506203 79462841285140736931759305)
          ·
            refine ⟨59597130963855552698819479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79462841285140736931759305 59597130963855552698819479)
            ·
              refine ⟨89395696445783329048229219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59597130963855552698819479 89395696445783329048229219)
              ·
                refine ⟨134093544668674993572343829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89395696445783329048229219 134093544668674993572343829)
                ·
                  refine ⟨6285634906344140323703617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134093544668674993572343829 6285634906344140323703617)
                  ·
                    refine ⟨4714226179758105242777713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6285634906344140323703617 4714226179758105242777713)
                    ·
                      refine ⟨3535669634818578932083285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4714226179758105242777713 3535669634818578932083285)
                      ·
                        rfl

theorem cell23_6885692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_6885692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885692 prefixEnd_6885692 := by exact prefixLift 6885692
  have htrace : WordTrace (prefixWord ++ tailWord_6885692) baseStart_6885692 baseEnd_6885692 := by
    simpa [prefixWord, tailWord_6885692, baseEnd_6885692] using wordTrace_append hprefix tailTrace_6885692
  have hstable : (prefixWord ++ tailWord_6885692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885692).length < 2 ^ (prefixWord ++ tailWord_6885692).sum := by decide
  have hdescent : baseEnd_6885692 < baseStart_6885692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885708 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 1, 2, 7]
def baseStart_6885708 : Nat := 118140960795 + 6885708 * 2 ^ 59
def prefixEnd_6885708 : Nat := 4983230072969 + 3 ^ 40 * 6885708 * 2
def baseEnd_6885708 : Nat := 3535677850509050869483211

theorem tailTrace_6885708 : CollatzResearch.WordTrace tailWord_6885708 prefixEnd_6885708 3535677850509050869483211 := by
  unfold tailWord_6885708
  simp only [CollatzResearch.WordTrace]
  refine ⟨125571201469131688073268889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167428268625508917431025185 125571201469131688073268889)
  ·
    refine ⟨94178401101848766054951667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125571201469131688073268889 94178401101848766054951667)
    ·
      refine ⟨141267601652773149082427501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94178401101848766054951667 141267601652773149082427501)
      ·
        refine ⟨52975350619789930905910313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141267601652773149082427501 52975350619789930905910313)
        ·
          refine ⟨39731512964842448179432735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52975350619789930905910313 39731512964842448179432735)
          ·
            refine ⟨59597269447263672269149103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39731512964842448179432735 59597269447263672269149103)
            ·
              refine ⟨89395904170895508403723655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59597269447263672269149103 89395904170895508403723655)
              ·
                refine ⟨134093856256343262605585483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89395904170895508403723655 134093856256343262605585483)
                ·
                  refine ⟨201140784384514893908378225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134093856256343262605585483 201140784384514893908378225)
                  ·
                    refine ⟨150855588288386170431283669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 201140784384514893908378225 150855588288386170431283669)
                    ·
                      refine ⟨3535677850509050869483211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 150855588288386170431283669 3535677850509050869483211)
                      ·
                        rfl

theorem cell23_6885708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_6885708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885708 prefixEnd_6885708 := by exact prefixLift 6885708
  have htrace : WordTrace (prefixWord ++ tailWord_6885708) baseStart_6885708 baseEnd_6885708 := by
    simpa [prefixWord, tailWord_6885708, baseEnd_6885708] using wordTrace_append hprefix tailTrace_6885708
  have hstable : (prefixWord ++ tailWord_6885708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885708).length < 2 ^ (prefixWord ++ tailWord_6885708).sum := by decide
  have hdescent : baseEnd_6885708 < baseStart_6885708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885785 : List Nat := [1, 2, 1, 2, 1, 4, 2, 2, 1, 4, 3]
def baseStart_6885785 : Nat := 118140960795 + 6885785 * 2 ^ 59
def prefixEnd_6885785 : Nat := 4983230072969 + 3 ^ 40 * 6885785 * 2
def baseEnd_6885785 : Nat := 3535717388519447068220357

theorem tailTrace_6885785 : CollatzResearch.WordTrace tailWord_6885785 prefixEnd_6885785 3535717388519447068220357 := by
  unfold tailWord_6885785
  simp only [CollatzResearch.WordTrace]
  refine ⟨251145211358984418297090809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167430140905989612198060539 251145211358984418297090809)
  ·
    refine ⟨188358908519238313722818107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251145211358984418297090809 188358908519238313722818107)
    ·
      refine ⟨282538362778857470584227161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188358908519238313722818107 282538362778857470584227161)
      ·
        refine ⟨211903772084143102938170371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282538362778857470584227161 211903772084143102938170371)
        ·
          refine ⟨317855658126214654407255557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211903772084143102938170371 317855658126214654407255557)
          ·
            refine ⟨59597935898665247701360417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 317855658126214654407255557 59597935898665247701360417)
            ·
              refine ⟨44698451923998935776020313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59597935898665247701360417 44698451923998935776020313)
              ·
                refine ⟨33523838942999201832015235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44698451923998935776020313 33523838942999201832015235)
                ·
                  refine ⟨50285758414498802748022853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33523838942999201832015235 50285758414498802748022853)
                  ·
                    refine ⟨9428579702718525515254285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50285758414498802748022853 9428579702718525515254285)
                    ·
                      refine ⟨3535717388519447068220357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9428579702718525515254285 3535717388519447068220357)
                      ·
                        rfl

theorem cell23_6885785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 4, 3].length) (baseStart_6885785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885785 prefixEnd_6885785 := by exact prefixLift 6885785
  have htrace : WordTrace (prefixWord ++ tailWord_6885785) baseStart_6885785 baseEnd_6885785 := by
    simpa [prefixWord, tailWord_6885785, baseEnd_6885785] using wordTrace_append hprefix tailTrace_6885785
  have hstable : (prefixWord ++ tailWord_6885785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885785).length < 2 ^ (prefixWord ++ tailWord_6885785).sum := by decide
  have hdescent : baseEnd_6885785 < baseStart_6885785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885792 : List Nat := [2, 1, 1, 4, 1, 4, 1, 2, 3, 4]
def baseStart_6885792 : Nat := 118140960795 + 6885792 * 2 ^ 59
def prefixEnd_6885792 : Nat := 4983230072969 + 3 ^ 40 * 6885792 * 2
def baseEnd_6885792 : Nat := 1178573660961342846944275

theorem tailTrace_6885792 : CollatzResearch.WordTrace tailWord_6885792 prefixEnd_6885792 1178573660961342846944275 := by
  unfold tailWord_6885792
  simp only [CollatzResearch.WordTrace]
  refine ⟨125572733334979529246297815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167430311113306038995063753 125572733334979529246297815)
  ·
    refine ⟨188359100002469293869446723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125572733334979529246297815 188359100002469293869446723)
    ·
      refine ⟨282538650003703940804170085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188359100002469293869446723 282538650003703940804170085)
      ·
        refine ⟨52975996875694488900781891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 282538650003703940804170085 52975996875694488900781891)
        ·
          refine ⟨79463995313541733351172837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52975996875694488900781891 79463995313541733351172837)
          ·
            refine ⟨14899499121289075003344907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79463995313541733351172837 14899499121289075003344907)
            ·
              refine ⟨22349248681933612505017361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14899499121289075003344907 22349248681933612505017361)
              ·
                refine ⟨16761936511450209378763021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22349248681933612505017361 16761936511450209378763021)
                ·
                  refine ⟨6285726191793828517036133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16761936511450209378763021 6285726191793828517036133)
                  ·
                    refine ⟨1178573660961342846944275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6285726191793828517036133 1178573660961342846944275)
                    ·
                      rfl

theorem cell23_6885792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 3, 4].length) (baseStart_6885792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885792 prefixEnd_6885792 := by exact prefixLift 6885792
  have htrace : WordTrace (prefixWord ++ tailWord_6885792) baseStart_6885792 baseEnd_6885792 := by
    simpa [prefixWord, tailWord_6885792, baseEnd_6885792] using wordTrace_append hprefix tailTrace_6885792
  have hstable : (prefixWord ++ tailWord_6885792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885792).length < 2 ^ (prefixWord ++ tailWord_6885792).sum := by decide
  have hdescent : baseEnd_6885792 < baseStart_6885792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885799 : List Nat := [1, 1, 6, 1, 1, 4, 1, 1, 2, 1, 4]
def baseStart_6885799 : Nat := 118140960795 + 6885799 * 2 ^ 59
def prefixEnd_6885799 : Nat := 4983230072969 + 3 ^ 40 * 6885799 * 2
def baseEnd_6885799 : Nat := 3535724577248610013445293

theorem tailTrace_6885799 : CollatzResearch.WordTrace tailWord_6885799 prefixEnd_6885799 3535724577248610013445293 := by
  unfold tailWord_6885799
  simp only [CollatzResearch.WordTrace]
  refine ⟨251145721980933698688100451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167430481320622465792066967 251145721980933698688100451)
  ·
    refine ⟨376718582971400548032150677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251145721980933698688100451 376718582971400548032150677)
    ·
      refine ⟨17658683576784400689007063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 376718582971400548032150677 17658683576784400689007063)
      ·
        refine ⟨26488025365176601033510595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17658683576784400689007063 26488025365176601033510595)
        ·
          refine ⟨39732038047764901550265893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26488025365176601033510595 39732038047764901550265893)
          ·
            refine ⟨7449757133955919040674855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39732038047764901550265893 7449757133955919040674855)
            ·
              refine ⟨11174635700933878561012283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7449757133955919040674855 11174635700933878561012283)
              ·
                refine ⟨16761953551400817841518425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11174635700933878561012283 16761953551400817841518425)
                ·
                  refine ⟨12571465163550613381138819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16761953551400817841518425 12571465163550613381138819)
                  ·
                    refine ⟨18857197745325920071708229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12571465163550613381138819 18857197745325920071708229)
                    ·
                      refine ⟨3535724577248610013445293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18857197745325920071708229 3535724577248610013445293)
                      ·
                        rfl

theorem cell23_6885799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_6885799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885799 prefixEnd_6885799 := by exact prefixLift 6885799
  have htrace : WordTrace (prefixWord ++ tailWord_6885799) baseStart_6885799 baseEnd_6885799 := by
    simpa [prefixWord, tailWord_6885799, baseEnd_6885799] using wordTrace_append hprefix tailTrace_6885799
  have hstable : (prefixWord ++ tailWord_6885799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885799).length < 2 ^ (prefixWord ++ tailWord_6885799).sum := by decide
  have hdescent : baseEnd_6885799 < baseStart_6885799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885809 : List Nat := [1, 2, 2, 4, 1, 2, 1, 5, 1, 4]
def baseStart_6885809 : Nat := 118140960795 + 6885809 * 2 ^ 59
def prefixEnd_6885809 : Nat := 4983230072969 + 3 ^ 40 * 6885809 * 2
def baseEnd_6885809 : Nat := 1178576570685051658106749

theorem tailTrace_6885809 : CollatzResearch.WordTrace tailWord_6885809 prefixEnd_6885809 1178576570685051658106749 := by
  unfold tailWord_6885809
  simp only [CollatzResearch.WordTrace]
  refine ⟨251146086710897470395964481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167430724473931646930642987 251146086710897470395964481)
  ·
    refine ⟨188359565033173102796973361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251146086710897470395964481 188359565033173102796973361)
    ·
      refine ⟨141269673774879827097730021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188359565033173102796973361 141269673774879827097730021)
      ·
        refine ⟨26488063832789967580824379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141269673774879827097730021 26488063832789967580824379)
        ·
          refine ⟨39732095749184951371236569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26488063832789967580824379 39732095749184951371236569)
          ·
            refine ⟨29799071811888713528427427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39732095749184951371236569 29799071811888713528427427)
            ·
              refine ⟨44698607717833070292641141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29799071811888713528427427 44698607717833070292641141)
              ·
                refine ⟨4190494473546850339935107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44698607717833070292641141 4190494473546850339935107)
                ·
                  refine ⟨6285741710320275509902661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4190494473546850339935107 6285741710320275509902661)
                  ·
                    refine ⟨1178576570685051658106749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6285741710320275509902661 1178576570685051658106749)
                    ·
                      rfl

theorem cell23_6885809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 5, 1, 4].length) (baseStart_6885809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885809 prefixEnd_6885809 := by exact prefixLift 6885809
  have htrace : WordTrace (prefixWord ++ tailWord_6885809) baseStart_6885809 baseEnd_6885809 := by
    simpa [prefixWord, tailWord_6885809, baseEnd_6885809] using wordTrace_append hprefix tailTrace_6885809
  have hstable : (prefixWord ++ tailWord_6885809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885809).length < 2 ^ (prefixWord ++ tailWord_6885809).sum := by decide
  have hdescent : baseEnd_6885809 < baseStart_6885809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885822 : List Nat := [4, 2, 1, 1, 1, 1, 5, 2, 6]
def baseStart_6885822 : Nat := 118140960795 + 6885822 * 2 ^ 59
def prefixEnd_6885822 : Nat := 4983230072969 + 3 ^ 40 * 6885822 * 2
def baseEnd_6885822 : Nat := 392859598589295935939743

theorem tailTrace_6885822 : CollatzResearch.WordTrace tailWord_6885822 prefixEnd_6885822 392859598589295935939743 := by
  unfold tailWord_6885822
  simp only [CollatzResearch.WordTrace]
  refine ⟨31393320107481296702023465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167431040573233582410791813 31393320107481296702023465)
  ·
    refine ⟨23544990080610972526517599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31393320107481296702023465 23544990080610972526517599)
    ·
      refine ⟨35317485120916458789776399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23544990080610972526517599 35317485120916458789776399)
      ·
        refine ⟨52976227681374688184664599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35317485120916458789776399 52976227681374688184664599)
        ·
          refine ⟨79464341522062032276996899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52976227681374688184664599 79464341522062032276996899)
          ·
            refine ⟨119196512283093048415495349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79464341522062032276996899 119196512283093048415495349)
            ·
              refine ⟨11174673026539973288952689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119196512283093048415495349 11174673026539973288952689)
              ·
                refine ⟨8381004769904979966714517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11174673026539973288952689 8381004769904979966714517)
                ·
                  refine ⟨392859598589295935939743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8381004769904979966714517 392859598589295935939743)
                  ·
                    rfl

theorem cell23_6885822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_6885822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885822 prefixEnd_6885822 := by exact prefixLift 6885822
  have htrace : WordTrace (prefixWord ++ tailWord_6885822) baseStart_6885822 baseEnd_6885822 := by
    simpa [prefixWord, tailWord_6885822, baseEnd_6885822] using wordTrace_append hprefix tailTrace_6885822
  have hstable : (prefixWord ++ tailWord_6885822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885822).length < 2 ^ (prefixWord ++ tailWord_6885822).sum := by decide
  have hdescent : baseEnd_6885822 < baseStart_6885822 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885869 : List Nat := [1, 5, 1, 3, 1, 1, 2, 3, 1, 5]
def baseStart_6885869 : Nat := 118140960795 + 6885869 * 2 ^ 59
def prefixEnd_6885869 : Nat := 4983230072969 + 3 ^ 40 * 6885869 * 2
def baseEnd_6885869 : Nat := 1178586840298141579856657

theorem tailTrace_6885869 : CollatzResearch.WordTrace tailWord_6885869 prefixEnd_6885869 1178586840298141579856657 := by
  unfold tailWord_6885869
  simp only [CollatzResearch.WordTrace]
  refine ⟨251148275090680100643148661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167432183393786733762099107 251148275090680100643148661)
  ·
    refine ⟨23545150789751259435295187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 251148275090680100643148661 23545150789751259435295187)
    ·
      refine ⟨35317726184626889152942781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23545150789751259435295187 35317726184626889152942781)
      ·
        refine ⟨13244147319235083432353543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35317726184626889152942781 13244147319235083432353543)
        ·
          refine ⟨19866220978852625148530315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13244147319235083432353543 19866220978852625148530315)
          ·
            refine ⟨29799331468278937722795473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19866220978852625148530315 29799331468278937722795473)
            ·
              refine ⟨22349498601209203292096605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29799331468278937722795473 22349498601209203292096605)
              ·
                refine ⟨8381061975453451234536227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22349498601209203292096605 8381061975453451234536227)
                ·
                  refine ⟨12571592963180176851804341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8381061975453451234536227 12571592963180176851804341)
                  ·
                    refine ⟨1178586840298141579856657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12571592963180176851804341 1178586840298141579856657)
                    ·
                      rfl

theorem cell23_6885869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_6885869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885869 prefixEnd_6885869 := by exact prefixLift 6885869
  have htrace : WordTrace (prefixWord ++ tailWord_6885869) baseStart_6885869 baseEnd_6885869 := by
    simpa [prefixWord, tailWord_6885869, baseEnd_6885869] using wordTrace_append hprefix tailTrace_6885869
  have hstable : (prefixWord ++ tailWord_6885869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885869).length < 2 ^ (prefixWord ++ tailWord_6885869).sum := by decide
  have hdescent : baseEnd_6885869 < baseStart_6885869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885872 : List Nat := [2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 4]
def baseStart_6885872 : Nat := 118140960795 + 6885872 * 2 ^ 59
def prefixEnd_6885872 : Nat := 4983230072969 + 3 ^ 40 * 6885872 * 2
def baseEnd_6885872 : Nat := 3535762061336388227832457

theorem tailTrace_6885872 : CollatzResearch.WordTrace tailWord_6885872 prefixEnd_6885872 3535762061336388227832457 := by
  unfold tailWord_6885872
  simp only [CollatzResearch.WordTrace]
  refine ⟨125574192254834616077753935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167432256339779488103671913 125574192254834616077753935)
  ·
    refine ⟨188361288382251924116630903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125574192254834616077753935 188361288382251924116630903)
    ·
      refine ⟨282541932573377886174946355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188361288382251924116630903 282541932573377886174946355)
      ·
        refine ⟨423812898860066829262419533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282541932573377886174946355 423812898860066829262419533)
        ·
          refine ⟨158929837072525060973407325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 423812898860066829262419533 158929837072525060973407325)
          ·
            refine ⟨59598688902196897865027747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158929837072525060973407325 59598688902196897865027747)
            ·
              refine ⟨89398033353295346797541621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59598688902196897865027747 89398033353295346797541621)
              ·
                refine ⟨8381065626871438762269527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89398033353295346797541621 8381065626871438762269527)
                ·
                  refine ⟨12571598440307158143404291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8381065626871438762269527 12571598440307158143404291)
                  ·
                    refine ⟨18857397660460737215106437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12571598440307158143404291 18857397660460737215106437)
                    ·
                      refine ⟨3535762061336388227832457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18857397660460737215106437 3535762061336388227832457)
                      ·
                        rfl

theorem cell23_6885872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 4].length) (baseStart_6885872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885872 prefixEnd_6885872 := by exact prefixLift 6885872
  have htrace : WordTrace (prefixWord ++ tailWord_6885872) baseStart_6885872 baseEnd_6885872 := by
    simpa [prefixWord, tailWord_6885872, baseEnd_6885872] using wordTrace_append hprefix tailTrace_6885872
  have hstable : (prefixWord ++ tailWord_6885872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885872).length < 2 ^ (prefixWord ++ tailWord_6885872).sum := by decide
  have hdescent : baseEnd_6885872 < baseStart_6885872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885885 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 3, 1, 6]
def baseStart_6885885 : Nat := 118140960795 + 6885885 * 2 ^ 59
def prefixEnd_6885885 : Nat := 4983230072969 + 3 ^ 40 * 6885885 * 2
def baseEnd_6885885 : Nat := 3535768736584896676969897

theorem tailTrace_6885885 : CollatzResearch.WordTrace tailWord_6885885 prefixEnd_6885885 3535768736584896676969897 := by
  unfold tailWord_6885885
  simp only [CollatzResearch.WordTrace]
  refine ⟨251148858658622135375731109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167432572439081423583820739 251148858658622135375731109)
  ·
    refine ⟨47090410998491650382949583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251148858658622135375731109 47090410998491650382949583)
    ·
      refine ⟨70635616497737475574424375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47090410998491650382949583 70635616497737475574424375)
      ·
        refine ⟨105953424746606213361636563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70635616497737475574424375 105953424746606213361636563)
        ·
          refine ⟨158930137119909320042454845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105953424746606213361636563 158930137119909320042454845)
          ·
            refine ⟨59598801419965995015920567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158930137119909320042454845 59598801419965995015920567)
            ·
              refine ⟨89398202129948992523880851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59598801419965995015920567 89398202129948992523880851)
              ·
                refine ⟨134097303194923488785821277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89398202129948992523880851 134097303194923488785821277)
                ·
                  refine ⟨50286488698096308294682979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134097303194923488785821277 50286488698096308294682979)
                  ·
                    refine ⟨75429733047144462442024469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50286488698096308294682979 75429733047144462442024469)
                    ·
                      refine ⟨3535768736584896676969897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75429733047144462442024469 3535768736584896676969897)
                      ·
                        rfl

theorem cell23_6885885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_6885885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885885 prefixEnd_6885885 := by exact prefixLift 6885885
  have htrace : WordTrace (prefixWord ++ tailWord_6885885) baseStart_6885885 baseEnd_6885885 := by
    simpa [prefixWord, tailWord_6885885, baseEnd_6885885] using wordTrace_append hprefix tailTrace_6885885
  have hstable : (prefixWord ++ tailWord_6885885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885885).length < 2 ^ (prefixWord ++ tailWord_6885885).sum := by decide
  have hdescent : baseEnd_6885885 < baseStart_6885885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885899 : List Nat := [1, 1, 1, 1, 7, 2, 1, 3, 2, 4]
def baseStart_6885899 : Nat := 118140960795 + 6885899 * 2 ^ 59
def prefixEnd_6885899 : Nat := 4983230072969 + 3 ^ 40 * 6885899 * 2
def baseEnd_6885899 : Nat := 1178591975104686540731611

theorem tailTrace_6885899 : CollatzResearch.WordTrace tailWord_6885899 prefixEnd_6885899 1178591975104686540731611 := by
  unfold tailWord_6885899
  simp only [CollatzResearch.WordTrace]
  refine ⟨251149369280571415766740751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167432912853714277177827167 251149369280571415766740751)
  ·
    refine ⟨376724053920857123650111127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251149369280571415766740751 376724053920857123650111127)
    ·
      refine ⟨565086080881285685475166691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376724053920857123650111127 565086080881285685475166691)
      ·
        refine ⟨847629121321928528212750037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565086080881285685475166691 847629121321928528212750037)
        ·
          refine ⟨19866307530982699879986329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 847629121321928528212750037 19866307530982699879986329)
          ·
            refine ⟨14899730648237024909989747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19866307530982699879986329 14899730648237024909989747)
            ·
              refine ⟨22349595972355537364984621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14899730648237024909989747 22349595972355537364984621)
              ·
                refine ⟨8381098489633326511869233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22349595972355537364984621 8381098489633326511869233)
                ·
                  refine ⟨6285823867224994883901925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8381098489633326511869233 6285823867224994883901925)
                  ·
                    refine ⟨1178591975104686540731611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6285823867224994883901925 1178591975104686540731611)
                    ·
                      rfl

theorem cell23_6885899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 2, 4].length) (baseStart_6885899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885899 prefixEnd_6885899 := by exact prefixLift 6885899
  have htrace : WordTrace (prefixWord ++ tailWord_6885899) baseStart_6885899 baseEnd_6885899 := by
    simpa [prefixWord, tailWord_6885899, baseEnd_6885899] using wordTrace_append hprefix tailTrace_6885899
  have hstable : (prefixWord ++ tailWord_6885899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885899).length < 2 ^ (prefixWord ++ tailWord_6885899).sum := by decide
  have hdescent : baseEnd_6885899 < baseStart_6885899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885902 : List Nat := [4, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6]
def baseStart_6885902 : Nat := 118140960795 + 6885902 * 2 ^ 59
def prefixEnd_6885902 : Nat := 4983230072969 + 3 ^ 40 * 6885902 * 2
def baseEnd_6885902 : Nat := 3535777465756023110457319

theorem tailTrace_6885902 : CollatzResearch.WordTrace tailWord_6885902 prefixEnd_6885902 3535777465756023110457319 := by
  unfold tailWord_6885902
  simp only [CollatzResearch.WordTrace]
  refine ⟨31393684837445068409887495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167432985799707031519399973 31393684837445068409887495)
  ·
    refine ⟨47090527256167602614831243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31393684837445068409887495 47090527256167602614831243)
    ·
      refine ⟨70635790884251403922246865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47090527256167602614831243 70635790884251403922246865)
      ·
        refine ⟨52976843163188552941685149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70635790884251403922246865 52976843163188552941685149)
        ·
          refine ⟨19866316186195707353131931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52976843163188552941685149 19866316186195707353131931)
          ·
            refine ⟨29799474279293561029697897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19866316186195707353131931 29799474279293561029697897)
            ·
              refine ⟨22349605709470170772273423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29799474279293561029697897 22349605709470170772273423)
              ·
                refine ⟨33524408564205256158410135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22349605709470170772273423 33524408564205256158410135)
                ·
                  refine ⟨50286612846307884237615203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33524408564205256158410135 50286612846307884237615203)
                  ·
                    refine ⟨75429919269461826356422805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50286612846307884237615203 75429919269461826356422805)
                    ·
                      refine ⟨3535777465756023110457319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75429919269461826356422805 3535777465756023110457319)
                      ·
                        rfl

theorem cell23_6885902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_6885902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885902 prefixEnd_6885902 := by exact prefixLift 6885902
  have htrace : WordTrace (prefixWord ++ tailWord_6885902) baseStart_6885902 baseEnd_6885902 := by
    simpa [prefixWord, tailWord_6885902, baseEnd_6885902] using wordTrace_append hprefix tailTrace_6885902
  have hstable : (prefixWord ++ tailWord_6885902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885902).length < 2 ^ (prefixWord ++ tailWord_6885902).sum := by decide
  have hdescent : baseEnd_6885902 < baseStart_6885902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885995 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 9]
def baseStart_6885995 : Nat := 118140960795 + 6885995 * 2 ^ 59
def prefixEnd_6885995 : Nat := 4983230072969 + 3 ^ 40 * 6885995 * 2
def baseEnd_6885995 : Nat := 3535825219456891246594391

theorem tailTrace_6885995 : CollatzResearch.WordTrace tailWord_6885995 prefixEnd_6885995 3535825219456891246594391 := by
  unfold tailWord_6885995
  simp only [CollatzResearch.WordTrace]
  refine ⟨251152870688223624162235439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167435247125482416108156959 251152870688223624162235439)
  ·
    refine ⟨376729306032335436243353159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251152870688223624162235439 376729306032335436243353159)
    ·
      refine ⟨565093959048503154365029739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376729306032335436243353159 565093959048503154365029739)
      ·
        refine ⟨847640938572754731547544609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565093959048503154365029739 847640938572754731547544609)
        ·
          refine ⟨635730703929566048660658457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 847640938572754731547544609 635730703929566048660658457)
          ·
            refine ⟨476798027947174536495493843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 635730703929566048660658457 476798027947174536495493843)
            ·
              refine ⟨715197041920761804743240765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476798027947174536495493843 715197041920761804743240765)
              ·
                refine ⟨268198890720285676778715287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 715197041920761804743240765 268198890720285676778715287)
                ·
                  refine ⟨402298336080428515168072931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 268198890720285676778715287 402298336080428515168072931)
                  ·
                    refine ⟨603447504120642772752109397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 402298336080428515168072931 603447504120642772752109397)
                    ·
                      refine ⟨3535825219456891246594391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 603447504120642772752109397 3535825219456891246594391)
                      ·
                        rfl

theorem cell23_6885995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 9].length) (baseStart_6885995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6885995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6885995 prefixEnd_6885995 := by exact prefixLift 6885995
  have htrace : WordTrace (prefixWord ++ tailWord_6885995) baseStart_6885995 baseEnd_6885995 := by
    simpa [prefixWord, tailWord_6885995, baseEnd_6885995] using wordTrace_append hprefix tailTrace_6885995
  have hstable : (prefixWord ++ tailWord_6885995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885995).length < 2 ^ (prefixWord ++ tailWord_6885995).sum := by decide
  have hdescent : baseEnd_6885995 < baseStart_6885995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886013 : List Nat := [1, 4, 1, 1, 5, 2, 1, 1, 1, 4, 2]
def baseStart_6886013 : Nat := 118140960795 + 6886013 * 2 ^ 59
def prefixEnd_6886013 : Nat := 4983230072969 + 3 ^ 40 * 6886013 * 2
def baseEnd_6886013 : Nat := 3535834462108672176169309

theorem tailTrace_6886013 : CollatzResearch.WordTrace tailWord_6886013 prefixEnd_6886013 3535834462108672176169309 := by
  unfold tailWord_6886013
  simp only [CollatzResearch.WordTrace]
  refine ⟨251153527202158413236390693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167435684801438942157593795 251153527202158413236390693)
  ·
    refine ⟨47091286350404702481823255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251153527202158413236390693 47091286350404702481823255)
    ·
      refine ⟨70636929525607053722734883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47091286350404702481823255 70636929525607053722734883)
      ·
        refine ⟨105955394288410580584102325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70636929525607053722734883 105955394288410580584102325)
        ·
          refine ⟨9933318214538491929759593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105955394288410580584102325 9933318214538491929759593)
          ·
            refine ⟨7449988660903868947319695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9933318214538491929759593 7449988660903868947319695)
            ·
              refine ⟨11174982991355803420979543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7449988660903868947319695 11174982991355803420979543)
              ·
                refine ⟨16762474487033705131469315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11174982991355803420979543 16762474487033705131469315)
                ·
                  refine ⟨25143711730550557697203973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16762474487033705131469315 25143711730550557697203973)
                  ·
                    refine ⟨4714445949478229568225745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25143711730550557697203973 4714445949478229568225745)
                    ·
                      refine ⟨3535834462108672176169309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4714445949478229568225745 3535834462108672176169309)
                      ·
                        rfl

theorem cell23_6886013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 4, 2].length) (baseStart_6886013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886013 prefixEnd_6886013 := by exact prefixLift 6886013
  have htrace : WordTrace (prefixWord ++ tailWord_6886013) baseStart_6886013 baseEnd_6886013 := by
    simpa [prefixWord, tailWord_6886013, baseEnd_6886013] using wordTrace_append hprefix tailTrace_6886013
  have hstable : (prefixWord ++ tailWord_6886013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886013).length < 2 ^ (prefixWord ++ tailWord_6886013).sum := by decide
  have hdescent : baseEnd_6886013 < baseStart_6886013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886112 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 6]
def baseStart_6886112 : Nat := 118140960795 + 6886112 * 2 ^ 59
def prefixEnd_6886112 : Nat := 4983230072969 + 3 ^ 40 * 6886112 * 2
def baseEnd_6886112 : Nat := 3535885296693467288831353

theorem tailTrace_6886112 : CollatzResearch.WordTrace tailWord_6886112 prefixEnd_6886112 3535885296693467288831353 := by
  unfold tailWord_6886112
  simp only [CollatzResearch.WordTrace]
  refine ⟨125578569014399876572122295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167438092019199835429496393 125578569014399876572122295)
  ·
    refine ⟨188367853521599814858183443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125578569014399876572122295 188367853521599814858183443)
    ·
      refine ⟨282551780282399722287275165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188367853521599814858183443 282551780282399722287275165)
      ·
        refine ⟨105956917605899895857728187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282551780282399722287275165 105956917605899895857728187)
        ·
          refine ⟨158935376408849843786592281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105956917605899895857728187 158935376408849843786592281)
          ·
            refine ⟨119201532306637382839944211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158935376408849843786592281 119201532306637382839944211)
            ·
              refine ⟨178802298459956074259916317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119201532306637382839944211 178802298459956074259916317)
              ·
                refine ⟨67050861922483527847468619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178802298459956074259916317 67050861922483527847468619)
                ·
                  refine ⟨100576292883725291771202929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67050861922483527847468619 100576292883725291771202929)
                  ·
                    refine ⟨75432219662793968828402197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100576292883725291771202929 75432219662793968828402197)
                    ·
                      refine ⟨3535885296693467288831353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75432219662793968828402197 3535885296693467288831353)
                      ·
                        rfl

theorem cell23_6886112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_6886112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886112 prefixEnd_6886112 := by exact prefixLift 6886112
  have htrace : WordTrace (prefixWord ++ tailWord_6886112) baseStart_6886112 baseEnd_6886112 := by
    simpa [prefixWord, tailWord_6886112, baseEnd_6886112] using wordTrace_append hprefix tailTrace_6886112
  have hstable : (prefixWord ++ tailWord_6886112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886112).length < 2 ^ (prefixWord ++ tailWord_6886112).sum := by decide
  have hdescent : baseEnd_6886112 < baseStart_6886112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886113 : List Nat := [1, 2, 3, 1, 4, 2, 1, 4, 1, 4]
def baseStart_6886113 : Nat := 118140960795 + 6886113 * 2 ^ 59
def prefixEnd_6886113 : Nat := 4983230072969 + 3 ^ 40 * 6886113 * 2
def baseEnd_6886113 : Nat := 1178628603391373928306283

theorem tailTrace_6886113 : CollatzResearch.WordTrace tailWord_6886113 prefixEnd_6886113 1178628603391373928306283 := by
  unfold tailWord_6886113
  simp only [CollatzResearch.WordTrace]
  refine ⟨251157174501796130315030993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167438116334530753543353995 251157174501796130315030993)
  ·
    refine ⟨188367880876347097736273245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251157174501796130315030993 188367880876347097736273245)
    ·
      refine ⟨70637955328630161651102467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188367880876347097736273245 70637955328630161651102467)
      ·
        refine ⟨105956932992945242476653701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70637955328630161651102467 105956932992945242476653701)
        ·
          refine ⟨19866924936177232964372569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105956932992945242476653701 19866924936177232964372569)
          ·
            refine ⟨14900193702132924723279427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19866924936177232964372569 14900193702132924723279427)
            ·
              refine ⟨22350290553199387084919141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14900193702132924723279427 22350290553199387084919141)
              ·
                refine ⟨4190679478724885078422339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22350290553199387084919141 4190679478724885078422339)
                ·
                  refine ⟨6286019218087327617633509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4190679478724885078422339 6286019218087327617633509)
                  ·
                    refine ⟨1178628603391373928306283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6286019218087327617633509 1178628603391373928306283)
                    ·
                      rfl

theorem cell23_6886113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_6886113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886113 prefixEnd_6886113 := by exact prefixLift 6886113
  have htrace : WordTrace (prefixWord ++ tailWord_6886113) baseStart_6886113 baseEnd_6886113 := by
    simpa [prefixWord, tailWord_6886113, baseEnd_6886113] using wordTrace_append hprefix tailTrace_6886113
  have hstable : (prefixWord ++ tailWord_6886113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886113).length < 2 ^ (prefixWord ++ tailWord_6886113).sum := by decide
  have hdescent : baseEnd_6886113 < baseStart_6886113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886136 : List Nat := [2, 1, 2, 1, 1, 2, 5, 2, 3, 1, 3]
def baseStart_6886136 : Nat := 118140960795 + 6886136 * 2 ^ 59
def prefixEnd_6886136 : Nat := 4983230072969 + 3 ^ 40 * 6886136 * 2
def baseEnd_6886136 : Nat := 3535897620229175194931243

theorem tailTrace_6886136 : CollatzResearch.WordTrace tailWord_6886136 prefixEnd_6886136 3535897620229175194931243 := by
  unfold tailWord_6886136
  simp only [CollatzResearch.WordTrace]
  refine ⟨125579006690356402621559131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167438675587141870162078841 125579006690356402621559131)
  ·
    refine ⟨188368510035534603932338697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125579006690356402621559131 188368510035534603932338697)
    ·
      refine ⟨141276382526650952949254023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188368510035534603932338697 141276382526650952949254023)
      ·
        refine ⟨211914573789976429423881035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141276382526650952949254023 211914573789976429423881035)
        ·
          refine ⟨317871860684964644135821553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211914573789976429423881035 317871860684964644135821553)
          ·
            refine ⟨238403895513723483101866165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317871860684964644135821553 238403895513723483101866165)
            ·
              refine ⟨22350365204411576540799953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 238403895513723483101866165 22350365204411576540799953)
              ·
                refine ⟨16762773903308682405599965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22350365204411576540799953 16762773903308682405599965)
                ·
                  refine ⟨6286040213740755902099987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16762773903308682405599965 6286040213740755902099987)
                  ·
                    refine ⟨9429060320611133853149981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6286040213740755902099987 9429060320611133853149981)
                    ·
                      refine ⟨3535897620229175194931243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9429060320611133853149981 3535897620229175194931243)
                      ·
                        rfl

theorem cell23_6886136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 3, 1, 3].length) (baseStart_6886136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886136 prefixEnd_6886136 := by exact prefixLift 6886136
  have htrace : WordTrace (prefixWord ++ tailWord_6886136) baseStart_6886136 baseEnd_6886136 := by
    simpa [prefixWord, tailWord_6886136, baseEnd_6886136] using wordTrace_append hprefix tailTrace_6886136
  have hstable : (prefixWord ++ tailWord_6886136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886136).length < 2 ^ (prefixWord ++ tailWord_6886136).sum := by decide
  have hdescent : baseEnd_6886136 < baseStart_6886136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886153 : List Nat := [1, 2, 1, 1, 3, 2, 3, 5, 1, 1, 3]
def baseStart_6886153 : Nat := 118140960795 + 6886153 * 2 ^ 59
def prefixEnd_6886153 : Nat := 4983230072969 + 3 ^ 40 * 6886153 * 2
def baseEnd_6886153 : Nat := 3535906349400301628418665

theorem tailTrace_6886153 : CollatzResearch.WordTrace tailWord_6886153 prefixEnd_6886153 3535906349400301628418665 := by
  unfold tailWord_6886153
  simp only [CollatzResearch.WordTrace]
  refine ⟨251158633421651217146487113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167439088947767478097658075 251158633421651217146487113)
  ·
    refine ⟨188368975066238412859865335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251158633421651217146487113 188368975066238412859865335)
    ·
      refine ⟨282553462599357619289798003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188368975066238412859865335 282553462599357619289798003)
      ·
        refine ⟨423830193899036428934697005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282553462599357619289798003 423830193899036428934697005)
        ·
          refine ⟨158936322712138660850511377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 423830193899036428934697005 158936322712138660850511377)
          ·
            refine ⟨119202242034103995637883533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158936322712138660850511377 119202242034103995637883533)
            ·
              refine ⟨44700840762788998364206325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119202242034103995637883533 44700840762788998364206325)
              ·
                refine ⟨4190703821511468596644343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44700840762788998364206325 4190703821511468596644343)
                ·
                  refine ⟨6286055732267202894966515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4190703821511468596644343 6286055732267202894966515)
                  ·
                    refine ⟨9429083598400804342449773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6286055732267202894966515 9429083598400804342449773)
                    ·
                      refine ⟨3535906349400301628418665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9429083598400804342449773 3535906349400301628418665)
                      ·
                        rfl

theorem cell23_6886153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 5, 1, 1, 3].length) (baseStart_6886153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886153 prefixEnd_6886153 := by exact prefixLift 6886153
  have htrace : WordTrace (prefixWord ++ tailWord_6886153) baseStart_6886153 baseEnd_6886153 := by
    simpa [prefixWord, tailWord_6886153, baseEnd_6886153] using wordTrace_append hprefix tailTrace_6886153
  have hstable : (prefixWord ++ tailWord_6886153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886153).length < 2 ^ (prefixWord ++ tailWord_6886153).sum := by decide
  have hdescent : baseEnd_6886153 < baseStart_6886153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886193 : List Nat := [1, 2, 2, 3, 2, 1, 1, 4, 3, 2, 2]
def baseStart_6886193 : Nat := 118140960795 + 6886193 * 2 ^ 59
def prefixEnd_6886193 : Nat := 4983230072969 + 3 ^ 40 * 6886193 * 2
def baseEnd_6886193 : Nat := 3535926888626481471918481

theorem tailTrace_6886193 : CollatzResearch.WordTrace tailWord_6886193 prefixEnd_6886193 3535926888626481471918481 := by
  unfold tailWord_6886193
  simp only [CollatzResearch.WordTrace]
  refine ⟨251160092341506303977943233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167440061561004202651962155 251160092341506303977943233)
  ·
    refine ⟨188370069256129727983457425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251160092341506303977943233 188370069256129727983457425)
    ·
      refine ⟨141277551942097295987593069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188370069256129727983457425 141277551942097295987593069)
      ·
        refine ⟨52979081978286485995347401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141277551942097295987593069 52979081978286485995347401)
        ·
          refine ⟨39734311483714864496510551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52979081978286485995347401 39734311483714864496510551)
          ·
            refine ⟨59601467225572296744765827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39734311483714864496510551 59601467225572296744765827)
            ·
              refine ⟨89402200838358445117148741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59601467225572296744765827 89402200838358445117148741)
              ·
                refine ⟨16762912657192208459465389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89402200838358445117148741 16762912657192208459465389)
                ·
                  refine ⟨6286092246447078172299521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16762912657192208459465389 6286092246447078172299521)
                  ·
                    refine ⟨4714569184835308629224641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6286092246447078172299521 4714569184835308629224641)
                    ·
                      refine ⟨3535926888626481471918481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4714569184835308629224641 3535926888626481471918481)
                      ·
                        rfl

theorem cell23_6886193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_6886193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886193 prefixEnd_6886193 := by exact prefixLift 6886193
  have htrace : WordTrace (prefixWord ++ tailWord_6886193) baseStart_6886193 baseEnd_6886193 := by
    simpa [prefixWord, tailWord_6886193, baseEnd_6886193] using wordTrace_append hprefix tailTrace_6886193
  have hstable : (prefixWord ++ tailWord_6886193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886193).length < 2 ^ (prefixWord ++ tailWord_6886193).sum := by decide
  have hdescent : baseEnd_6886193 < baseStart_6886193 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886229 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 2, 7]
def baseStart_6886229 : Nat := 118140960795 + 6886229 * 2 ^ 59
def prefixEnd_6886229 : Nat := 4983230072969 + 3 ^ 40 * 6886229 * 2
def baseEnd_6886229 : Nat := 1178648457976681110356105

theorem tailTrace_6886229 : CollatzResearch.WordTrace tailWord_6886229 prefixEnd_6886229 1178648457976681110356105 := by
  unfold tailWord_6886229
  simp only [CollatzResearch.WordTrace]
  refine ⟨251161405369375882126253741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167440936912917254750835827 251161405369375882126253741)
  ·
    refine ⟨94185527013515955797345153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251161405369375882126253741 94185527013515955797345153)
    ·
      refine ⟨70639145260136966848008865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94185527013515955797345153 70639145260136966848008865)
      ·
        refine ⟨52979358945102725136006649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70639145260136966848008865 52979358945102725136006649)
        ·
          refine ⟨39734519208827043852004987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52979358945102725136006649 39734519208827043852004987)
          ·
            refine ⟨59601778813240565778007481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39734519208827043852004987 59601778813240565778007481)
            ·
              refine ⟨44701334109930424333505611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59601778813240565778007481 44701334109930424333505611)
              ·
                refine ⟨67052001164895636500258417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44701334109930424333505611 67052001164895636500258417)
                ·
                  refine ⟨50289000873671727375193813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67052001164895636500258417 50289000873671727375193813)
                  ·
                    refine ⟨1178648457976681110356105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50289000873671727375193813 1178648457976681110356105)
                    ·
                      rfl

theorem cell23_6886229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_6886229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886229 prefixEnd_6886229 := by exact prefixLift 6886229
  have htrace : WordTrace (prefixWord ++ tailWord_6886229) baseStart_6886229 baseEnd_6886229 := by
    simpa [prefixWord, tailWord_6886229, baseEnd_6886229] using wordTrace_append hprefix tailTrace_6886229
  have hstable : (prefixWord ++ tailWord_6886229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886229).length < 2 ^ (prefixWord ++ tailWord_6886229).sum := by decide
  have hdescent : baseEnd_6886229 < baseStart_6886229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886283 : List Nat := [1, 1, 1, 1, 4, 2, 2, 3, 4, 2, 2]
def baseStart_6886283 : Nat := 118140960795 + 6886283 * 2 ^ 59
def prefixEnd_6886283 : Nat := 4983230072969 + 3 ^ 40 * 6886283 * 2
def baseEnd_6886283 : Nat := 3535973101885386119793067

theorem tailTrace_6886283 : CollatzResearch.WordTrace tailWord_6886283 prefixEnd_6886283 3535973101885386119793067 := by
  unfold tailWord_6886283
  simp only [CollatzResearch.WordTrace]
  refine ⟨251163374911180249348719503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167442249940786832899146335 251163374911180249348719503)
  ·
    refine ⟨376745062366770374023079255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251163374911180249348719503 376745062366770374023079255)
    ·
      refine ⟨565117593550155561034618883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376745062366770374023079255 565117593550155561034618883)
      ·
        refine ⟨847676390325233341551928325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565117593550155561034618883 847676390325233341551928325)
        ·
          refine ⟨158939323185981251540986561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 847676390325233341551928325 158939323185981251540986561)
          ·
            refine ⟨119204492389485938655739921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158939323185981251540986561 119204492389485938655739921)
            ·
              refine ⟨89403369292114453991804941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119204492389485938655739921 89403369292114453991804941)
              ·
                refine ⟨33526263484542920246926853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89403369292114453991804941 33526263484542920246926853)
                ·
                  refine ⟨6286174403351797546298785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33526263484542920246926853 6286174403351797546298785)
                  ·
                    refine ⟨4714630802513848159724089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6286174403351797546298785 4714630802513848159724089)
                    ·
                      refine ⟨3535973101885386119793067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4714630802513848159724089 3535973101885386119793067)
                      ·
                        rfl

theorem cell23_6886283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 4, 2, 2].length) (baseStart_6886283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886283 prefixEnd_6886283 := by exact prefixLift 6886283
  have htrace : WordTrace (prefixWord ++ tailWord_6886283) baseStart_6886283 baseEnd_6886283 := by
    simpa [prefixWord, tailWord_6886283, baseEnd_6886283] using wordTrace_append hprefix tailTrace_6886283
  have hstable : (prefixWord ++ tailWord_6886283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886283).length < 2 ^ (prefixWord ++ tailWord_6886283).sum := by decide
  have hdescent : baseEnd_6886283 < baseStart_6886283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886289 : List Nat := [1, 2, 2, 1, 1, 1, 3, 5, 7]
def baseStart_6886289 : Nat := 118140960795 + 6886289 * 2 ^ 59
def prefixEnd_6886289 : Nat := 4983230072969 + 3 ^ 40 * 6886289 * 2
def baseEnd_6886289 : Nat := 392886242529923677368671

theorem tailTrace_6886289 : CollatzResearch.WordTrace tailWord_6886289 prefixEnd_6886289 392886242529923677368671 := by
  unfold tailWord_6886289
  simp only [CollatzResearch.WordTrace]
  refine ⟨251163593749158512373437921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167442395832772341582291947 251163593749158512373437921)
  ·
    refine ⟨188372695311868884280078441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251163593749158512373437921 188372695311868884280078441)
    ·
      refine ⟨141279521483901663210058831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188372695311868884280078441 141279521483901663210058831)
      ·
        refine ⟨211919282225852494815088247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141279521483901663210058831 211919282225852494815088247)
        ·
          refine ⟨317878923338778742222632371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211919282225852494815088247 317878923338778742222632371)
          ·
            refine ⟨476818385008168113333948557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317878923338778742222632371 476818385008168113333948557)
            ·
              refine ⟨178806894378063042500230709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 476818385008168113333948557 178806894378063042500230709)
              ·
                refine ⟨16763146347943410234396629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 178806894378063042500230709 16763146347943410234396629)
                ·
                  refine ⟨392886242529923677368671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16763146347943410234396629 392886242529923677368671)
                  ·
                    rfl

theorem cell23_6886289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 7].length) (baseStart_6886289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886289 prefixEnd_6886289 := by exact prefixLift 6886289
  have htrace : WordTrace (prefixWord ++ tailWord_6886289) baseStart_6886289 baseEnd_6886289 := by
    simpa [prefixWord, tailWord_6886289, baseEnd_6886289] using wordTrace_append hprefix tailTrace_6886289
  have hstable : (prefixWord ++ tailWord_6886289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886289).length < 2 ^ (prefixWord ++ tailWord_6886289).sum := by decide
  have hdescent : baseEnd_6886289 < baseStart_6886289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886294 : List Nat := [5, 3, 1, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_6886294 : Nat := 118140960795 + 6886294 * 2 ^ 59
def prefixEnd_6886294 : Nat := 4983230072969 + 3 ^ 40 * 6886294 * 2
def baseEnd_6886294 : Nat := 3535978750172585576755517

theorem tailTrace_6886294 : CollatzResearch.WordTrace tailWord_6886294 prefixEnd_6886294 3535978750172585576755517 := by
  unfold tailWord_6886294
  simp only [CollatzResearch.WordTrace]
  refine ⟨15697736007133774889210621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167442517409426932151579957 15697736007133774889210621)
  ·
    refine ⟨5886651002675165583453983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15697736007133774889210621 5886651002675165583453983)
    ·
      refine ⟨8829976504012748375180975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5886651002675165583453983 8829976504012748375180975)
      ·
        refine ⟨13244964756019122562771463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8829976504012748375180975 13244964756019122562771463)
        ·
          refine ⟨19867447134028683844157195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13244964756019122562771463 19867447134028683844157195)
          ·
            refine ⟨29801170701043025766235793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19867447134028683844157195 29801170701043025766235793)
            ·
              refine ⟨22350878025782269324676845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29801170701043025766235793 22350878025782269324676845)
              ·
                refine ⟨8381579259668350996753817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22350878025782269324676845 8381579259668350996753817)
                ·
                  refine ⟨6286184444751263247565363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8381579259668350996753817 6286184444751263247565363)
                  ·
                    refine ⟨9429276667126894871348045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6286184444751263247565363 9429276667126894871348045)
                    ·
                      refine ⟨3535978750172585576755517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9429276667126894871348045 3535978750172585576755517)
                      ·
                        rfl

theorem cell23_6886294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_6886294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886294 prefixEnd_6886294 := by exact prefixLift 6886294
  have htrace : WordTrace (prefixWord ++ tailWord_6886294) baseStart_6886294 baseEnd_6886294 := by
    simpa [prefixWord, tailWord_6886294, baseEnd_6886294] using wordTrace_append hprefix tailTrace_6886294
  have hstable : (prefixWord ++ tailWord_6886294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886294).length < 2 ^ (prefixWord ++ tailWord_6886294).sum := by decide
  have hdescent : baseEnd_6886294 < baseStart_6886294 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886306 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 9]
def baseStart_6886306 : Nat := 118140960795 + 6886306 * 2 ^ 59
def prefixEnd_6886306 : Nat := 4983230072969 + 3 ^ 40 * 6886306 * 2
def baseEnd_6886306 : Nat := 392887212437826614422829

theorem tailTrace_6886306 : CollatzResearch.WordTrace tailWord_6886306 prefixEnd_6886306 392887212437826614422829 := by
  unfold tailWord_6886306
  simp only [CollatzResearch.WordTrace]
  refine ⟨62791053447524231069201693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167442809193397949517871181 62791053447524231069201693)
  ·
    refine ⟨23546645042821586650950635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62791053447524231069201693 23546645042821586650950635)
    ·
      refine ⟨35319967564232379976425953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23546645042821586650950635 35319967564232379976425953)
      ·
        refine ⟨26489975673174284982319465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35319967564232379976425953 26489975673174284982319465)
        ·
          refine ⟨19867481754880713736739599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26489975673174284982319465 19867481754880713736739599)
          ·
            refine ⟨29801222632321070605109399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19867481754880713736739599 29801222632321070605109399)
            ·
              refine ⟨44701833948481605907664099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29801222632321070605109399 44701833948481605907664099)
              ·
                refine ⟨67052750922722408861496149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44701833948481605907664099 67052750922722408861496149)
                ·
                  refine ⟨392887212437826614422829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67052750922722408861496149 392887212437826614422829)
                  ·
                    rfl

theorem cell23_6886306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_6886306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886306 prefixEnd_6886306 := by exact prefixLift 6886306
  have htrace : WordTrace (prefixWord ++ tailWord_6886306) baseStart_6886306 baseEnd_6886306 := by
    simpa [prefixWord, tailWord_6886306, baseEnd_6886306] using wordTrace_append hprefix tailTrace_6886306
  have hstable : (prefixWord ++ tailWord_6886306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886306).length < 2 ^ (prefixWord ++ tailWord_6886306).sum := by decide
  have hdescent : baseEnd_6886306 < baseStart_6886306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886340 : List Nat := [2, 3, 3, 3, 1, 1, 2, 1, 7]
def baseStart_6886340 : Nat := 118140960795 + 6886340 * 2 ^ 59
def prefixEnd_6886340 : Nat := 4983230072969 + 3 ^ 40 * 6886340 * 2
def baseEnd_6886340 : Nat := 392889152253632488531145

theorem tailTrace_6886340 : CollatzResearch.WordTrace tailWord_6886340 prefixEnd_6886340 392889152253632488531145 := by
  unfold tailWord_6886340
  simp only [CollatzResearch.WordTrace]
  refine ⟨125582726935986874041772237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167443635914649165389029649 125582726935986874041772237)
  ·
    refine ⟨47093522600995077765664589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125582726935986874041772237 47093522600995077765664589)
    ·
      refine ⟨17660070975373154162124221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47093522600995077765664589 17660070975373154162124221)
      ·
        refine ⟨6622526615764932810796583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17660070975373154162124221 6622526615764932810796583)
        ·
          refine ⟨9933789923647399216194875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6622526615764932810796583 9933789923647399216194875)
          ·
            refine ⟨14900684885471098824292313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9933789923647399216194875 14900684885471098824292313)
            ·
              refine ⟨11175513664103324118219235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14900684885471098824292313 11175513664103324118219235)
              ·
                refine ⟨16763270496154986177328853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11175513664103324118219235 16763270496154986177328853)
                ·
                  refine ⟨392889152253632488531145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16763270496154986177328853 392889152253632488531145)
                  ·
                    rfl

theorem cell23_6886340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 7].length) (baseStart_6886340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886340 prefixEnd_6886340 := by exact prefixLift 6886340
  have htrace : WordTrace (prefixWord ++ tailWord_6886340) baseStart_6886340 baseEnd_6886340 := by
    simpa [prefixWord, tailWord_6886340, baseEnd_6886340] using wordTrace_append hprefix tailTrace_6886340
  have hstable : (prefixWord ++ tailWord_6886340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886340).length < 2 ^ (prefixWord ++ tailWord_6886340).sum := by decide
  have hdescent : baseEnd_6886340 < baseStart_6886340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886390 : List Nat := [5, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4]
def baseStart_6886390 : Nat := 118140960795 + 6886390 * 2 ^ 59
def prefixEnd_6886390 : Nat := 4983230072969 + 3 ^ 40 * 6886390 * 2
def baseEnd_6886390 : Nat := 3536028044315417201155075

theorem tailTrace_6886390 : CollatzResearch.WordTrace tailWord_6886390 prefixEnd_6886390 3536028044315417201155075 := by
  unfold tailWord_6886390
  simp only [CollatzResearch.WordTrace]
  refine ⟨15697954845112037913929039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167444851681195071081909749 15697954845112037913929039)
  ·
    refine ⟨23546932267668056870893559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15697954845112037913929039 23546932267668056870893559)
    ·
      refine ⟨35320398401502085306340339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23546932267668056870893559 35320398401502085306340339)
      ·
        refine ⟨52980597602253127959510509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35320398401502085306340339 52980597602253127959510509)
        ·
          refine ⟨19867724100844922984816441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52980597602253127959510509 19867724100844922984816441)
          ·
            refine ⟨14900793075633692238612331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19867724100844922984816441 14900793075633692238612331)
            ·
              refine ⟨22351189613450538357918497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14900793075633692238612331 22351189613450538357918497)
              ·
                refine ⟨16763392210087903768438873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22351189613450538357918497 16763392210087903768438873)
                ·
                  refine ⟨12572544157565927826329155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16763392210087903768438873 12572544157565927826329155)
                  ·
                    refine ⟨18858816236348891739493733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12572544157565927826329155 18858816236348891739493733)
                    ·
                      refine ⟨3536028044315417201155075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18858816236348891739493733 3536028044315417201155075)
                      ·
                        rfl

theorem cell23_6886390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_6886390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886390 prefixEnd_6886390 := by exact prefixLift 6886390
  have htrace : WordTrace (prefixWord ++ tailWord_6886390) baseStart_6886390 baseEnd_6886390 := by
    simpa [prefixWord, tailWord_6886390, baseEnd_6886390] using wordTrace_append hprefix tailTrace_6886390
  have hstable : (prefixWord ++ tailWord_6886390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886390).length < 2 ^ (prefixWord ++ tailWord_6886390).sum := by decide
  have hdescent : baseEnd_6886390 < baseStart_6886390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886393 : List Nat := [1, 2, 1, 3, 1, 3, 3, 2, 2, 2, 3]
def baseStart_6886393 : Nat := 118140960795 + 6886393 * 2 ^ 59
def prefixEnd_6886393 : Nat := 4983230072969 + 3 ^ 40 * 6886393 * 2
def baseEnd_6886393 : Nat := 3536029584757380689417561

theorem tailTrace_6886393 : CollatzResearch.WordTrace tailWord_6886393 prefixEnd_6886393 3536029584757380689417561 := by
  unfold tailWord_6886393
  simp only [CollatzResearch.WordTrace]
  refine ⟨251167386940781738135223833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167444924627187825423482555 251167386940781738135223833)
  ·
    refine ⟨188375540205586303601417875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251167386940781738135223833 188375540205586303601417875)
    ·
      refine ⟨282563310308379455402126813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188375540205586303601417875 282563310308379455402126813)
      ·
        refine ⟨105961241365642295775797555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282563310308379455402126813 105961241365642295775797555)
        ·
          refine ⟨158941862048463443663696333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105961241365642295775797555 158941862048463443663696333)
          ·
            refine ⟨59603198268173791373886125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158941862048463443663696333 59603198268173791373886125)
            ·
              refine ⟨22351199350565171765207297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59603198268173791373886125 22351199350565171765207297)
              ·
                refine ⟨16763399512923878823905473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22351199350565171765207297 16763399512923878823905473)
                ·
                  refine ⟨12572549634692909117929105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16763399512923878823905473 12572549634692909117929105)
                  ·
                    refine ⟨9429412226019681838446829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12572549634692909117929105 9429412226019681838446829)
                    ·
                      refine ⟨3536029584757380689417561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9429412226019681838446829 3536029584757380689417561)
                      ·
                        rfl

theorem cell23_6886393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_6886393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886393 prefixEnd_6886393 := by exact prefixLift 6886393
  have htrace : WordTrace (prefixWord ++ tailWord_6886393) baseStart_6886393 baseEnd_6886393 := by
    simpa [prefixWord, tailWord_6886393, baseEnd_6886393] using wordTrace_append hprefix tailTrace_6886393
  have hstable : (prefixWord ++ tailWord_6886393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886393).length < 2 ^ (prefixWord ++ tailWord_6886393).sum := by decide
  have hdescent : baseEnd_6886393 < baseStart_6886393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886396 : List Nat := [2, 2, 2, 1, 2, 3, 2, 1, 8]
def baseStart_6886396 : Nat := 118140960795 + 6886396 * 2 ^ 59
def prefixEnd_6886396 : Nat := 4983230072969 + 3 ^ 40 * 6886396 * 2
def baseEnd_6886396 : Nat := 392892347244371575297783

theorem tailTrace_6886396 : CollatzResearch.WordTrace tailWord_6886396 prefixEnd_6886396 392892347244371575297783 := by
  unfold tailWord_6886396
  simp only [CollatzResearch.WordTrace]
  refine ⟨125583748179885434823791521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167444997573180579765055361 125583748179885434823791521)
  ·
    refine ⟨94187811134914076117843641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125583748179885434823791521 94187811134914076117843641)
    ·
      refine ⟨70640858351185557088382731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94187811134914076117843641 70640858351185557088382731)
      ·
        refine ⟨105961287526778335632574097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70640858351185557088382731 105961287526778335632574097)
        ·
          refine ⟨79470965645083751724430573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105961287526778335632574097 79470965645083751724430573)
          ·
            refine ⟨29801612116906406896661465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79470965645083751724430573 29801612116906406896661465)
            ·
              refine ⟨22351209087679805172496099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29801612116906406896661465 22351209087679805172496099)
              ·
                refine ⟨33526813631519707758744149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22351209087679805172496099 33526813631519707758744149)
                ·
                  refine ⟨392892347244371575297783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33526813631519707758744149 392892347244371575297783)
                  ·
                    rfl

theorem cell23_6886396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 8].length) (baseStart_6886396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886396 prefixEnd_6886396 := by exact prefixLift 6886396
  have htrace : WordTrace (prefixWord ++ tailWord_6886396) baseStart_6886396 baseEnd_6886396 := by
    simpa [prefixWord, tailWord_6886396, baseEnd_6886396] using wordTrace_append hprefix tailTrace_6886396
  have hstable : (prefixWord ++ tailWord_6886396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886396).length < 2 ^ (prefixWord ++ tailWord_6886396).sum := by decide
  have hdescent : baseEnd_6886396 < baseStart_6886396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886450 : List Nat := [3, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2]
def baseStart_6886450 : Nat := 118140960795 + 6886450 * 2 ^ 59
def prefixEnd_6886450 : Nat := 4983230072969 + 3 ^ 40 * 6886450 * 2
def baseEnd_6886450 : Nat := 3536058853154686966404799

theorem tailTrace_6886450 : CollatzResearch.WordTrace tailWord_6886450 prefixEnd_6886450 3536058853154686966404799 := by
  unfold tailWord_6886450
  simp only [CollatzResearch.WordTrace]
  refine ⟨62792366475393809217512201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167446310601050157913365869 62792366475393809217512201)
  ·
    refine ⟨47094274856545356913134151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62792366475393809217512201 47094274856545356913134151)
    ·
      refine ⟨70641412284818035369701227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47094274856545356913134151 70641412284818035369701227)
      ·
        refine ⟨105962118427227053054551841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70641412284818035369701227 105962118427227053054551841)
        ·
          refine ⟨79471588820420289790913881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105962118427227053054551841 79471588820420289790913881)
          ·
            refine ⟨59603691615315217343185411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79471588820420289790913881 59603691615315217343185411)
            ·
              refine ⟨89405537422972826014778117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59603691615315217343185411 89405537422972826014778117)
              ·
                refine ⟨16763538266807404877770897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89405537422972826014778117 16763538266807404877770897)
                ·
                  refine ⟨12572653700105553658328173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16763538266807404877770897 12572653700105553658328173)
                  ·
                    refine ⟨4714745137539582621873065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12572653700105553658328173 4714745137539582621873065)
                    ·
                      refine ⟨3536058853154686966404799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4714745137539582621873065 3536058853154686966404799)
                      ·
                        rfl

theorem cell23_6886450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2].length) (baseStart_6886450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886450 prefixEnd_6886450 := by exact prefixLift 6886450
  have htrace : WordTrace (prefixWord ++ tailWord_6886450) baseStart_6886450 baseEnd_6886450 := by
    simpa [prefixWord, tailWord_6886450, baseEnd_6886450] using wordTrace_append hprefix tailTrace_6886450
  have hstable : (prefixWord ++ tailWord_6886450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886450).length < 2 ^ (prefixWord ++ tailWord_6886450).sum := by decide
  have hdescent : baseEnd_6886450 < baseStart_6886450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886463 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 2, 6, 2]
def baseStart_6886463 : Nat := 118140960795 + 6886463 * 2 ^ 59
def prefixEnd_6886463 : Nat := 4983230072969 + 3 ^ 40 * 6886463 * 2
def baseEnd_6886463 : Nat := 3536065528403195415542239

theorem tailTrace_6886463 : CollatzResearch.WordTrace tailWord_6886463 prefixEnd_6886463 3536065528403195415542239 := by
  unfold tailWord_6886463
  simp only [CollatzResearch.WordTrace]
  refine ⟨251169940050528140090272043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167446626700352093393514695 251169940050528140090272043)
  ·
    refine ⟨376754910075792210135408065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251169940050528140090272043 376754910075792210135408065)
    ·
      refine ⟨282566182556844157601556049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376754910075792210135408065 282566182556844157601556049)
      ·
        refine ⟨211924636917633118201167037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282566182556844157601556049 211924636917633118201167037)
        ·
          refine ⟨79471738844112419325437639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211924636917633118201167037 79471738844112419325437639)
          ·
            refine ⟨119207608266168628988156459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79471738844112419325437639 119207608266168628988156459)
            ·
              refine ⟨178811412399252943482234689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119207608266168628988156459 178811412399252943482234689)
              ·
                refine ⟨134108559299439707611676017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178811412399252943482234689 134108559299439707611676017)
                ·
                  refine ⟨100581419474579780708757013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134108559299439707611676017 100581419474579780708757013)
                  ·
                    refine ⟨4714754037870927220722985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100581419474579780708757013 4714754037870927220722985)
                    ·
                      refine ⟨3536065528403195415542239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4714754037870927220722985 3536065528403195415542239)
                      ·
                        rfl

theorem cell23_6886463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 6, 2].length) (baseStart_6886463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886463 prefixEnd_6886463 := by exact prefixLift 6886463
  have htrace : WordTrace (prefixWord ++ tailWord_6886463) baseStart_6886463 baseEnd_6886463 := by
    simpa [prefixWord, tailWord_6886463, baseEnd_6886463] using wordTrace_append hprefix tailTrace_6886463
  have hstable : (prefixWord ++ tailWord_6886463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886463).length < 2 ^ (prefixWord ++ tailWord_6886463).sum := by decide
  have hdescent : baseEnd_6886463 < baseStart_6886463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886494 : List Nat := [4, 4, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_6886494 : Nat := 118140960795 + 6886494 * 2 ^ 59
def prefixEnd_6886494 : Nat := 4983230072969 + 3 ^ 40 * 6886494 * 2
def baseEnd_6886494 : Nat := 1178693815434494931418199

theorem tailTrace_6886494 : CollatzResearch.WordTrace tailWord_6886494 prefixEnd_6886494 1178693815434494931418199 := by
  unfold tailWord_6886494
  simp only [CollatzResearch.WordTrace]
  refine ⟨31396383839176979048081317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167447380475610554923100357 31396383839176979048081317)
  ·
    refine ⟨5886821969845683571515247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31396383839176979048081317 5886821969845683571515247)
    ·
      refine ⟨8830232954768525357272871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5886821969845683571515247 8830232954768525357272871)
      ·
        refine ⟨13245349432152788035909307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8830232954768525357272871 13245349432152788035909307)
        ·
          refine ⟨19868024148229182053863961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13245349432152788035909307 19868024148229182053863961)
          ·
            refine ⟨14901018111171886540397971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19868024148229182053863961 14901018111171886540397971)
            ·
              refine ⟨22351527166757829810596957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14901018111171886540397971 22351527166757829810596957)
              ·
                refine ⟨8381822687534186178973859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22351527166757829810596957 8381822687534186178973859)
                ·
                  refine ⟨12572734031301279268460789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8381822687534186178973859 12572734031301279268460789)
                  ·
                    refine ⟨1178693815434494931418199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12572734031301279268460789 1178693815434494931418199)
                    ·
                      rfl

theorem cell23_6886494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_6886494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886494 prefixEnd_6886494 := by exact prefixLift 6886494
  have htrace : WordTrace (prefixWord ++ tailWord_6886494) baseStart_6886494 baseEnd_6886494 := by
    simpa [prefixWord, tailWord_6886494, baseEnd_6886494] using wordTrace_append hprefix tailTrace_6886494
  have hstable : (prefixWord ++ tailWord_6886494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886494).length < 2 ^ (prefixWord ++ tailWord_6886494).sum := by decide
  have hdescent : baseEnd_6886494 < baseStart_6886494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886514 : List Nat := [3, 2, 1, 2, 2, 1, 1, 6, 1, 2, 2]
def baseStart_6886514 : Nat := 118140960795 + 6886514 * 2 ^ 59
def prefixEnd_6886514 : Nat := 4983230072969 + 3 ^ 40 * 6886514 * 2
def baseEnd_6886514 : Nat := 3536091715916574716004505

theorem tailTrace_6886514 : CollatzResearch.WordTrace tailWord_6886514 prefixEnd_6886514 3536091715916574716004505 := by
  unfold tailWord_6886514
  simp only [CollatzResearch.WordTrace]
  refine ⟨62792950043335843950094649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167447866782228917200252397 62792950043335843950094649)
  ·
    refine ⟨47094712532501882962570987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62792950043335843950094649 47094712532501882962570987)
    ·
      refine ⟨70642068798752824443856481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47094712532501882962570987 70642068798752824443856481)
      ·
        refine ⟨52981551599064618332892361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70642068798752824443856481 52981551599064618332892361)
        ·
          refine ⟨39736163699298463749669271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52981551599064618332892361 39736163699298463749669271)
          ·
            refine ⟨59604245548947695624503907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39736163699298463749669271 59604245548947695624503907)
            ·
              refine ⟨89406368323421543436755861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59604245548947695624503907 89406368323421543436755861)
              ·
                refine ⟨4190923515160384848597931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89406368323421543436755861 4190923515160384848597931)
                ·
                  refine ⟨6286385272740577272896897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4190923515160384848597931 6286385272740577272896897)
                  ·
                    refine ⟨4714788954555432954672673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6286385272740577272896897 4714788954555432954672673)
                    ·
                      refine ⟨3536091715916574716004505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4714788954555432954672673 3536091715916574716004505)
                      ·
                        rfl

theorem cell23_6886514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_6886514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886514 prefixEnd_6886514 := by exact prefixLift 6886514
  have htrace : WordTrace (prefixWord ++ tailWord_6886514) baseStart_6886514 baseEnd_6886514 := by
    simpa [prefixWord, tailWord_6886514, baseEnd_6886514] using wordTrace_append hprefix tailTrace_6886514
  have hstable : (prefixWord ++ tailWord_6886514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886514).length < 2 ^ (prefixWord ++ tailWord_6886514).sum := by decide
  have hdescent : baseEnd_6886514 < baseStart_6886514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886517 : List Nat := [1, 3, 4, 3, 1, 1, 1, 2, 1, 1, 5]
def baseStart_6886517 : Nat := 118140960795 + 6886517 * 2 ^ 59
def prefixEnd_6886517 : Nat := 4983230072969 + 3 ^ 40 * 6886517 * 2
def baseEnd_6886517 : Nat := 3536093256358538204266991

theorem tailTrace_6886517 : CollatzResearch.WordTrace tailWord_6886517 prefixEnd_6886517 3536093256358538204266991 := by
  unfold tailWord_6886517
  simp only [CollatzResearch.WordTrace]
  refine ⟨251171909592332507312737805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167447939728221671541825203 251171909592332507312737805)
  ·
    refine ⟨94189466097124690242276677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251171909592332507312737805 94189466097124690242276677)
    ·
      refine ⟨17660524893210879420426877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94189466097124690242276677 17660524893210879420426877)
      ·
        refine ⟨6622696834954079782660079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17660524893210879420426877 6622696834954079782660079)
        ·
          refine ⟨9934045252431119673990119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6622696834954079782660079 9934045252431119673990119)
          ·
            refine ⟨14901067878646679510985179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9934045252431119673990119 14901067878646679510985179)
            ·
              refine ⟨22351601817970019266477769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14901067878646679510985179 22351601817970019266477769)
              ·
                refine ⟨16763701363477514449858327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22351601817970019266477769 16763701363477514449858327)
                ·
                  refine ⟨25145552045216271674787491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16763701363477514449858327 25145552045216271674787491)
                  ·
                    refine ⟨37718328067824407512181237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25145552045216271674787491 37718328067824407512181237)
                    ·
                      refine ⟨3536093256358538204266991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37718328067824407512181237 3536093256358538204266991)
                      ·
                        rfl

theorem cell23_6886517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_6886517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886517 prefixEnd_6886517 := by exact prefixLift 6886517
  have htrace : WordTrace (prefixWord ++ tailWord_6886517) baseStart_6886517 baseEnd_6886517 := by
    simpa [prefixWord, tailWord_6886517, baseEnd_6886517] using wordTrace_append hprefix tailTrace_6886517
  have hstable : (prefixWord ++ tailWord_6886517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886517).length < 2 ^ (prefixWord ++ tailWord_6886517).sum := by decide
  have hdescent : baseEnd_6886517 < baseStart_6886517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886540 : List Nat := [2, 2, 1, 2, 1, 1, 1, 5, 3, 3, 2]
def baseStart_6886540 : Nat := 118140960795 + 6886540 * 2 ^ 59
def prefixEnd_6886540 : Nat := 4983230072969 + 3 ^ 40 * 6886540 * 2
def baseEnd_6886540 : Nat := 3536105066413591614279385

theorem tailTrace_6886540 : CollatzResearch.WordTrace tailWord_6886540 prefixEnd_6886540 3536105066413591614279385 := by
  unfold tailWord_6886540
  simp only [CollatzResearch.WordTrace]
  refine ⟨125586374235624591120412537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167448498980832788160550049 125586374235624591120412537)
  ·
    refine ⟨94189780676718443340309403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125586374235624591120412537 94189780676718443340309403)
    ·
      refine ⟨141284671015077665010464105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94189780676718443340309403 141284671015077665010464105)
      ·
        refine ⟨105963503261308248757848079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141284671015077665010464105 105963503261308248757848079)
        ·
          refine ⟨158945254891962373136772119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105963503261308248757848079 158945254891962373136772119)
          ·
            refine ⟨238417882337943559705158179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158945254891962373136772119 238417882337943559705158179)
            ·
              refine ⟨357626823506915339557737269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238417882337943559705158179 357626823506915339557737269)
              ·
                refine ⟨33527514703773313083537869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 357626823506915339557737269 33527514703773313083537869)
                ·
                  refine ⟨12572818013914992406326701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33527514703773313083537869 12572818013914992406326701)
                  ·
                    refine ⟨4714806755218122152372513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12572818013914992406326701 4714806755218122152372513)
                    ·
                      refine ⟨3536105066413591614279385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4714806755218122152372513 3536105066413591614279385)
                      ·
                        rfl

theorem cell23_6886540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 3, 3, 2].length) (baseStart_6886540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886540 prefixEnd_6886540 := by exact prefixLift 6886540
  have htrace : WordTrace (prefixWord ++ tailWord_6886540) baseStart_6886540 baseEnd_6886540 := by
    simpa [prefixWord, tailWord_6886540, baseEnd_6886540] using wordTrace_append hprefix tailTrace_6886540
  have hstable : (prefixWord ++ tailWord_6886540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886540).length < 2 ^ (prefixWord ++ tailWord_6886540).sum := by decide
  have hdescent : baseEnd_6886540 < baseStart_6886540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886557 : List Nat := [1, 4, 2, 1, 1, 2, 1, 5, 1, 3, 2]
def baseStart_6886557 : Nat := 118140960795 + 6886557 * 2 ^ 59
def prefixEnd_6886557 : Nat := 4983230072969 + 3 ^ 40 * 6886557 * 2
def baseEnd_6886557 : Nat := 3536113795584718047766807

theorem tailTrace_6886557 : CollatzResearch.WordTrace tailWord_6886557 prefixEnd_6886557 3536113795584718047766807 := by
  unfold tailWord_6886557
  simp only [CollatzResearch.WordTrace]
  refine ⟨251173368512187594144193925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167448912341458396096129283 251173368512187594144193925)
  ·
    refine ⟨47095006596035173902036361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251173368512187594144193925 47095006596035173902036361)
    ·
      refine ⟨35321254947026380426527271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47095006596035173902036361 35321254947026380426527271)
      ·
        refine ⟨52981882420539570639790907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35321254947026380426527271 52981882420539570639790907)
        ·
          refine ⟨79472823630809355959686361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52981882420539570639790907 79472823630809355959686361)
          ·
            refine ⟨59604617723107016969764771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79472823630809355959686361 59604617723107016969764771)
            ·
              refine ⟨89406926584660525454647157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59604617723107016969764771 89406926584660525454647157)
              ·
                refine ⟨8381899367311924261373171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89406926584660525454647157 8381899367311924261373171)
                ·
                  refine ⟨12572849050967886392059757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8381899367311924261373171 12572849050967886392059757)
                  ·
                    refine ⟨4714818394112957397022409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12572849050967886392059757 4714818394112957397022409)
                    ·
                      refine ⟨3536113795584718047766807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4714818394112957397022409 3536113795584718047766807)
                      ·
                        rfl

theorem cell23_6886557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_6886557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886557 prefixEnd_6886557 := by exact prefixLift 6886557
  have htrace : WordTrace (prefixWord ++ tailWord_6886557) baseStart_6886557 baseEnd_6886557 := by
    simpa [prefixWord, tailWord_6886557, baseEnd_6886557] using wordTrace_append hprefix tailTrace_6886557
  have hstable : (prefixWord ++ tailWord_6886557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886557).length < 2 ^ (prefixWord ++ tailWord_6886557).sum := by decide
  have hdescent : baseEnd_6886557 < baseStart_6886557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886583 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 4]
def baseStart_6886583 : Nat := 118140960795 + 6886583 * 2 ^ 59
def prefixEnd_6886583 : Nat := 4983230072969 + 3 ^ 40 * 6886583 * 2
def baseEnd_6886583 : Nat := 3536127146081734946041687

theorem tailTrace_6886583 : CollatzResearch.WordTrace tailWord_6886583 prefixEnd_6886583 3536127146081734946041687 := by
  unfold tailWord_6886583
  simp only [CollatzResearch.WordTrace]
  refine ⟨251174316810093400584640403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167449544540062267056426935 251174316810093400584640403)
  ·
    refine ⟨376761475215140100876960605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251174316810093400584640403 376761475215140100876960605)
    ·
      refine ⟨141285553205677537828860227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 376761475215140100876960605 141285553205677537828860227)
      ·
        refine ⟨211928329808516306743290341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141285553205677537828860227 211928329808516306743290341)
        ·
          refine ⟨39736561839096807514366939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211928329808516306743290341 39736561839096807514366939)
          ·
            refine ⟨59604842758645211271550409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39736561839096807514366939 59604842758645211271550409)
            ·
              refine ⟨44703632068983908453662807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59604842758645211271550409 44703632068983908453662807)
              ·
                refine ⟨67055448103475862680494211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44703632068983908453662807 67055448103475862680494211)
                ·
                  refine ⟨100583172155213794020741317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67055448103475862680494211 100583172155213794020741317)
                  ·
                    refine ⟨18859344779102586378888997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100583172155213794020741317 18859344779102586378888997)
                    ·
                      refine ⟨3536127146081734946041687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18859344779102586378888997 3536127146081734946041687)
                      ·
                        rfl

theorem cell23_6886583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_6886583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886583 prefixEnd_6886583 := by exact prefixLift 6886583
  have htrace : WordTrace (prefixWord ++ tailWord_6886583) baseStart_6886583 baseEnd_6886583 := by
    simpa [prefixWord, tailWord_6886583, baseEnd_6886583] using wordTrace_append hprefix tailTrace_6886583
  have hstable : (prefixWord ++ tailWord_6886583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886583).length < 2 ^ (prefixWord ++ tailWord_6886583).sum := by decide
  have hdescent : baseEnd_6886583 < baseStart_6886583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886590 : List Nat := [4, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5]
def baseStart_6886590 : Nat := 118140960795 + 6886590 * 2 ^ 59
def prefixEnd_6886590 : Nat := 4983230072969 + 3 ^ 40 * 6886590 * 2
def baseEnd_6886590 : Nat := 3536130740446316418654155

theorem tailTrace_6886590 : CollatzResearch.WordTrace tailWord_6886590 prefixEnd_6886590 3536130740446316418654155 := by
  unfold tailWord_6886590
  simp only [CollatzResearch.WordTrace]
  refine ⟨31396821515133505097518153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167449714747378693853430149 31396821515133505097518153)
  ·
    refine ⟨23547616136350128823138615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31396821515133505097518153 23547616136350128823138615)
    ·
      refine ⟨35321424204525193234707923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23547616136350128823138615 35321424204525193234707923)
      ·
        refine ⟨52982136306787789852061885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35321424204525193234707923 52982136306787789852061885)
        ·
          refine ⟨19868301115045421194523207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52982136306787789852061885 19868301115045421194523207)
          ·
            refine ⟨29802451672568131791784811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19868301115045421194523207 29802451672568131791784811)
            ·
              refine ⟨44703677508852197687677217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29802451672568131791784811 44703677508852197687677217)
              ·
                refine ⟨33527758131639148265757913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44703677508852197687677217 33527758131639148265757913)
                ·
                  refine ⟨25145818598729361199318435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33527758131639148265757913 25145818598729361199318435)
                  ·
                    refine ⟨37718727898094041798977653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25145818598729361199318435 37718727898094041798977653)
                    ·
                      refine ⟨3536130740446316418654155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37718727898094041798977653 3536130740446316418654155)
                      ·
                        rfl

theorem cell23_6886590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_6886590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886590 prefixEnd_6886590 := by exact prefixLift 6886590
  have htrace : WordTrace (prefixWord ++ tailWord_6886590) baseStart_6886590 baseEnd_6886590 := by
    simpa [prefixWord, tailWord_6886590, baseEnd_6886590] using wordTrace_append hprefix tailTrace_6886590
  have hstable : (prefixWord ++ tailWord_6886590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886590).length < 2 ^ (prefixWord ++ tailWord_6886590).sum := by decide
  have hdescent : baseEnd_6886590 < baseStart_6886590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886603 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 3, 5, 3]
def baseStart_6886603 : Nat := 118140960795 + 6886603 * 2 ^ 59
def prefixEnd_6886603 : Nat := 4983230072969 + 3 ^ 40 * 6886603 * 2
def baseEnd_6886603 : Nat := 3536137415694824867791595

theorem tailTrace_6886603 : CollatzResearch.WordTrace tailWord_6886603 prefixEnd_6886603 3536137415694824867791595 := by
  unfold tailWord_6886603
  simp only [CollatzResearch.WordTrace]
  refine ⟨251175046270020944000368463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167450030846680629333578975 251175046270020944000368463)
  ·
    refine ⟨376762569405031416000552695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251175046270020944000368463 376762569405031416000552695)
    ·
      refine ⟨565143854107547124000829043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376762569405031416000552695 565143854107547124000829043)
      ·
        refine ⟨847715781161320686001243565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565143854107547124000829043 847715781161320686001243565)
        ·
          refine ⟨317893417935495257250466337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 847715781161320686001243565 317893417935495257250466337)
          ·
            refine ⟨238420063451621442937849753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317893417935495257250466337 238420063451621442937849753)
            ·
              refine ⟨178815047588716082203387315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238420063451621442937849753 178815047588716082203387315)
              ·
                refine ⟨268222571383074123305080973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178815047588716082203387315 268222571383074123305080973)
                ·
                  refine ⟨100583464268652796239405365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 268222571383074123305080973 100583464268652796239405365)
                  ·
                    refine ⟨9429699775186199647444253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100583464268652796239405365 9429699775186199647444253)
                    ·
                      refine ⟨3536137415694824867791595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9429699775186199647444253 3536137415694824867791595)
                      ·
                        rfl

theorem cell23_6886603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 5, 3].length) (baseStart_6886603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886603 prefixEnd_6886603 := by exact prefixLift 6886603
  have htrace : WordTrace (prefixWord ++ tailWord_6886603) baseStart_6886603 baseEnd_6886603 := by
    simpa [prefixWord, tailWord_6886603, baseEnd_6886603] using wordTrace_append hprefix tailTrace_6886603
  have hstable : (prefixWord ++ tailWord_6886603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886603).length < 2 ^ (prefixWord ++ tailWord_6886603).sum := by decide
  have hdescent : baseEnd_6886603 < baseStart_6886603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886637 : List Nat := [1, 5, 1, 2, 2, 2, 1, 1, 2, 3, 3]
def baseStart_6886637 : Nat := 118140960795 + 6886637 * 2 ^ 59
def prefixEnd_6886637 : Nat := 4983230072969 + 3 ^ 40 * 6886637 * 2
def baseEnd_6886637 : Nat := 3536154874037077734766439

theorem tailTrace_6886637 : CollatzResearch.WordTrace tailWord_6886637 prefixEnd_6886637 3536154874037077734766439 := by
  unfold tailWord_6886637
  simp only [CollatzResearch.WordTrace]
  refine ⟨251176286351897767807106165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167450857567931845204737443 251176286351897767807106165)
  ·
    refine ⟨23547776845490415731916203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 251176286351897767807106165 23547776845490415731916203)
    ·
      refine ⟨35321665268235623597874305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23547776845490415731916203 35321665268235623597874305)
      ·
        refine ⟨26491248951176717698405729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35321665268235623597874305 26491248951176717698405729)
        ·
          refine ⟨19868436713382538273804297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26491248951176717698405729 19868436713382538273804297)
          ·
            refine ⟨14901327535036903705353223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19868436713382538273804297 14901327535036903705353223)
            ·
              refine ⟨22351991302555355558029835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14901327535036903705353223 22351991302555355558029835)
              ·
                refine ⟨33527986953833033337044753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22351991302555355558029835 33527986953833033337044753)
                ·
                  refine ⟨25145990215374775002783565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33527986953833033337044753 25145990215374775002783565)
                  ·
                    refine ⟨9429746330765540626043837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25145990215374775002783565 9429746330765540626043837)
                    ·
                      refine ⟨3536154874037077734766439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9429746330765540626043837 3536154874037077734766439)
                      ·
                        rfl

theorem cell23_6886637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_6886637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886637 prefixEnd_6886637 := by exact prefixLift 6886637
  have htrace : WordTrace (prefixWord ++ tailWord_6886637) baseStart_6886637 baseEnd_6886637 := by
    simpa [prefixWord, tailWord_6886637, baseEnd_6886637] using wordTrace_append hprefix tailTrace_6886637
  have hstable : (prefixWord ++ tailWord_6886637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886637).length < 2 ^ (prefixWord ++ tailWord_6886637).sum := by decide
  have hdescent : baseEnd_6886637 < baseStart_6886637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886657 : List Nat := [1, 2, 4, 1, 1, 5, 1, 1, 2, 5]
def baseStart_6886657 : Nat := 118140960795 + 6886657 * 2 ^ 59
def prefixEnd_6886657 : Nat := 4983230072969 + 3 ^ 40 * 6886657 * 2
def baseEnd_6886657 : Nat := 1178721714550055885505449

theorem tailTrace_6886657 : CollatzResearch.WordTrace tailWord_6886657 prefixEnd_6886657 1178721714550055885505449 := by
  unfold tailWord_6886657
  simp only [CollatzResearch.WordTrace]
  refine ⟨251177015811825311222834225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167451343874550207481889483 251177015811825311222834225)
  ·
    refine ⟨188382761858868983417125669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251177015811825311222834225 188382761858868983417125669)
    ·
      refine ⟨35321767848537934390711063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188382761858868983417125669 35321767848537934390711063)
      ·
        refine ⟨52982651772806901586066595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35321767848537934390711063 52982651772806901586066595)
        ·
          refine ⟨79473977659210352379099893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52982651772806901586066595 79473977659210352379099893)
          ·
            refine ⟨7450685405550970535540615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79473977659210352379099893 7450685405550970535540615)
            ·
              refine ⟨11176028108326455803310923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7450685405550970535540615 11176028108326455803310923)
              ·
                refine ⟨16764042162489683704966385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11176028108326455803310923 16764042162489683704966385)
                ·
                  refine ⟨12573031621867262778724789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16764042162489683704966385 12573031621867262778724789)
                  ·
                    refine ⟨1178721714550055885505449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12573031621867262778724789 1178721714550055885505449)
                    ·
                      rfl

theorem cell23_6886657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_6886657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886657 prefixEnd_6886657 := by exact prefixLift 6886657
  have htrace : WordTrace (prefixWord ++ tailWord_6886657) baseStart_6886657 baseEnd_6886657 := by
    simpa [prefixWord, tailWord_6886657, baseEnd_6886657] using wordTrace_append hprefix tailTrace_6886657
  have hstable : (prefixWord ++ tailWord_6886657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886657).length < 2 ^ (prefixWord ++ tailWord_6886657).sum := by decide
  have hdescent : baseEnd_6886657 < baseStart_6886657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886673 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 6]
def baseStart_6886673 : Nat := 118140960795 + 6886673 * 2 ^ 59
def prefixEnd_6886673 : Nat := 4983230072969 + 3 ^ 40 * 6886673 * 2
def baseEnd_6886673 : Nat := 3536173359340639593916273

theorem tailTrace_6886673 : CollatzResearch.WordTrace tailWord_6886673 prefixEnd_6886673 3536173359340639593916273 := by
  unfold tailWord_6886673
  simp only [CollatzResearch.WordTrace]
  refine ⟨251177599379767345955416673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167451732919844897303611115 251177599379767345955416673)
  ·
    refine ⟨188383199534825509466562505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251177599379767345955416673 188383199534825509466562505)
    ·
      refine ⟨141287399651119132099921879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188383199534825509466562505 141287399651119132099921879)
      ·
        refine ⟨211931099476678698149882819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141287399651119132099921879 211931099476678698149882819)
        ·
          refine ⟨317896649215018047224824229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211931099476678698149882819 317896649215018047224824229)
          ·
            refine ⟨59605621727815883854654543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 317896649215018047224824229 59605621727815883854654543)
            ·
              refine ⟨89408432591723825781981815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59605621727815883854654543 89408432591723825781981815)
              ·
                refine ⟨134112648887585738672972723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89408432591723825781981815 134112648887585738672972723)
                ·
                  refine ⟨201168973331378608009459085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134112648887585738672972723 201168973331378608009459085)
                  ·
                    refine ⟨75438364999266978003547157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 201168973331378608009459085 75438364999266978003547157)
                    ·
                      refine ⟨3536173359340639593916273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75438364999266978003547157 3536173359340639593916273)
                      ·
                        rfl

theorem cell23_6886673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_6886673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886673 prefixEnd_6886673 := by exact prefixLift 6886673
  have htrace : WordTrace (prefixWord ++ tailWord_6886673) baseStart_6886673 baseEnd_6886673 := by
    simpa [prefixWord, tailWord_6886673, baseEnd_6886673] using wordTrace_append hprefix tailTrace_6886673
  have hstable : (prefixWord ++ tailWord_6886673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886673).length < 2 ^ (prefixWord ++ tailWord_6886673).sum := by decide
  have hdescent : baseEnd_6886673 < baseStart_6886673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886703 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 6]
def baseStart_6886703 : Nat := 118140960795 + 6886703 * 2 ^ 59
def prefixEnd_6886703 : Nat := 4983230072969 + 3 ^ 40 * 6886703 * 2
def baseEnd_6886703 : Nat := 3536188763760274476541135

theorem tailTrace_6886703 : CollatzResearch.WordTrace tailWord_6886703 prefixEnd_6886703 3536188763760274476541135 := by
  unfold tailWord_6886703
  simp only [CollatzResearch.WordTrace]
  refine ⟨251178693569658661079008763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167452462379772440719339175 251178693569658661079008763)
  ·
    refine ⟨376768040354487991618513145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251178693569658661079008763 376768040354487991618513145)
    ·
      refine ⟨282576030265865993713884859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376768040354487991618513145 282576030265865993713884859)
      ·
        refine ⟨423864045398798990570827289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282576030265865993713884859 423864045398798990570827289)
        ·
          refine ⟨317898034049099242928120467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423864045398798990570827289 317898034049099242928120467)
          ·
            refine ⟨476847051073648864392180701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317898034049099242928120467 476847051073648864392180701)
            ·
              refine ⟨178817644152618324147067763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 476847051073648864392180701 178817644152618324147067763)
              ·
                refine ⟨268226466228927486220601645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178817644152618324147067763 268226466228927486220601645)
                ·
                  refine ⟨100584924835847807332725617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 268226466228927486220601645 100584924835847807332725617)
                  ·
                    refine ⟨75438693626885855499544213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100584924835847807332725617 75438693626885855499544213)
                    ·
                      refine ⟨3536188763760274476541135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75438693626885855499544213 3536188763760274476541135)
                      ·
                        rfl

theorem cell23_6886703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 6].length) (baseStart_6886703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886703 prefixEnd_6886703 := by exact prefixLift 6886703
  have htrace : WordTrace (prefixWord ++ tailWord_6886703) baseStart_6886703 baseEnd_6886703 := by
    simpa [prefixWord, tailWord_6886703, baseEnd_6886703] using wordTrace_append hprefix tailTrace_6886703
  have hstable : (prefixWord ++ tailWord_6886703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886703).length < 2 ^ (prefixWord ++ tailWord_6886703).sum := by decide
  have hdescent : baseEnd_6886703 < baseStart_6886703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886721 : List Nat := [1, 2, 5, 2, 1, 1, 3, 3, 1, 4]
def baseStart_6886721 : Nat := 118140960795 + 6886721 * 2 ^ 59
def prefixEnd_6886721 : Nat := 4983230072969 + 3 ^ 40 * 6886721 * 2
def baseEnd_6886721 : Nat := 1178732668804018468705351

theorem tailTrace_6886721 : CollatzResearch.WordTrace tailWord_6886721 prefixEnd_6886721 1178732668804018468705351 := by
  unfold tailWord_6886721
  simp only [CollatzResearch.WordTrace]
  refine ⟨251179350083593450153164017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167452900055728966768776011 251179350083593450153164017)
  ·
    refine ⟨188384512562695087614873013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251179350083593450153164017 188384512562695087614873013)
    ·
      refine ⟨17661048052752664463894345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188384512562695087614873013 17661048052752664463894345)
      ·
        refine ⟨13245786039564498347920759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17661048052752664463894345 13245786039564498347920759)
        ·
          refine ⟨19868679059346747521881139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13245786039564498347920759 19868679059346747521881139)
          ·
            refine ⟨29803018589020121282821709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19868679059346747521881139 29803018589020121282821709)
            ·
              refine ⟨11176131970882545481058141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29803018589020121282821709 11176131970882545481058141)
              ·
                refine ⟨4191049489080954555396803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11176131970882545481058141 4191049489080954555396803)
                ·
                  refine ⟨6286574233621431833095205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4191049489080954555396803 6286574233621431833095205)
                  ·
                    refine ⟨1178732668804018468705351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6286574233621431833095205 1178732668804018468705351)
                    ·
                      rfl

theorem cell23_6886721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_6886721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886721 prefixEnd_6886721 := by exact prefixLift 6886721
  have htrace : WordTrace (prefixWord ++ tailWord_6886721) baseStart_6886721 baseEnd_6886721 := by
    simpa [prefixWord, tailWord_6886721, baseEnd_6886721] using wordTrace_append hprefix tailTrace_6886721
  have hstable : (prefixWord ++ tailWord_6886721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886721).length < 2 ^ (prefixWord ++ tailWord_6886721).sum := by decide
  have hdescent : baseEnd_6886721 < baseStart_6886721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886754 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 4, 3, 2]
def baseStart_6886754 : Nat := 118140960795 + 6886754 * 2 ^ 59
def prefixEnd_6886754 : Nat := 4983230072969 + 3 ^ 40 * 6886754 * 2
def baseEnd_6886754 : Nat := 3536214951273653777003401

theorem tailTrace_6886754 : CollatzResearch.WordTrace tailWord_6886754 prefixEnd_6886754 3536214951273653777003401 := by
  unfold tailWord_6886754
  simp only [CollatzResearch.WordTrace]
  refine ⟨62795138423118474197278829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167453702461649264526076877 62795138423118474197278829)
  ·
    refine ⟨23548176908669427823979561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62795138423118474197278829 23548176908669427823979561)
    ·
      refine ⟨17661132681502070867984671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23548176908669427823979561 17661132681502070867984671)
      ·
        refine ⟨26491699022253106301977007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17661132681502070867984671 26491699022253106301977007)
        ·
          refine ⟨39737548533379659452965511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26491699022253106301977007 39737548533379659452965511)
          ·
            refine ⟨59606322800069489179448267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39737548533379659452965511 59606322800069489179448267)
            ·
              refine ⟨89409484200104233769172401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59606322800069489179448267 89409484200104233769172401)
              ·
                refine ⟨67057113150078175326879301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89409484200104233769172401 67057113150078175326879301)
                ·
                  refine ⟨12573208715639657873789869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67057113150078175326879301 12573208715639657873789869)
                  ·
                    refine ⟨4714953268364871702671201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12573208715639657873789869 4714953268364871702671201)
                    ·
                      refine ⟨3536214951273653777003401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4714953268364871702671201 3536214951273653777003401)
                      ·
                        rfl

theorem cell23_6886754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_6886754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886754 prefixEnd_6886754 := by exact prefixLift 6886754
  have htrace : WordTrace (prefixWord ++ tailWord_6886754) baseStart_6886754 baseEnd_6886754 := by
    simpa [prefixWord, tailWord_6886754, baseEnd_6886754] using wordTrace_append hprefix tailTrace_6886754
  have hstable : (prefixWord ++ tailWord_6886754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886754).length < 2 ^ (prefixWord ++ tailWord_6886754).sum := by decide
  have hdescent : baseEnd_6886754 < baseStart_6886754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886764 : List Nat := [2, 2, 1, 1, 5, 3, 1, 2, 1, 5]
def baseStart_6886764 : Nat := 118140960795 + 6886764 * 2 ^ 59
def prefixEnd_6886764 : Nat := 4983230072969 + 3 ^ 40 * 6886764 * 2
def baseEnd_6886764 : Nat := 1178740028693399579292785

theorem tailTrace_6886764 : CollatzResearch.WordTrace tailWord_6886764 prefixEnd_6886764 1178740028693399579292785 := by
  unfold tailWord_6886764
  simp only [CollatzResearch.WordTrace]
  refine ⟨125590459211218834248489673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167453945614958445664652897 125590459211218834248489673)
  ·
    refine ⟨94192844408414125686367255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125590459211218834248489673 94192844408414125686367255)
    ·
      refine ⟨141289266612621188529550883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94192844408414125686367255 141289266612621188529550883)
      ·
        refine ⟨211933899918931782794326325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141289266612621188529550883 211933899918931782794326325)
        ·
          refine ⟨19868803117399854636968093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 211933899918931782794326325 19868803117399854636968093)
          ·
            refine ⟨7450801169024945488863035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19868803117399854636968093 7450801169024945488863035)
            ·
              refine ⟨11176201753537418233294553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7450801169024945488863035 11176201753537418233294553)
              ·
                refine ⟨8382151315153063674970915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11176201753537418233294553 8382151315153063674970915)
                ·
                  refine ⟨12573226972729595512456373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8382151315153063674970915 12573226972729595512456373)
                  ·
                    refine ⟨1178740028693399579292785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12573226972729595512456373 1178740028693399579292785)
                    ·
                      rfl

theorem cell23_6886764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 5].length) (baseStart_6886764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886764 prefixEnd_6886764 := by exact prefixLift 6886764
  have htrace : WordTrace (prefixWord ++ tailWord_6886764) baseStart_6886764 baseEnd_6886764 := by
    simpa [prefixWord, tailWord_6886764, baseEnd_6886764] using wordTrace_append hprefix tailTrace_6886764
  have hstable : (prefixWord ++ tailWord_6886764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886764).length < 2 ^ (prefixWord ++ tailWord_6886764).sum := by decide
  have hdescent : baseEnd_6886764 < baseStart_6886764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886787 : List Nat := [1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 5]
def baseStart_6886787 : Nat := 118140960795 + 6886787 * 2 ^ 59
def prefixEnd_6886787 : Nat := 4983230072969 + 3 ^ 40 * 6886787 * 2
def baseEnd_6886787 : Nat := 3536231896135252147890749

theorem tailTrace_6886787 : CollatzResearch.WordTrace tailWord_6886787 prefixEnd_6886787 3536231896135252147890749 := by
  unfold tailWord_6886787
  simp only [CollatzResearch.WordTrace]
  refine ⟨251181757301354343425066615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167454504867569562283377743 251181757301354343425066615)
  ·
    refine ⟨376772635952031515137599923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251181757301354343425066615 376772635952031515137599923)
    ·
      refine ⟨565158953928047272706399885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376772635952031515137599923 565158953928047272706399885)
      ·
        refine ⟨211934607723017727264899957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 565158953928047272706399885 211934607723017727264899957)
        ·
          refine ⟨19868869474032911931084371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 211934607723017727264899957 19868869474032911931084371)
          ·
            refine ⟨29803304211049367896626557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19868869474032911931084371 29803304211049367896626557)
            ·
              refine ⟨11176239079143512961234959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29803304211049367896626557 11176239079143512961234959)
              ·
                refine ⟨16764358618715269441852439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11176239079143512961234959 16764358618715269441852439)
                ·
                  refine ⟨25146537928072904162778659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16764358618715269441852439 25146537928072904162778659)
                  ·
                    refine ⟨37719806892109356244167989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25146537928072904162778659 37719806892109356244167989)
                    ·
                      refine ⟨3536231896135252147890749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37719806892109356244167989 3536231896135252147890749)
                      ·
                        rfl

theorem cell23_6886787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 5].length) (baseStart_6886787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886787 prefixEnd_6886787 := by exact prefixLift 6886787
  have htrace : WordTrace (prefixWord ++ tailWord_6886787) baseStart_6886787 baseEnd_6886787 := by
    simpa [prefixWord, tailWord_6886787, baseEnd_6886787] using wordTrace_append hprefix tailTrace_6886787
  have hstable : (prefixWord ++ tailWord_6886787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886787).length < 2 ^ (prefixWord ++ tailWord_6886787).sum := by decide
  have hdescent : baseEnd_6886787 < baseStart_6886787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886800 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 3]
def baseStart_6886800 : Nat := 118140960795 + 6886800 * 2 ^ 59
def prefixEnd_6886800 : Nat := 4983230072969 + 3 ^ 40 * 6886800 * 2
def baseEnd_6886800 : Nat := 3536238571383760597028189

theorem tailTrace_6886800 : CollatzResearch.WordTrace tailWord_6886800 prefixEnd_6886800 3536238571383760597028189 := by
  unfold tailWord_6886800
  simp only [CollatzResearch.WordTrace]
  refine ⟨125591115725153623322644927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167454820966871497763526569 125591115725153623322644927)
  ·
    refine ⟨188386673587730434983967391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125591115725153623322644927 188386673587730434983967391)
    ·
      refine ⟨282580010381595652475951087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188386673587730434983967391 282580010381595652475951087)
      ·
        refine ⟨423870015572393478713926631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282580010381595652475951087 423870015572393478713926631)
        ·
          refine ⟨635805023358590218070889947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423870015572393478713926631 635805023358590218070889947)
          ·
            refine ⟨953707535037885327106334921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635805023358590218070889947 953707535037885327106334921)
            ·
              refine ⟨715280651278413995329751191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 953707535037885327106334921 715280651278413995329751191)
              ·
                refine ⟨1072920976917620992994626787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 715280651278413995329751191 1072920976917620992994626787)
                ·
                  refine ⟨1609381465376431489491940181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1072920976917620992994626787 1609381465376431489491940181)
                  ·
                    refine ⟨9429969523690028258741837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1609381465376431489491940181 9429969523690028258741837)
                    ·
                      refine ⟨3536238571383760597028189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9429969523690028258741837 3536238571383760597028189)
                      ·
                        rfl

theorem cell23_6886800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 3].length) (baseStart_6886800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886800 prefixEnd_6886800 := by exact prefixLift 6886800
  have htrace : WordTrace (prefixWord ++ tailWord_6886800) baseStart_6886800 baseEnd_6886800 := by
    simpa [prefixWord, tailWord_6886800, baseEnd_6886800] using wordTrace_append hprefix tailTrace_6886800
  have hstable : (prefixWord ++ tailWord_6886800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886800).length < 2 ^ (prefixWord ++ tailWord_6886800).sum := by decide
  have hdescent : baseEnd_6886800 < baseStart_6886800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886801 : List Nat := [1, 2, 2, 1, 1, 1, 2, 8, 1, 2, 2]
def baseStart_6886801 : Nat := 118140960795 + 6886801 * 2 ^ 59
def prefixEnd_6886801 : Nat := 4983230072969 + 3 ^ 40 * 6886801 * 2
def baseEnd_6886801 : Nat := 3536239084864415093115685

theorem tailTrace_6886801 : CollatzResearch.WordTrace tailWord_6886801 prefixEnd_6886801 3536239084864415093115685 := by
  unfold tailWord_6886801
  simp only [CollatzResearch.WordTrace]
  refine ⟨251182267923303623816076257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167454845282202415877384171 251182267923303623816076257)
  ·
    refine ⟨188386700942477717862057193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251182267923303623816076257 188386700942477717862057193)
    ·
      refine ⟨141290025706858288396542895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188386700942477717862057193 141290025706858288396542895)
      ·
        refine ⟨211935038560287432594814343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141290025706858288396542895 211935038560287432594814343)
        ·
          refine ⟨317902557840431148892221515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211935038560287432594814343 317902557840431148892221515)
          ·
            refine ⟨476853836760646723338332273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317902557840431148892221515 476853836760646723338332273)
            ·
              refine ⟨357640377570485042503749205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 476853836760646723338332273 357640377570485042503749205)
              ·
                refine ⟨4191098174654121591840811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 357640377570485042503749205 4191098174654121591840811)
                ·
                  refine ⟨6286647261981182387761217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4191098174654121591840811 6286647261981182387761217)
                  ·
                    refine ⟨4714985446485886790820913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6286647261981182387761217 4714985446485886790820913)
                    ·
                      refine ⟨3536239084864415093115685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4714985446485886790820913 3536239084864415093115685)
                      ·
                        rfl

theorem cell23_6886801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 8, 1, 2, 2].length) (baseStart_6886801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886801 prefixEnd_6886801 := by exact prefixLift 6886801
  have htrace : WordTrace (prefixWord ++ tailWord_6886801) baseStart_6886801 baseEnd_6886801 := by
    simpa [prefixWord, tailWord_6886801, baseEnd_6886801] using wordTrace_append hprefix tailTrace_6886801
  have hstable : (prefixWord ++ tailWord_6886801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886801).length < 2 ^ (prefixWord ++ tailWord_6886801).sum := by decide
  have hdescent : baseEnd_6886801 < baseStart_6886801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886804 : List Nat := [2, 4, 2, 1, 2, 1, 1, 2, 3, 2, 3]
def baseStart_6886804 : Nat := 118140960795 + 6886804 * 2 ^ 59
def prefixEnd_6886804 : Nat := 4983230072969 + 3 ^ 40 * 6886804 * 2
def baseEnd_6886804 : Nat := 3536240625306378581378171

theorem tailTrace_6886804 : CollatzResearch.WordTrace tailWord_6886804 prefixEnd_6886804 3536240625306378581378171 := by
  unfold tailWord_6886804
  simp only [CollatzResearch.WordTrace]
  refine ⟨125591188671146377664217733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167454918228195170218956977 125591188671146377664217733)
  ·
    refine ⟨23548347875839945812040825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125591188671146377664217733 23548347875839945812040825)
    ·
      refine ⟨17661260906879959359030619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23548347875839945812040825 17661260906879959359030619)
      ·
        refine ⟨26491891360319939038545929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17661260906879959359030619 26491891360319939038545929)
        ·
          refine ⟨19868918520239954278909447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26491891360319939038545929 19868918520239954278909447)
          ·
            refine ⟨29803377780359931418364171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19868918520239954278909447 29803377780359931418364171)
            ·
              refine ⟨44705066670539897127546257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29803377780359931418364171 44705066670539897127546257)
              ·
                refine ⟨33528800002904922845659693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44705066670539897127546257 33528800002904922845659693)
                ·
                  refine ⟨12573300001089346067122385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33528800002904922845659693 12573300001089346067122385)
                  ·
                    refine ⟨9429975000817009550341789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12573300001089346067122385 9429975000817009550341789)
                    ·
                      refine ⟨3536240625306378581378171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9429975000817009550341789 3536240625306378581378171)
                      ·
                        rfl

theorem cell23_6886804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_6886804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886804 prefixEnd_6886804 := by exact prefixLift 6886804
  have htrace : WordTrace (prefixWord ++ tailWord_6886804) baseStart_6886804 baseEnd_6886804 := by
    simpa [prefixWord, tailWord_6886804, baseEnd_6886804] using wordTrace_append hprefix tailTrace_6886804
  have hstable : (prefixWord ++ tailWord_6886804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886804).length < 2 ^ (prefixWord ++ tailWord_6886804).sum := by decide
  have hdescent : baseEnd_6886804 < baseStart_6886804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886820 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 4, 7]
def baseStart_6886820 : Nat := 118140960795 + 6886820 * 2 ^ 59
def prefixEnd_6886820 : Nat := 4983230072969 + 3 ^ 40 * 6886820 * 2
def baseEnd_6886820 : Nat := 1178749613665616839592699

theorem tailTrace_6886820 : CollatzResearch.WordTrace tailWord_6886820 prefixEnd_6886820 1178749613665616839592699 := by
  unfold tailWord_6886820
  simp only [CollatzResearch.WordTrace]
  refine ⟨125591480455117395030508957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167455307273489860040678609 125591480455117395030508957)
  ·
    refine ⟨47096805170669023136440859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125591480455117395030508957 47096805170669023136440859)
    ·
      refine ⟨70645207756003534704661289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47096805170669023136440859 70645207756003534704661289)
      ·
        refine ⟨52983905817002651028495967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70645207756003534704661289 52983905817002651028495967)
        ·
          refine ⟨79475858725503976542743951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52983905817002651028495967 79475858725503976542743951)
          ·
            refine ⟨119213788088255964814115927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79475858725503976542743951 119213788088255964814115927)
            ·
              refine ⟨178820682132383947221173891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119213788088255964814115927 178820682132383947221173891)
              ·
                refine ⟨268231023198575920831760837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178820682132383947221173891 268231023198575920831760837)
                ·
                  refine ⟨50293316849732985155955157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 268231023198575920831760837 50293316849732985155955157)
                  ·
                    refine ⟨1178749613665616839592699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50293316849732985155955157 1178749613665616839592699)
                    ·
                      rfl

theorem cell23_6886820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_6886820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886820 prefixEnd_6886820 := by exact prefixLift 6886820
  have htrace : WordTrace (prefixWord ++ tailWord_6886820) baseStart_6886820 baseEnd_6886820 := by
    simpa [prefixWord, tailWord_6886820, baseEnd_6886820] using wordTrace_append hprefix tailTrace_6886820
  have hstable : (prefixWord ++ tailWord_6886820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886820).length < 2 ^ (prefixWord ++ tailWord_6886820).sum := by decide
  have hdescent : baseEnd_6886820 < baseStart_6886820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886868 : List Nat := [2, 4, 1, 2, 4, 1, 1, 1, 1, 3, 3]
def baseStart_6886868 : Nat := 118140960795 + 6886868 * 2 ^ 59
def prefixEnd_6886868 : Nat := 4983230072969 + 3 ^ 40 * 6886868 * 2
def baseEnd_6886868 : Nat := 3536273488068266330977877

theorem tailTrace_6886868 : CollatzResearch.WordTrace tailWord_6886868 prefixEnd_6886868 3536273488068266330977877 := by
  unfold tailWord_6886868
  simp only [CollatzResearch.WordTrace]
  refine ⟨125592355807030447129382629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167456474409373929505843505 125592355807030447129382629)
  ·
    refine ⟨23548566713818208836759243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125592355807030447129382629 23548566713818208836759243)
    ·
      refine ⟨35322850070727313255138865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23548566713818208836759243 35322850070727313255138865)
      ·
        refine ⟨26492137553045484941354149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35322850070727313255138865 26492137553045484941354149)
        ·
          refine ⟨4967275791196028426503903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26492137553045484941354149 4967275791196028426503903)
          ·
            refine ⟨7450913686794042639755855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4967275791196028426503903 7450913686794042639755855)
            ·
              refine ⟨11176370530191063959633783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7450913686794042639755855 11176370530191063959633783)
              ·
                refine ⟨16764555795286595939450675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11176370530191063959633783 16764555795286595939450675)
                ·
                  refine ⟨25146833692929893909176013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16764555795286595939450675 25146833692929893909176013)
                  ·
                    refine ⟨9430062634848710215941005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25146833692929893909176013 9430062634848710215941005)
                    ·
                      refine ⟨3536273488068266330977877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9430062634848710215941005 3536273488068266330977877)
                      ·
                        rfl

theorem cell23_6886868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_6886868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886868 prefixEnd_6886868 := by exact prefixLift 6886868
  have htrace : WordTrace (prefixWord ++ tailWord_6886868) baseStart_6886868 baseEnd_6886868 := by
    simpa [prefixWord, tailWord_6886868, baseEnd_6886868] using wordTrace_append hprefix tailTrace_6886868
  have hstable : (prefixWord ++ tailWord_6886868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886868).length < 2 ^ (prefixWord ++ tailWord_6886868).sum := by decide
  have hdescent : baseEnd_6886868 < baseStart_6886868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886880 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 9]
def baseStart_6886880 : Nat := 118140960795 + 6886880 * 2 ^ 59
def prefixEnd_6886880 : Nat := 4983230072969 + 3 ^ 40 * 6886880 * 2
def baseEnd_6886880 : Nat := 392919961092902253780869

theorem tailTrace_6886880 : CollatzResearch.WordTrace tailWord_6886880 prefixEnd_6886880 392919961092902253780869 := by
  unfold tailWord_6886880
  simp only [CollatzResearch.WordTrace]
  refine ⟨125592574645008710154101047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167456766193344946872134729 125592574645008710154101047)
  ·
    refine ⟨188388861967513065231151571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125592574645008710154101047 188388861967513065231151571)
    ·
      refine ⟨282583292951269597846727357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188388861967513065231151571 282583292951269597846727357)
      ·
        refine ⟨105968734856726099192522759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282583292951269597846727357 105968734856726099192522759)
        ·
          refine ⟨158953102285089148788784139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105968734856726099192522759 158953102285089148788784139)
          ·
            refine ⟨238429653427633723183176209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158953102285089148788784139 238429653427633723183176209)
            ·
              refine ⟨178822240070725292387382157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238429653427633723183176209 178822240070725292387382157)
              ·
                refine ⟨67058340026521984645268309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178822240070725292387382157 67058340026521984645268309)
                ·
                  refine ⟨392919961092902253780869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67058340026521984645268309 392919961092902253780869)
                  ·
                    rfl

theorem cell23_6886880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 9].length) (baseStart_6886880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886880 prefixEnd_6886880 := by exact prefixLift 6886880
  have htrace : WordTrace (prefixWord ++ tailWord_6886880) baseStart_6886880 baseEnd_6886880 := by
    simpa [prefixWord, tailWord_6886880, baseEnd_6886880] using wordTrace_append hprefix tailTrace_6886880
  have hstable : (prefixWord ++ tailWord_6886880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886880).length < 2 ^ (prefixWord ++ tailWord_6886880).sum := by decide
  have hdescent : baseEnd_6886880 < baseStart_6886880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886942 : List Nat := [4, 3, 3, 1, 1, 1, 1, 2, 1, 4, 2]
def baseStart_6886942 : Nat := 118140960795 + 6886942 * 2 ^ 59
def prefixEnd_6886942 : Nat := 4983230072969 + 3 ^ 40 * 6886942 * 2
def baseEnd_6886942 : Nat := 3536311485636699041452537

theorem tailTrace_6886942 : CollatzResearch.WordTrace tailWord_6886942 prefixEnd_6886942 3536311485636699041452537 := by
  unfold tailWord_6886942
  simp only [CollatzResearch.WordTrace]
  refine ⟨31398426326974100612119885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167458273743861869931306053 31398426326974100612119885)
  ·
    refine ⟨11774409872615287729544957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31398426326974100612119885 11774409872615287729544957)
    ·
      refine ⟨4415403702230732898579359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11774409872615287729544957 4415403702230732898579359)
      ·
        refine ⟨6623105553346099347869039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4415403702230732898579359 6623105553346099347869039)
        ·
          refine ⟨9934658330019149021803559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6623105553346099347869039 9934658330019149021803559)
          ·
            refine ⟨14901987495028723532705339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9934658330019149021803559 14901987495028723532705339)
            ·
              refine ⟨22352981242543085299058009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14901987495028723532705339 22352981242543085299058009)
              ·
                refine ⟨16764735931907313974293507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22352981242543085299058009 16764735931907313974293507)
                ·
                  refine ⟨25147103897860970961440261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16764735931907313974293507 25147103897860970961440261)
                  ·
                    refine ⟨4715081980848932055270049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25147103897860970961440261 4715081980848932055270049)
                    ·
                      refine ⟨3536311485636699041452537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4715081980848932055270049 3536311485636699041452537)
                      ·
                        rfl

theorem cell23_6886942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_6886942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886942 prefixEnd_6886942 := by exact prefixLift 6886942
  have htrace : WordTrace (prefixWord ++ tailWord_6886942) baseStart_6886942 baseEnd_6886942 := by
    simpa [prefixWord, tailWord_6886942, baseEnd_6886942] using wordTrace_append hprefix tailTrace_6886942
  have hstable : (prefixWord ++ tailWord_6886942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886942).length < 2 ^ (prefixWord ++ tailWord_6886942).sum := by decide
  have hdescent : baseEnd_6886942 < baseStart_6886942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6886944 : List Nat := [2, 1, 1, 6, 1, 1, 1, 3, 2, 5]
def baseStart_6886944 : Nat := 118140960795 + 6886944 * 2 ^ 59
def prefixEnd_6886944 : Nat := 4983230072969 + 3 ^ 40 * 6886944 * 2
def baseEnd_6886944 : Nat := 1178770837532669344542509

theorem tailTrace_6886944 : CollatzResearch.WordTrace tailWord_6886944 prefixEnd_6886944 1178770837532669344542509 := by
  unfold tailWord_6886944
  simp only [CollatzResearch.WordTrace]
  refine ⟨125593741780892779619265943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167458322374523706159021257 125593741780892779619265943)
  ·
    refine ⟨188390612671339169428898915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125593741780892779619265943 188390612671339169428898915)
    ·
      refine ⟨282585919007008754143348373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188390612671339169428898915 282585919007008754143348373)
      ·
        refine ⟨13246214953453535350469455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 282585919007008754143348373 13246214953453535350469455)
        ·
          refine ⟨19869322430180303025704183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13246214953453535350469455 19869322430180303025704183)
          ·
            refine ⟨29803983645270454538556275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19869322430180303025704183 29803983645270454538556275)
            ·
              refine ⟨44705975467905681807834413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29803983645270454538556275 44705975467905681807834413)
              ·
                refine ⟨16764740800464630677937905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44705975467905681807834413 16764740800464630677937905)
                ·
                  refine ⟨12573555600348473008453429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16764740800464630677937905 12573555600348473008453429)
                  ·
                    refine ⟨1178770837532669344542509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12573555600348473008453429 1178770837532669344542509)
                    ·
                      rfl

theorem cell23_6886944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 2, 5].length) (baseStart_6886944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6886944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6886944 prefixEnd_6886944 := by exact prefixLift 6886944
  have htrace : WordTrace (prefixWord ++ tailWord_6886944) baseStart_6886944 baseEnd_6886944 := by
    simpa [prefixWord, tailWord_6886944, baseEnd_6886944] using wordTrace_append hprefix tailTrace_6886944
  have hstable : (prefixWord ++ tailWord_6886944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6886944).length < 2 ^ (prefixWord ++ tailWord_6886944).sum := by decide
  have hdescent : baseEnd_6886944 < baseStart_6886944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6886944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887041 : List Nat := [1, 2, 4, 2, 1, 2, 1, 2, 1, 5, 2]
def baseStart_6887041 : Nat := 118140960795 + 6887041 * 2 ^ 59
def prefixEnd_6887041 : Nat := 4983230072969 + 3 ^ 40 * 6887041 * 2
def baseEnd_6887041 : Nat := 3536362320221494154114581

theorem tailTrace_6887041 : CollatzResearch.WordTrace tailWord_6887041 prefixEnd_6887041 3536362320221494154114581 := by
  unfold tailWord_6887041
  simp only [CollatzResearch.WordTrace]
  refine ⟨251191021442434144804812977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167460680961622763203208651 251191021442434144804812977)
  ·
    refine ⟨188393266081825608603609733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251191021442434144804812977 188393266081825608603609733)
    ·
      refine ⟨35323737390342301613176825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188393266081825608603609733 35323737390342301613176825)
      ·
        refine ⟨26492803042756726209882619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35323737390342301613176825 26492803042756726209882619)
        ·
          refine ⟨39739204564135089314823929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26492803042756726209882619 39739204564135089314823929)
          ·
            refine ⟨29804403423101316986117947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39739204564135089314823929 29804403423101316986117947)
            ·
              refine ⟨44706605134651975479176921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29804403423101316986117947 44706605134651975479176921)
              ·
                refine ⟨33529953850988981609382691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44706605134651975479176921 33529953850988981609382691)
                ·
                  refine ⟨50294930776483472414074037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33529953850988981609382691 50294930776483472414074037)
                  ·
                    refine ⟨4715149760295325538819441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50294930776483472414074037 4715149760295325538819441)
                    ·
                      refine ⟨3536362320221494154114581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4715149760295325538819441 3536362320221494154114581)
                      ·
                        rfl

theorem cell23_6887041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_6887041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887041 prefixEnd_6887041 := by exact prefixLift 6887041
  have htrace : WordTrace (prefixWord ++ tailWord_6887041) baseStart_6887041 baseEnd_6887041 := by
    simpa [prefixWord, tailWord_6887041, baseEnd_6887041] using wordTrace_append hprefix tailTrace_6887041
  have hstable : (prefixWord ++ tailWord_6887041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887041).length < 2 ^ (prefixWord ++ tailWord_6887041).sum := by decide
  have hdescent : baseEnd_6887041 < baseStart_6887041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887077 : List Nat := [1, 3, 1, 2, 1, 2, 13]
def baseStart_6887077 : Nat := 118140960795 + 6887077 * 2 ^ 59
def prefixEnd_6887077 : Nat := 4983230072969 + 3 ^ 40 * 6887077 * 2
def baseEnd_6887077 : Nat := 43659022290432790287215

theorem tailTrace_6887077 : CollatzResearch.WordTrace tailWord_6887077 prefixEnd_6887077 43659022290432790287215 := by
  unfold tailWord_6887077
  simp only [CollatzResearch.WordTrace]
  refine ⟨251192334470303722953123485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167461556313535815302082323 251192334470303722953123485)
  ·
    refine ⟨94197125426363896107421307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251192334470303722953123485 94197125426363896107421307)
    ·
      refine ⟨141295688139545844161131961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94197125426363896107421307 141295688139545844161131961)
      ·
        refine ⟨105971766104659383120848971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141295688139545844161131961 105971766104659383120848971)
        ·
          refine ⟨158957649156989074681273457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105971766104659383120848971 158957649156989074681273457)
          ·
            refine ⟨119218236867741806010955093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158957649156989074681273457 119218236867741806010955093)
            ·
              refine ⟨43659022290432790287215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 119218236867741806010955093 43659022290432790287215)
              ·
                rfl

theorem cell23_6887077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 13].length) (baseStart_6887077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887077 prefixEnd_6887077 := by exact prefixLift 6887077
  have htrace : WordTrace (prefixWord ++ tailWord_6887077) baseStart_6887077 baseEnd_6887077 := by
    simpa [prefixWord, tailWord_6887077, baseEnd_6887077] using wordTrace_append hprefix tailTrace_6887077
  have hstable : (prefixWord ++ tailWord_6887077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887077).length < 2 ^ (prefixWord ++ tailWord_6887077).sum := by decide
  have hdescent : baseEnd_6887077 < baseStart_6887077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887088 : List Nat := [2, 1, 1, 1, 2, 1, 7, 1, 3, 2, 2]
def baseStart_6887088 : Nat := 118140960795 + 6887088 * 2 ^ 59
def prefixEnd_6887088 : Nat := 4983230072969 + 3 ^ 40 * 6887088 * 2
def baseEnd_6887088 : Nat := 3536386453812255470226865

theorem tailTrace_6887088 : CollatzResearch.WordTrace tailWord_6887088 prefixEnd_6887088 3536386453812255470226865 := by
  unfold tailWord_6887088
  simp only [CollatzResearch.WordTrace]
  refine ⟨125596367836631935915886959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167461823782175914554515945 125596367836631935915886959)
  ·
    refine ⟨188394551754947903873830439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125596367836631935915886959 188394551754947903873830439)
    ·
      refine ⟨282591827632421855810745659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188394551754947903873830439 282591827632421855810745659)
      ·
        refine ⟨423887741448632783716118489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282591827632421855810745659 423887741448632783716118489)
        ·
          refine ⟨317915806086474587787088867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423887741448632783716118489 317915806086474587787088867)
          ·
            refine ⟨476873709129711881680633301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317915806086474587787088867 476873709129711881680633301)
            ·
              refine ⟨11176727557727622226889843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 476873709129711881680633301 11176727557727622226889843)
              ·
                refine ⟨16765091336591433340334765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11176727557727622226889843 16765091336591433340334765)
                ·
                  refine ⟨6286909251221787502625537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16765091336591433340334765 6286909251221787502625537)
                  ·
                    refine ⟨4715181938416340626969153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6286909251221787502625537 4715181938416340626969153)
                    ·
                      refine ⟨3536386453812255470226865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4715181938416340626969153 3536386453812255470226865)
                      ·
                        rfl

theorem cell23_6887088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 3, 2, 2].length) (baseStart_6887088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887088 prefixEnd_6887088 := by exact prefixLift 6887088
  have htrace : WordTrace (prefixWord ++ tailWord_6887088) baseStart_6887088 baseEnd_6887088 := by
    simpa [prefixWord, tailWord_6887088, baseEnd_6887088] using wordTrace_append hprefix tailTrace_6887088
  have hstable : (prefixWord ++ tailWord_6887088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887088).length < 2 ^ (prefixWord ++ tailWord_6887088).sum := by decide
  have hdescent : baseEnd_6887088 < baseStart_6887088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887098 : List Nat := [3, 1, 1, 1, 2, 4, 4, 1, 2, 4]
def baseStart_6887098 : Nat := 118140960795 + 6887098 * 2 ^ 59
def prefixEnd_6887098 : Nat := 4983230072969 + 3 ^ 40 * 6887098 * 2
def baseEnd_6887098 : Nat := 1178797196206266810367273

theorem tailTrace_6887098 : CollatzResearch.WordTrace tailWord_6887098 prefixEnd_6887098 1178797196206266810367273 := by
  unfold tailWord_6887098
  simp only [CollatzResearch.WordTrace]
  refine ⟨62798275100806910884909487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167462066935485095693091965 62798275100806910884909487)
  ·
    refine ⟨94197412651210366327364231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62798275100806910884909487 94197412651210366327364231)
    ·
      refine ⟨141296118976815549491046347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94197412651210366327364231 141296118976815549491046347)
      ·
        refine ⟨211944178465223324236569521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141296118976815549491046347 211944178465223324236569521)
        ·
          refine ⟨158958133848917493177427141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211944178465223324236569521 158958133848917493177427141)
          ·
            refine ⟨29804650096672029970767589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158958133848917493177427141 29804650096672029970767589)
            ·
              refine ⟨5588371893126005619518923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29804650096672029970767589 5588371893126005619518923)
              ·
                refine ⟨8382557839689008429278385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5588371893126005619518923 8382557839689008429278385)
                ·
                  refine ⟨6286918379766756321958789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8382557839689008429278385 6286918379766756321958789)
                  ·
                    refine ⟨1178797196206266810367273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6286918379766756321958789 1178797196206266810367273)
                    ·
                      rfl

theorem cell23_6887098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 2, 4].length) (baseStart_6887098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887098 prefixEnd_6887098 := by exact prefixLift 6887098
  have htrace : WordTrace (prefixWord ++ tailWord_6887098) baseStart_6887098 baseEnd_6887098 := by
    simpa [prefixWord, tailWord_6887098, baseEnd_6887098] using wordTrace_append hprefix tailTrace_6887098
  have hstable : (prefixWord ++ tailWord_6887098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887098).length < 2 ^ (prefixWord ++ tailWord_6887098).sum := by decide
  have hdescent : baseEnd_6887098 < baseStart_6887098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887121 : List Nat := [1, 2, 2, 1, 2, 5, 1, 2, 1, 3, 3]
def baseStart_6887121 : Nat := 118140960795 + 6887121 * 2 ^ 59
def prefixEnd_6887121 : Nat := 4983230072969 + 3 ^ 40 * 6887121 * 2
def baseEnd_6887121 : Nat := 3536403398673853841114213

theorem tailTrace_6887121 : CollatzResearch.WordTrace tailWord_6887121 prefixEnd_6887121 3536403398673853841114213 := by
  unfold tailWord_6887121
  simp only [CollatzResearch.WordTrace]
  refine ⟨251193939282144318467725217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167462626188096212311816811 251193939282144318467725217)
  ·
    refine ⟨188395454461608238850793913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251193939282144318467725217 188395454461608238850793913)
    ·
      refine ⟨141296590846206179138095435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188395454461608238850793913 141296590846206179138095435)
      ·
        refine ⟨211944886269309268707143153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141296590846206179138095435 211944886269309268707143153)
        ·
          refine ⟨158958664701981951530357365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211944886269309268707143153 158958664701981951530357365)
          ·
            refine ⟨14902374815810807955971003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158958664701981951530357365 14902374815810807955971003)
            ·
              refine ⟨22353562223716211933956505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14902374815810807955971003 22353562223716211933956505)
              ·
                refine ⟨16765171667787158950467379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22353562223716211933956505 16765171667787158950467379)
                ·
                  refine ⟨25147757501680738425701069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16765171667787158950467379 25147757501680738425701069)
                  ·
                    refine ⟨9430409063130276909637901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25147757501680738425701069 9430409063130276909637901)
                    ·
                      refine ⟨3536403398673853841114213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9430409063130276909637901 3536403398673853841114213)
                      ·
                        rfl

theorem cell23_6887121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 3, 3].length) (baseStart_6887121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887121 prefixEnd_6887121 := by exact prefixLift 6887121
  have htrace : WordTrace (prefixWord ++ tailWord_6887121) baseStart_6887121 baseEnd_6887121 := by
    simpa [prefixWord, tailWord_6887121, baseEnd_6887121] using wordTrace_append hprefix tailTrace_6887121
  have hstable : (prefixWord ++ tailWord_6887121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887121).length < 2 ^ (prefixWord ++ tailWord_6887121).sum := by decide
  have hdescent : baseEnd_6887121 < baseStart_6887121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887178 : List Nat := [3, 1, 2, 2, 1, 3, 2, 2, 1, 4, 2]
def baseStart_6887178 : Nat := 118140960795 + 6887178 * 2 ^ 59
def prefixEnd_6887178 : Nat := 4983230072969 + 3 ^ 40 * 6887178 * 2
def baseEnd_6887178 : Nat := 3536432667071160118101451

theorem tailTrace_6887178 : CollatzResearch.WordTrace tailWord_6887178 prefixEnd_6887178 3536432667071160118101451 := by
  unfold tailWord_6887178
  simp only [CollatzResearch.WordTrace]
  refine ⟨62799004560734454300637547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167464012161958544801700125 62799004560734454300637547)
  ·
    refine ⟨94198506841101681450956321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62799004560734454300637547 94198506841101681450956321)
    ·
      refine ⟨70648880130826261088217241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94198506841101681450956321 70648880130826261088217241)
      ·
        refine ⟨52986660098119695816162931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70648880130826261088217241 52986660098119695816162931)
        ·
          refine ⟨79479990147179543724244397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52986660098119695816162931 79479990147179543724244397)
          ·
            refine ⟨29804996305192328896591649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79479990147179543724244397 29804996305192328896591649)
            ·
              refine ⟨22353747228894246672443737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29804996305192328896591649 22353747228894246672443737)
              ·
                refine ⟨16765310421670685004332803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22353747228894246672443737 16765310421670685004332803)
                ·
                  refine ⟨25147965632506027506499205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16765310421670685004332803 25147965632506027506499205)
                  ·
                    refine ⟨4715243556094880157468601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25147965632506027506499205 4715243556094880157468601)
                    ·
                      refine ⟨3536432667071160118101451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4715243556094880157468601 3536432667071160118101451)
                      ·
                        rfl

theorem cell23_6887178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_6887178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887178 prefixEnd_6887178 := by exact prefixLift 6887178
  have htrace : WordTrace (prefixWord ++ tailWord_6887178) baseStart_6887178 baseEnd_6887178 := by
    simpa [prefixWord, tailWord_6887178, baseEnd_6887178] using wordTrace_append hprefix tailTrace_6887178
  have hstable : (prefixWord ++ tailWord_6887178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887178).length < 2 ^ (prefixWord ++ tailWord_6887178).sum := by decide
  have hdescent : baseEnd_6887178 < baseStart_6887178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887191 : List Nat := [1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 4]
def baseStart_6887191 : Nat := 118140960795 + 6887191 * 2 ^ 59
def prefixEnd_6887191 : Nat := 4983230072969 + 3 ^ 40 * 6887191 * 2
def baseEnd_6887191 : Nat := 3536439342319668567238891

theorem tailTrace_6887191 : CollatzResearch.WordTrace tailWord_6887191 prefixEnd_6887191 3536439342319668567238891 := by
  unfold tailWord_6887191
  simp only [CollatzResearch.WordTrace]
  refine ⟨251196492391890720422773427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167464328261260480281848951 251196492391890720422773427)
  ·
    refine ⟨376794738587836080634160141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251196492391890720422773427 376794738587836080634160141)
    ·
      refine ⟨141298026970438530237810053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 376794738587836080634160141 141298026970438530237810053)
      ·
        refine ⟨26493380056957224419589385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141298026970438530237810053 26493380056957224419589385)
        ·
          refine ⟨19870035042717918314692039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26493380056957224419589385 19870035042717918314692039)
          ·
            refine ⟨29805052564076877472038059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19870035042717918314692039 29805052564076877472038059)
            ·
              refine ⟨44707578846115316208057089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29805052564076877472038059 44707578846115316208057089)
              ·
                refine ⟨33530684134586487156042817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44707578846115316208057089 33530684134586487156042817)
                ·
                  refine ⟨25148013100939865367032113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33530684134586487156042817 25148013100939865367032113)
                  ·
                    refine ⟨18861009825704899025274085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25148013100939865367032113 18861009825704899025274085)
                    ·
                      refine ⟨3536439342319668567238891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18861009825704899025274085 3536439342319668567238891)
                      ·
                        rfl

theorem cell23_6887191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_6887191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887191 prefixEnd_6887191 := by exact prefixLift 6887191
  have htrace : WordTrace (prefixWord ++ tailWord_6887191) baseStart_6887191 baseEnd_6887191 := by
    simpa [prefixWord, tailWord_6887191, baseEnd_6887191] using wordTrace_append hprefix tailTrace_6887191
  have hstable : (prefixWord ++ tailWord_6887191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887191).length < 2 ^ (prefixWord ++ tailWord_6887191).sum := by decide
  have hdescent : baseEnd_6887191 < baseStart_6887191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887201 : List Nat := [1, 2, 3, 2, 1, 4, 2, 1, 7]
def baseStart_6887201 : Nat := 118140960795 + 6887201 * 2 ^ 59
def prefixEnd_6887201 : Nat := 4983230072969 + 3 ^ 40 * 6887201 * 2
def baseEnd_6887201 : Nat := 392938275236245947568205

theorem tailTrace_6887201 : CollatzResearch.WordTrace tailWord_6887201 prefixEnd_6887201 392938275236245947568205 := by
  unfold tailWord_6887201
  simp only [CollatzResearch.WordTrace]
  refine ⟨251196857121854492130637457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167464571414569661420424971 251196857121854492130637457)
  ·
    refine ⟨188397642841390869097978093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251196857121854492130637457 188397642841390869097978093)
    ·
      refine ⟨70649116065521575911741785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188397642841390869097978093 70649116065521575911741785)
      ·
        refine ⟨52986837049141181933806339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70649116065521575911741785 52986837049141181933806339)
        ·
          refine ⟨79480255573711772900709509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52986837049141181933806339 79480255573711772900709509)
          ·
            refine ⟨14902547920070957418883033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79480255573711772900709509 14902547920070957418883033)
            ·
              refine ⟨11176910940053218064162275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14902547920070957418883033 11176910940053218064162275)
              ·
                refine ⟨16765366410079827096243413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11176910940053218064162275 16765366410079827096243413)
                ·
                  refine ⟨392938275236245947568205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16765366410079827096243413 392938275236245947568205)
                  ·
                    rfl

theorem cell23_6887201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 7].length) (baseStart_6887201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887201 prefixEnd_6887201 := by exact prefixLift 6887201
  have htrace : WordTrace (prefixWord ++ tailWord_6887201) baseStart_6887201 baseEnd_6887201 := by
    simpa [prefixWord, tailWord_6887201, baseEnd_6887201] using wordTrace_append hprefix tailTrace_6887201
  have hstable : (prefixWord ++ tailWord_6887201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887201).length < 2 ^ (prefixWord ++ tailWord_6887201).sum := by decide
  have hdescent : baseEnd_6887201 < baseStart_6887201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887212 : List Nat := [2, 2, 1, 1, 1, 6, 3, 1, 2, 2, 2]
def baseStart_6887212 : Nat := 118140960795 + 6887212 * 2 ^ 59
def prefixEnd_6887212 : Nat := 4983230072969 + 3 ^ 40 * 6887212 * 2
def baseEnd_6887212 : Nat := 3536450125413412985076295

theorem tailTrace_6887212 : CollatzResearch.WordTrace tailWord_6887212 prefixEnd_6887212 3536450125413412985076295 := by
  unfold tailWord_6887212
  simp only [CollatzResearch.WordTrace]
  refine ⟨125598629162407320504643945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167464838883209760672858593 125598629162407320504643945)
  ·
    refine ⟨94198971871805490378482959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125598629162407320504643945 94198971871805490378482959)
    ·
      refine ⟨141298457807708235567724439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94198971871805490378482959 141298457807708235567724439)
      ·
        refine ⟨211947686711562353351586659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141298457807708235567724439 211947686711562353351586659)
        ·
          refine ⟨317921530067343530027379989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211947686711562353351586659 317921530067343530027379989)
          ·
            refine ⟨14902571721906727970033437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 317921530067343530027379989 14902571721906727970033437)
            ·
              refine ⟨5588464395715022988762539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14902571721906727970033437 5588464395715022988762539)
              ·
                refine ⟨8382696593572534483143809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5588464395715022988762539 8382696593572534483143809)
                ·
                  refine ⟨6287022445179400862357857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8382696593572534483143809 6287022445179400862357857)
                  ·
                    refine ⟨4715266833884550646768393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6287022445179400862357857 4715266833884550646768393)
                    ·
                      refine ⟨3536450125413412985076295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4715266833884550646768393 3536450125413412985076295)
                      ·
                        rfl

theorem cell23_6887212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 2, 2].length) (baseStart_6887212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887212 prefixEnd_6887212 := by exact prefixLift 6887212
  have htrace : WordTrace (prefixWord ++ tailWord_6887212) baseStart_6887212 baseEnd_6887212 := by
    simpa [prefixWord, tailWord_6887212, baseEnd_6887212] using wordTrace_append hprefix tailTrace_6887212
  have hstable : (prefixWord ++ tailWord_6887212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887212).length < 2 ^ (prefixWord ++ tailWord_6887212).sum := by decide
  have hdescent : baseEnd_6887212 < baseStart_6887212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887321 : List Nat := [1, 2, 1, 2, 1, 3, 3, 2, 3, 5]
def baseStart_6887321 : Nat := 118140960795 + 6887321 * 2 ^ 59
def prefixEnd_6887321 : Nat := 4983230072969 + 3 ^ 40 * 6887321 * 2
def baseEnd_6887321 : Nat := 1178835364934917686204431

theorem tailTrace_6887321 : CollatzResearch.WordTrace tailWord_6887321 prefixEnd_6887321 1178835364934917686204431 := by
  unfold tailWord_6887321
  simp only [CollatzResearch.WordTrace]
  refine ⟨251201233881419752625005817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167467489254279835083337211 251201233881419752625005817)
  ·
    refine ⟨188400925411064814468754363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251201233881419752625005817 188400925411064814468754363)
    ·
      refine ⟨282601388116597221703131545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188400925411064814468754363 282601388116597221703131545)
      ·
        refine ⟨211951041087447916277348659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282601388116597221703131545 211951041087447916277348659)
        ·
          refine ⟨317926561631171874416022989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211951041087447916277348659 317926561631171874416022989)
          ·
            refine ⟨119222460611689452906008621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317926561631171874416022989 119222460611689452906008621)
            ·
              refine ⟨44708422729383544839753233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119222460611689452906008621 44708422729383544839753233)
              ·
                refine ⟨33531317047037658629814925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44708422729383544839753233 33531317047037658629814925)
                ·
                  refine ⟨12574243892639121986180597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33531317047037658629814925 12574243892639121986180597)
                  ·
                    refine ⟨1178835364934917686204431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12574243892639121986180597 1178835364934917686204431)
                    ·
                      rfl

theorem cell23_6887321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 5].length) (baseStart_6887321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887321 prefixEnd_6887321 := by exact prefixLift 6887321
  have htrace : WordTrace (prefixWord ++ tailWord_6887321) baseStart_6887321 baseEnd_6887321 := by
    simpa [prefixWord, tailWord_6887321, baseEnd_6887321] using wordTrace_append hprefix tailTrace_6887321
  have hstable : (prefixWord ++ tailWord_6887321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887321).length < 2 ^ (prefixWord ++ tailWord_6887321).sum := by decide
  have hdescent : baseEnd_6887321 < baseStart_6887321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887328 : List Nat := [2, 1, 1, 4, 1, 1, 1, 4, 1, 5, 2]
def baseStart_6887328 : Nat := 118140960795 + 6887328 * 2 ^ 59
def prefixEnd_6887328 : Nat := 4983230072969 + 3 ^ 40 * 6887328 * 2
def baseEnd_6887328 : Nat := 3536509689169334531225761

theorem tailTrace_6887328 : CollatzResearch.WordTrace tailWord_6887328 prefixEnd_6887328 3536509689169334531225761 := by
  unfold tailWord_6887328
  simp only [CollatzResearch.WordTrace]
  refine ⟨125600744596197196410255319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167467659461596261880340425 125600744596197196410255319)
  ·
    refine ⟨188401116894295794615382979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125600744596197196410255319 188401116894295794615382979)
    ·
      refine ⟨282601675341443691923074469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188401116894295794615382979 282601675341443691923074469)
      ·
        refine ⟨52987814126520692235576463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 282601675341443691923074469 52987814126520692235576463)
        ·
          refine ⟨79481721189781038353364695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52987814126520692235576463 79481721189781038353364695)
          ·
            refine ⟨119222581784671557530047043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79481721189781038353364695 119222581784671557530047043)
            ·
              refine ⟨178833872677007336295070565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119222581784671557530047043 178833872677007336295070565)
              ·
                refine ⟨33531351126938875555325731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 178833872677007336295070565 33531351126938875555325731)
                ·
                  refine ⟨50297026690408313332988597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33531351126938875555325731 50297026690408313332988597)
                  ·
                    refine ⟨4715346252225779374967681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50297026690408313332988597 4715346252225779374967681)
                    ·
                      refine ⟨3536509689169334531225761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4715346252225779374967681 3536509689169334531225761)
                      ·
                        rfl

theorem cell23_6887328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_6887328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887328 prefixEnd_6887328 := by exact prefixLift 6887328
  have htrace : WordTrace (prefixWord ++ tailWord_6887328) baseStart_6887328 baseEnd_6887328 := by
    simpa [prefixWord, tailWord_6887328, baseEnd_6887328] using wordTrace_append hprefix tailTrace_6887328
  have hstable : (prefixWord ++ tailWord_6887328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887328).length < 2 ^ (prefixWord ++ tailWord_6887328).sum := by decide
  have hdescent : baseEnd_6887328 < baseStart_6887328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887335 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 5, 1, 3]
def baseStart_6887335 : Nat := 118140960795 + 6887335 * 2 ^ 59
def prefixEnd_6887335 : Nat := 4983230072969 + 3 ^ 40 * 6887335 * 2
def baseEnd_6887335 : Nat := 3536513283533916003838229

theorem tailTrace_6887335 : CollatzResearch.WordTrace tailWord_6887335 prefixEnd_6887335 3536513283533916003838229 := by
  unfold tailWord_6887335
  simp only [CollatzResearch.WordTrace]
  refine ⟨251201744503369033016015459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167467829668912688677343639 251201744503369033016015459)
  ·
    refine ⟨376802616755053549524023189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251201744503369033016015459 376802616755053549524023189)
    ·
      refine ⟨17662622660393135133938587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 376802616755053549524023189 17662622660393135133938587)
      ·
        refine ⟨26493933990589702700907881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17662622660393135133938587 26493933990589702700907881)
        ·
          refine ⟨19870450492942277025680911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26493933990589702700907881 19870450492942277025680911)
          ·
            refine ⟨29805675739413415538521367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19870450492942277025680911 29805675739413415538521367)
            ·
              refine ⟨44708513609120123307782051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29805675739413415538521367 44708513609120123307782051)
              ·
                refine ⟨67062770413680184961673077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44708513609120123307782051 67062770413680184961673077)
                ·
                  refine ⟨6287134726282517340156851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67062770413680184961673077 6287134726282517340156851)
                  ·
                    refine ⟨9430702089423776010235277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6287134726282517340156851 9430702089423776010235277)
                    ·
                      refine ⟨3536513283533916003838229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9430702089423776010235277 3536513283533916003838229)
                      ·
                        rfl

theorem cell23_6887335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_6887335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887335 prefixEnd_6887335 := by exact prefixLift 6887335
  have htrace : WordTrace (prefixWord ++ tailWord_6887335) baseStart_6887335 baseEnd_6887335 := by
    simpa [prefixWord, tailWord_6887335, baseEnd_6887335] using wordTrace_append hprefix tailTrace_6887335
  have hstable : (prefixWord ++ tailWord_6887335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887335).length < 2 ^ (prefixWord ++ tailWord_6887335).sum := by decide
  have hdescent : baseEnd_6887335 < baseStart_6887335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887345 : List Nat := [1, 2, 2, 4, 2, 2, 1, 1, 1, 5, 2]
def baseStart_6887345 : Nat := 118140960795 + 6887345 * 2 ^ 59
def prefixEnd_6887345 : Nat := 4983230072969 + 3 ^ 40 * 6887345 * 2
def baseEnd_6887345 : Nat := 3536518418340460964713183

theorem tailTrace_6887345 : CollatzResearch.WordTrace tailWord_6887345 prefixEnd_6887345 3536518418340460964713183 := by
  unfold tailWord_6887345
  simp only [CollatzResearch.WordTrace]
  refine ⟨251202109233332804723879489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167468072822221869815919659 251202109233332804723879489)
  ·
    refine ⟨188401581924999603542909617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251202109233332804723879489 188401581924999603542909617)
    ·
      refine ⟨141301186443749702657182213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188401581924999603542909617 141301186443749702657182213)
      ·
        refine ⟨26493972458203069248221665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141301186443749702657182213 26493972458203069248221665)
        ·
          refine ⟨19870479343652301936166249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26493972458203069248221665 19870479343652301936166249)
          ·
            refine ⟨14902859507739226452124687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19870479343652301936166249 14902859507739226452124687)
            ·
              refine ⟨22354289261608839678187031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14902859507739226452124687 22354289261608839678187031)
              ·
                refine ⟨33531433892413259517280547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22354289261608839678187031 33531433892413259517280547)
                ·
                  refine ⟨50297150838619889275920821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33531433892413259517280547 50297150838619889275920821)
                  ·
                    refine ⟨4715357891120614619617577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50297150838619889275920821 4715357891120614619617577)
                    ·
                      refine ⟨3536518418340460964713183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4715357891120614619617577 3536518418340460964713183)
                      ·
                        rfl

theorem cell23_6887345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_6887345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887345 prefixEnd_6887345 := by exact prefixLift 6887345
  have htrace : WordTrace (prefixWord ++ tailWord_6887345) baseStart_6887345 baseEnd_6887345 := by
    simpa [prefixWord, tailWord_6887345, baseEnd_6887345] using wordTrace_append hprefix tailTrace_6887345
  have hstable : (prefixWord ++ tailWord_6887345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887345).length < 2 ^ (prefixWord ++ tailWord_6887345).sum := by decide
  have hdescent : baseEnd_6887345 < baseStart_6887345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887352 : List Nat := [2, 1, 2, 1, 2, 3, 4, 3, 1, 1, 3]
def baseStart_6887352 : Nat := 118140960795 + 6887352 * 2 ^ 59
def prefixEnd_6887352 : Nat := 4983230072969 + 3 ^ 40 * 6887352 * 2
def baseEnd_6887352 : Nat := 3536522012705042437325651

theorem tailTrace_6887352 : CollatzResearch.WordTrace tailWord_6887352 prefixEnd_6887352 3536522012705042437325651 := by
  unfold tailWord_6887352
  simp only [CollatzResearch.WordTrace]
  refine ⟨125601182272153722459692155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167468243029538296612922873 125601182272153722459692155)
  ·
    refine ⟨188401773408230583689538233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125601182272153722459692155 188401773408230583689538233)
    ·
      refine ⟨141301330056172937767153675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188401773408230583689538233 141301330056172937767153675)
      ·
        refine ⟨211951995084259406650730513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141301330056172937767153675 211951995084259406650730513)
        ·
          refine ⟨158963996313194554988047885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211951995084259406650730513 158963996313194554988047885)
          ·
            refine ⟨59611498617447958120517957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158963996313194554988047885 59611498617447958120517957)
            ·
              refine ⟨11177155990771492147597117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59611498617447958120517957 11177155990771492147597117)
              ·
                refine ⟨4191433496539309555348919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11177155990771492147597117 4191433496539309555348919)
                ·
                  refine ⟨6287150244808964333023379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4191433496539309555348919 6287150244808964333023379)
                  ·
                    refine ⟨9430725367213446499535069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6287150244808964333023379 9430725367213446499535069)
                    ·
                      refine ⟨3536522012705042437325651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9430725367213446499535069 3536522012705042437325651)
                      ·
                        rfl

theorem cell23_6887352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 3, 1, 1, 3].length) (baseStart_6887352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887352 prefixEnd_6887352 := by exact prefixLift 6887352
  have htrace : WordTrace (prefixWord ++ tailWord_6887352) baseStart_6887352 baseEnd_6887352 := by
    simpa [prefixWord, tailWord_6887352, baseEnd_6887352] using wordTrace_append hprefix tailTrace_6887352
  have hstable : (prefixWord ++ tailWord_6887352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887352).length < 2 ^ (prefixWord ++ tailWord_6887352).sum := by decide
  have hdescent : baseEnd_6887352 < baseStart_6887352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887371 : List Nat := [1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 6]
def baseStart_6887371 : Nat := 118140960795 + 6887371 * 2 ^ 59
def prefixEnd_6887371 : Nat := 4983230072969 + 3 ^ 40 * 6887371 * 2
def baseEnd_6887371 : Nat := 3536531768837477862988063

theorem tailTrace_6887371 : CollatzResearch.WordTrace tailWord_6887371 prefixEnd_6887371 3536531768837477862988063 := by
  unfold tailWord_6887371
  simp only [CollatzResearch.WordTrace]
  refine ⟨251203057531238611164325967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167468705020825740776217311 251203057531238611164325967)
  ·
    refine ⟨376804586296857916746488951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251203057531238611164325967 376804586296857916746488951)
    ·
      refine ⟨565206879445286875119733427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376804586296857916746488951 565206879445286875119733427)
      ·
        refine ⟨847810319167930312679600141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565206879445286875119733427 847810319167930312679600141)
        ·
          refine ⟨317928869687973867254850053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 847810319167930312679600141 317928869687973867254850053)
          ·
            refine ⟨59611663066495100110284385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 317928869687973867254850053 59611663066495100110284385)
            ·
              refine ⟨44708747299871325082713289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59611663066495100110284385 44708747299871325082713289)
              ·
                refine ⟨33531560474903493812034967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44708747299871325082713289 33531560474903493812034967)
                ·
                  refine ⟨50297340712355240718052451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33531560474903493812034967 50297340712355240718052451)
                  ·
                    refine ⟨75446011068532861077078677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50297340712355240718052451 75446011068532861077078677)
                    ·
                      refine ⟨3536531768837477862988063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75446011068532861077078677 3536531768837477862988063)
                      ·
                        rfl

theorem cell23_6887371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 6].length) (baseStart_6887371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887371 prefixEnd_6887371 := by exact prefixLift 6887371
  have htrace : WordTrace (prefixWord ++ tailWord_6887371) baseStart_6887371 baseEnd_6887371 := by
    simpa [prefixWord, tailWord_6887371, baseEnd_6887371] using wordTrace_append hprefix tailTrace_6887371
  have hstable : (prefixWord ++ tailWord_6887371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887371).length < 2 ^ (prefixWord ++ tailWord_6887371).sum := by decide
  have hdescent : baseEnd_6887371 < baseStart_6887371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887385 : List Nat := [1, 2, 1, 2, 6, 2, 1, 1, 1, 6]
def baseStart_6887385 : Nat := 118140960795 + 6887385 * 2 ^ 59
def prefixEnd_6887385 : Nat := 4983230072969 + 3 ^ 40 * 6887385 * 2
def baseEnd_6887385 : Nat := 1178846319188880269404333

theorem tailTrace_6887385 : CollatzResearch.WordTrace tailWord_6887385 prefixEnd_6887385 1178846319188880269404333 := by
  unfold tailWord_6887385
  simp only [CollatzResearch.WordTrace]
  refine ⟨251203568153187891555335609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167469045435458594370223739 251203568153187891555335609)
  ·
    refine ⟨188402676114890918666501707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251203568153187891555335609 188402676114890918666501707)
    ·
      refine ⟨282604014172336377999752561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188402676114890918666501707 282604014172336377999752561)
      ·
        refine ⟨211953010629252283499814421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282604014172336377999752561 211953010629252283499814421)
        ·
          refine ⟨9935297373246200789053801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 211953010629252283499814421 9935297373246200789053801)
          ·
            refine ⟨7451473029934650591790351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9935297373246200789053801 7451473029934650591790351)
            ·
              refine ⟨11177209544901975887685527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7451473029934650591790351 11177209544901975887685527)
              ·
                refine ⟨16765814317352963831528291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11177209544901975887685527 16765814317352963831528291)
                ·
                  refine ⟨25148721476029445747292437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16765814317352963831528291 25148721476029445747292437)
                  ·
                    refine ⟨1178846319188880269404333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25148721476029445747292437 1178846319188880269404333)
                    ·
                      rfl

theorem cell23_6887385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 6].length) (baseStart_6887385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887385 prefixEnd_6887385 := by exact prefixLift 6887385
  have htrace : WordTrace (prefixWord ++ tailWord_6887385) baseStart_6887385 baseEnd_6887385 := by
    simpa [prefixWord, tailWord_6887385, baseEnd_6887385] using wordTrace_append hprefix tailTrace_6887385
  have hstable : (prefixWord ++ tailWord_6887385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887385).length < 2 ^ (prefixWord ++ tailWord_6887385).sum := by decide
  have hdescent : baseEnd_6887385 < baseStart_6887385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887395 : List Nat := [1, 1, 1, 6, 1, 2, 1, 4, 1, 2, 3]
def baseStart_6887395 : Nat := 118140960795 + 6887395 * 2 ^ 59
def prefixEnd_6887395 : Nat := 4983230072969 + 3 ^ 40 * 6887395 * 2
def baseEnd_6887395 : Nat := 3536544092373185769087953

theorem tailTrace_6887395 : CollatzResearch.WordTrace tailWord_6887395 prefixEnd_6887395 3536544092373185769087953 := by
  unfold tailWord_6887395
  simp only [CollatzResearch.WordTrace]
  refine ⟨251203932883151663263199639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167469288588767775508799759 251203932883151663263199639)
  ·
    refine ⟨376805899324727494894799459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251203932883151663263199639 376805899324727494894799459)
    ·
      refine ⟨565208848987091242342199189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376805899324727494894799459 565208848987091242342199189)
      ·
        refine ⟨26494164796269901984790587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 565208848987091242342199189 26494164796269901984790587)
        ·
          refine ⟨39741247194404852977185881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26494164796269901984790587 39741247194404852977185881)
          ·
            refine ⟨29805935395803639732889411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39741247194404852977185881 29805935395803639732889411)
            ·
              refine ⟨44708903093705459599334117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29805935395803639732889411 44708903093705459599334117)
              ·
                refine ⟨8382919330069773674875147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44708903093705459599334117 8382919330069773674875147)
                ·
                  refine ⟨12574378995104660512312721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8382919330069773674875147 12574378995104660512312721)
                  ·
                    refine ⟨9430784246328495384234541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12574378995104660512312721 9430784246328495384234541)
                    ·
                      refine ⟨3536544092373185769087953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9430784246328495384234541 3536544092373185769087953)
                      ·
                        rfl

theorem cell23_6887395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_6887395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887395 prefixEnd_6887395 := by exact prefixLift 6887395
  have htrace : WordTrace (prefixWord ++ tailWord_6887395) baseStart_6887395 baseEnd_6887395 := by
    simpa [prefixWord, tailWord_6887395, baseEnd_6887395] using wordTrace_append hprefix tailTrace_6887395
  have hstable : (prefixWord ++ tailWord_6887395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887395).length < 2 ^ (prefixWord ++ tailWord_6887395).sum := by decide
  have hdescent : baseEnd_6887395 < baseStart_6887395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887408 : List Nat := [2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 3]
def baseStart_6887408 : Nat := 118140960795 + 6887408 * 2 ^ 59
def prefixEnd_6887408 : Nat := 4983230072969 + 3 ^ 40 * 6887408 * 2
def baseEnd_6887408 : Nat := 3536550767621694218225393

theorem tailTrace_6887408 : CollatzResearch.WordTrace tailWord_6887408 prefixEnd_6887408 3536550767621694218225393 := by
  unfold tailWord_6887408
  simp only [CollatzResearch.WordTrace]
  refine ⟨125602203516052283241711439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167469604688069710988948585 125602203516052283241711439)
  ·
    refine ⟨188403305274078424862567159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125602203516052283241711439 188403305274078424862567159)
    ·
      refine ⟨282604957911117637293850739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188403305274078424862567159 282604957911117637293850739)
      ·
        refine ⟨423907436866676455940776109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282604957911117637293850739 423907436866676455940776109)
        ·
          refine ⟨158965288825003670977791041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 423907436866676455940776109 158965288825003670977791041)
          ·
            refine ⟨119223966618752753233343281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158965288825003670977791041 119223966618752753233343281)
            ·
              refine ⟨89417974964064564925007461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119223966618752753233343281 89417974964064564925007461)
              ·
                refine ⟨16765870305762105923438899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89417974964064564925007461 16765870305762105923438899)
                ·
                  refine ⟨25148805458643158885158349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16765870305762105923438899 25148805458643158885158349)
                  ·
                    refine ⟨9430802046991184581934381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25148805458643158885158349 9430802046991184581934381)
                    ·
                      refine ⟨3536550767621694218225393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9430802046991184581934381 3536550767621694218225393)
                      ·
                        rfl

theorem cell23_6887408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 3].length) (baseStart_6887408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887408 prefixEnd_6887408 := by exact prefixLift 6887408
  have htrace : WordTrace (prefixWord ++ tailWord_6887408) baseStart_6887408 baseEnd_6887408 := by
    simpa [prefixWord, tailWord_6887408, baseEnd_6887408] using wordTrace_append hprefix tailTrace_6887408
  have hstable : (prefixWord ++ tailWord_6887408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887408).length < 2 ^ (prefixWord ++ tailWord_6887408).sum := by decide
  have hdescent : baseEnd_6887408 < baseStart_6887408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887425 : List Nat := [1, 2, 4, 1, 2, 1, 1, 3, 4, 1, 3]
def baseStart_6887425 : Nat := 118140960795 + 6887425 * 2 ^ 59
def prefixEnd_6887425 : Nat := 4983230072969 + 3 ^ 40 * 6887425 * 2
def baseEnd_6887425 : Nat := 3536559496792820651712815

theorem tailTrace_6887425 : CollatzResearch.WordTrace tailWord_6887425 prefixEnd_6887425 3536559496792820651712815 := by
  unfold tailWord_6887425
  simp only [CollatzResearch.WordTrace]
  refine ⟨251205027073042978386791729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167470018048695318924527819 251205027073042978386791729)
  ·
    refine ⟨188403770304782233790093797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251205027073042978386791729 188403770304782233790093797)
    ·
      refine ⟨35325706932146668835642587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188403770304782233790093797 35325706932146668835642587)
      ·
        refine ⟨52988560398220003253463881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35325706932146668835642587 52988560398220003253463881)
        ·
          refine ⟨39741420298665002440097911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52988560398220003253463881 39741420298665002440097911)
          ·
            refine ⟨59612130447997503660146867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39741420298665002440097911 59612130447997503660146867)
            ·
              refine ⟨89418195671996255490220301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59612130447997503660146867 89418195671996255490220301)
              ·
                refine ⟨33531823376998595808832613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89418195671996255490220301 33531823376998595808832613)
                ·
                  refine ⟨6287216883187236714156115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33531823376998595808832613 6287216883187236714156115)
                  ·
                    refine ⟨9430825324780855071234173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6287216883187236714156115 9430825324780855071234173)
                    ·
                      refine ⟨3536559496792820651712815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9430825324780855071234173 3536559496792820651712815)
                      ·
                        rfl

theorem cell23_6887425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_6887425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887425 prefixEnd_6887425 := by exact prefixLift 6887425
  have htrace : WordTrace (prefixWord ++ tailWord_6887425) baseStart_6887425 baseEnd_6887425 := by
    simpa [prefixWord, tailWord_6887425, baseEnd_6887425] using wordTrace_append hprefix tailTrace_6887425
  have hstable : (prefixWord ++ tailWord_6887425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887425).length < 2 ^ (prefixWord ++ tailWord_6887425).sum := by decide
  have hdescent : baseEnd_6887425 < baseStart_6887425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887435 : List Nat := [1, 1, 1, 1, 6, 1, 2, 2, 3, 3, 2]
def baseStart_6887435 : Nat := 118140960795 + 6887435 * 2 ^ 59
def prefixEnd_6887435 : Nat := 4983230072969 + 3 ^ 40 * 6887435 * 2
def baseEnd_6887435 : Nat := 3536564631599365612587769

theorem tailTrace_6887435 : CollatzResearch.WordTrace tailWord_6887435 prefixEnd_6887435 3536564631599365612587769 := by
  unfold tailWord_6887435
  simp only [CollatzResearch.WordTrace]
  refine ⟨251205391803006750094655759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167470261202004500063103839 251205391803006750094655759)
  ·
    refine ⟨376808087704510125141983639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251205391803006750094655759 376808087704510125141983639)
    ·
      refine ⟨565212131556765187712975459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376808087704510125141983639 565212131556765187712975459)
      ·
        refine ⟨847818197335147781569463189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565212131556765187712975459 847818197335147781569463189)
        ·
          refine ⟨39741478000085052261068587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 847818197335147781569463189 39741478000085052261068587)
          ·
            refine ⟨59612217000127578391602881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39741478000085052261068587 59612217000127578391602881)
            ·
              refine ⟨44709162750095683793702161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59612217000127578391602881 44709162750095683793702161)
              ·
                refine ⟨33531872062571762845276621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44709162750095683793702161 33531872062571762845276621)
                ·
                  refine ⟨12574452023464411066978733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33531872062571762845276621 12574452023464411066978733)
                  ·
                    refine ⟨4715419508799154150117025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12574452023464411066978733 4715419508799154150117025)
                    ·
                      refine ⟨3536564631599365612587769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4715419508799154150117025 3536564631599365612587769)
                      ·
                        rfl

theorem cell23_6887435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 3, 2].length) (baseStart_6887435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887435 prefixEnd_6887435 := by exact prefixLift 6887435
  have htrace : WordTrace (prefixWord ++ tailWord_6887435) baseStart_6887435 baseEnd_6887435 := by
    simpa [prefixWord, tailWord_6887435, baseEnd_6887435] using wordTrace_append hprefix tailTrace_6887435
  have hstable : (prefixWord ++ tailWord_6887435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887435).length < 2 ^ (prefixWord ++ tailWord_6887435).sum := by decide
  have hdescent : baseEnd_6887435 < baseStart_6887435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887452 : List Nat := [2, 2, 3, 1, 3, 2, 1, 1, 3, 3, 2]
def baseStart_6887452 : Nat := 118140960795 + 6887452 * 2 ^ 59
def prefixEnd_6887452 : Nat := 4983230072969 + 3 ^ 40 * 6887452 * 2
def baseEnd_6887452 : Nat := 3536573360770492046075191

theorem tailTrace_6887452 : CollatzResearch.WordTrace tailWord_6887452 prefixEnd_6887452 3536573360770492046075191 := by
  unfold tailWord_6887452
  simp only [CollatzResearch.WordTrace]
  refine ⟨125603005921972580999012305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167470674562630107998683073 125603005921972580999012305)
  ·
    refine ⟨94202254441479435749259229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125603005921972580999012305 94202254441479435749259229)
    ·
      refine ⟨35325845415554788405972211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94202254441479435749259229 35325845415554788405972211)
      ·
        refine ⟨52988768123332182608958317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35325845415554788405972211 52988768123332182608958317)
        ·
          refine ⟨19870788046249568478359369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52988768123332182608958317 19870788046249568478359369)
          ·
            refine ⟨14903091034687176358769527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19870788046249568478359369 14903091034687176358769527)
            ·
              refine ⟨22354636552030764538154291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14903091034687176358769527 22354636552030764538154291)
              ·
                refine ⟨33531954828046146807231437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22354636552030764538154291 33531954828046146807231437)
                ·
                  refine ⟨12574483060517305052711789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33531954828046146807231437 12574483060517305052711789)
                  ·
                    refine ⟨4715431147693989394766921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12574483060517305052711789 4715431147693989394766921)
                    ·
                      refine ⟨3536573360770492046075191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4715431147693989394766921 3536573360770492046075191)
                      ·
                        rfl

theorem cell23_6887452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_6887452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887452 prefixEnd_6887452 := by exact prefixLift 6887452
  have htrace : WordTrace (prefixWord ++ tailWord_6887452) baseStart_6887452 baseEnd_6887452 := by
    simpa [prefixWord, tailWord_6887452, baseEnd_6887452] using wordTrace_append hprefix tailTrace_6887452
  have hstable : (prefixWord ++ tailWord_6887452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887452).length < 2 ^ (prefixWord ++ tailWord_6887452).sum := by decide
  have hdescent : baseEnd_6887452 < baseStart_6887452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887471 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 11]
def baseStart_6887471 : Nat := 118140960795 + 6887471 * 2 ^ 59
def prefixEnd_6887471 : Nat := 4983230072969 + 3 ^ 40 * 6887471 * 2
def baseEnd_6887471 : Nat := 392953679655880830193067

theorem tailTrace_6887471 : CollatzResearch.WordTrace tailWord_6887471 prefixEnd_6887471 392953679655880830193067 := by
  unfold tailWord_6887471
  simp only [CollatzResearch.WordTrace]
  refine ⟨251206704830876328242966267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167471136553917552161977511 251206704830876328242966267)
  ·
    refine ⟨376810057246314492364449401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251206704830876328242966267 376810057246314492364449401)
    ·
      refine ⟨282607542934735869273337051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376810057246314492364449401 282607542934735869273337051)
      ·
        refine ⟨423911314402103803910005577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282607542934735869273337051 423911314402103803910005577)
        ·
          refine ⟨317933485801577852932504183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423911314402103803910005577 317933485801577852932504183)
          ·
            refine ⟨476900228702366779398756275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317933485801577852932504183 476900228702366779398756275)
            ·
              refine ⟨715350343053550169098134413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476900228702366779398756275 715350343053550169098134413)
              ·
                refine ⟨268256378645081313411800405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 715350343053550169098134413 268256378645081313411800405)
                ·
                  refine ⟨392953679655880830193067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 268256378645081313411800405 392953679655880830193067)
                  ·
                    rfl

theorem cell23_6887471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 11].length) (baseStart_6887471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887471 prefixEnd_6887471 := by exact prefixLift 6887471
  have htrace : WordTrace (prefixWord ++ tailWord_6887471) baseStart_6887471 baseEnd_6887471 := by
    simpa [prefixWord, tailWord_6887471, baseEnd_6887471] using wordTrace_append hprefix tailTrace_6887471
  have hstable : (prefixWord ++ tailWord_6887471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887471).length < 2 ^ (prefixWord ++ tailWord_6887471).sum := by decide
  have hdescent : baseEnd_6887471 < baseStart_6887471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887476 : List Nat := [2, 5, 1, 2, 2, 1, 2, 2, 2, 1, 3]
def baseStart_6887476 : Nat := 118140960795 + 6887476 * 2 ^ 59
def prefixEnd_6887476 : Nat := 4983230072969 + 3 ^ 40 * 6887476 * 2
def baseEnd_6887476 : Nat := 3536585684306199952175081

theorem tailTrace_6887476 : CollatzResearch.WordTrace tailWord_6887476 prefixEnd_6887476 3536585684306199952175081 := by
  unfold tailWord_6887476
  simp only [CollatzResearch.WordTrace]
  refine ⟨125603443597929107048449141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167471258130572142731265521 125603443597929107048449141)
  ·
    refine ⟨11775322837305853785792107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125603443597929107048449141 11775322837305853785792107)
    ·
      refine ⟨17662984255958780678688161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11775322837305853785792107 17662984255958780678688161)
      ·
        refine ⟨13247238191969085509016121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17662984255958780678688161 13247238191969085509016121)
        ·
          refine ⟨9935428643976814131762091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13247238191969085509016121 9935428643976814131762091)
          ·
            refine ⟨14903142965965221197643137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9935428643976814131762091 14903142965965221197643137)
            ·
              refine ⟨11177357224473915898232353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14903142965965221197643137 11177357224473915898232353)
              ·
                refine ⟨8383017918355436923674265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11177357224473915898232353 8383017918355436923674265)
                ·
                  refine ⟨6287263438766577692755699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8383017918355436923674265 6287263438766577692755699)
                  ·
                    refine ⟨9430895158149866539133549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6287263438766577692755699 9430895158149866539133549)
                    ·
                      refine ⟨3536585684306199952175081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9430895158149866539133549 3536585684306199952175081)
                      ·
                        rfl

theorem cell23_6887476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_6887476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887476 prefixEnd_6887476 := by exact prefixLift 6887476
  have htrace : WordTrace (prefixWord ++ tailWord_6887476) baseStart_6887476 baseEnd_6887476 := by
    simpa [prefixWord, tailWord_6887476, baseEnd_6887476] using wordTrace_append hprefix tailTrace_6887476
  have hstable : (prefixWord ++ tailWord_6887476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887476).length < 2 ^ (prefixWord ++ tailWord_6887476).sum := by decide
  have hdescent : baseEnd_6887476 < baseStart_6887476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887568 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 4]
def baseStart_6887568 : Nat := 118140960795 + 6887568 * 2 ^ 59
def prefixEnd_6887568 : Nat := 4983230072969 + 3 ^ 40 * 6887568 * 2
def baseEnd_6887568 : Nat := 3536632924526413592224657

theorem tailTrace_6887568 : CollatzResearch.WordTrace tailWord_6887568 prefixEnd_6887568 3536632924526413592224657 := by
  unfold tailWord_6887568
  simp only [CollatzResearch.WordTrace]
  refine ⟨125605121355762456904623679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167473495141016609206164905 125605121355762456904623679)
  ·
    refine ⟨188407682033643685356935519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125605121355762456904623679 188407682033643685356935519)
    ·
      refine ⟨282611523050465528035403279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188407682033643685356935519 282611523050465528035403279)
      ·
        refine ⟨423917284575698292053104919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282611523050465528035403279 423917284575698292053104919)
        ·
          refine ⟨635875926863547438079657379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423917284575698292053104919 635875926863547438079657379)
          ·
            refine ⟨953813890295321157119486069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635875926863547438079657379 953813890295321157119486069)
            ·
              refine ⟨89420052215186358479951819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 953813890295321157119486069 89420052215186358479951819)
              ·
                refine ⟨134130078322779537719927729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89420052215186358479951819 134130078322779537719927729)
                ·
                  refine ⟨100597558742084653289945797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134130078322779537719927729 100597558742084653289945797)
                  ·
                    refine ⟨18862042264140872491864837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100597558742084653289945797 18862042264140872491864837)
                    ·
                      refine ⟨3536632924526413592224657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18862042264140872491864837 3536632924526413592224657)
                      ·
                        rfl

theorem cell23_6887568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 4].length) (baseStart_6887568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887568 prefixEnd_6887568 := by exact prefixLift 6887568
  have htrace : WordTrace (prefixWord ++ tailWord_6887568) baseStart_6887568 baseEnd_6887568 := by
    simpa [prefixWord, tailWord_6887568, baseEnd_6887568] using wordTrace_append hprefix tailTrace_6887568
  have hstable : (prefixWord ++ tailWord_6887568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887568).length < 2 ^ (prefixWord ++ tailWord_6887568).sum := by decide
  have hdescent : baseEnd_6887568 < baseStart_6887568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887612 : List Nat := [2, 2, 2, 3, 3, 1, 1, 3, 6]
def baseStart_6887612 : Nat := 118140960795 + 6887612 * 2 ^ 59
def prefixEnd_6887612 : Nat := 4983230072969 + 3 ^ 40 * 6887612 * 2
def baseEnd_6887612 : Nat := 392961724186134602230495

theorem tailTrace_6887612 : CollatzResearch.WordTrace tailWord_6887612 prefixEnd_6887612 392961724186134602230495 := by
  unfold tailWord_6887612
  simp only [CollatzResearch.WordTrace]
  refine ⟨125605923761682754661924545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167474565015577006215899393 125605923761682754661924545)
  ·
    refine ⟨94204442821262065996443409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125605923761682754661924545 94204442821262065996443409)
    ·
      refine ⟨70653332115946549497332557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94204442821262065996443409 70653332115946549497332557)
      ·
        refine ⟨26494999543479956061499709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70653332115946549497332557 26494999543479956061499709)
        ·
          refine ⟨9935624828804983523062391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26494999543479956061499709 9935624828804983523062391)
          ·
            refine ⟨14903437243207475284593587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9935624828804983523062391 14903437243207475284593587)
            ·
              refine ⟨22355155864811212926890381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14903437243207475284593587 22355155864811212926890381)
              ·
                refine ⟨8383183449304204847583893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22355155864811212926890381 8383183449304204847583893)
                ·
                  refine ⟨392961724186134602230495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8383183449304204847583893 392961724186134602230495)
                  ·
                    rfl

theorem cell23_6887612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 6].length) (baseStart_6887612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887612 prefixEnd_6887612 := by exact prefixLift 6887612
  have htrace : WordTrace (prefixWord ++ tailWord_6887612) baseStart_6887612 baseEnd_6887612 := by
    simpa [prefixWord, tailWord_6887612, baseEnd_6887612] using wordTrace_append hprefix tailTrace_6887612
  have hstable : (prefixWord ++ tailWord_6887612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887612).length < 2 ^ (prefixWord ++ tailWord_6887612).sum := by decide
  have hdescent : baseEnd_6887612 < baseStart_6887612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887625 : List Nat := [1, 2, 1, 1, 2, 1, 1, 8, 1, 5]
def baseStart_6887625 : Nat := 118140960795 + 6887625 * 2 ^ 59
def prefixEnd_6887625 : Nat := 4983230072969 + 3 ^ 40 * 6887625 * 2
def baseEnd_6887625 : Nat := 1178887397641239956403965

theorem tailTrace_6887625 : CollatzResearch.WordTrace tailWord_6887625 prefixEnd_6887625 1178887397641239956403965 := by
  unfold tailWord_6887625
  simp only [CollatzResearch.WordTrace]
  refine ⟨251212321672318412544072329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167474881114878941696048219 251212321672318412544072329)
  ·
    refine ⟨188409241254238809408054247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251212321672318412544072329 188409241254238809408054247)
    ·
      refine ⟨282613861881358214112081371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188409241254238809408054247 282613861881358214112081371)
      ·
        refine ⟨423920792822037321168122057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282613861881358214112081371 423920792822037321168122057)
        ·
          refine ⟨317940594616527990876091543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423920792822037321168122057 317940594616527990876091543)
          ·
            refine ⟨476910891924791986314137315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317940594616527990876091543 476910891924791986314137315)
            ·
              refine ⟨715366337887187979471205973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476910891924791986314137315 715366337887187979471205973)
              ·
                refine ⟨8383199272115484134428195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 715366337887187979471205973 8383199272115484134428195)
                ·
                  refine ⟨12574798908173226201642293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8383199272115484134428195 12574798908173226201642293)
                  ·
                    refine ⟨1178887397641239956403965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12574798908173226201642293 1178887397641239956403965)
                    ·
                      rfl

theorem cell23_6887625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 5].length) (baseStart_6887625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887625 prefixEnd_6887625 := by exact prefixLift 6887625
  have htrace : WordTrace (prefixWord ++ tailWord_6887625) baseStart_6887625 baseEnd_6887625 := by
    simpa [prefixWord, tailWord_6887625, baseEnd_6887625] using wordTrace_append hprefix tailTrace_6887625
  have hstable : (prefixWord ++ tailWord_6887625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887625).length < 2 ^ (prefixWord ++ tailWord_6887625).sum := by decide
  have hdescent : baseEnd_6887625 < baseStart_6887625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887639 : List Nat := [1, 1, 3, 2, 1, 2, 1, 7, 1, 1, 3]
def baseStart_6887639 : Nat := 118140960795 + 6887639 * 2 ^ 59
def prefixEnd_6887639 : Nat := 4983230072969 + 3 ^ 40 * 6887639 * 2
def baseEnd_6887639 : Nat := 3536669381652882814436831

theorem tailTrace_6887639 : CollatzResearch.WordTrace tailWord_6887639 prefixEnd_6887639 3536669381652882814436831 := by
  unfold tailWord_6887639
  simp only [CollatzResearch.WordTrace]
  refine ⟨251212832294267692935081971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167475221529511795290054647 251212832294267692935081971)
  ·
    refine ⟨376819248441401539402622957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251212832294267692935081971 376819248441401539402622957)
    ·
      refine ⟨141307218165525577275983609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 376819248441401539402622957 141307218165525577275983609)
      ·
        refine ⟨105980413624144182956987707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141307218165525577275983609 105980413624144182956987707)
        ·
          refine ⟨158970620436216274435481561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105980413624144182956987707 158970620436216274435481561)
          ·
            refine ⟨119227965327162205826611171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158970620436216274435481561 119227965327162205826611171)
            ·
              refine ⟨178841947990743308739916757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119227965327162205826611171 178841947990743308739916757)
              ·
                refine ⟨4191608156033046298591799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 178841947990743308739916757 4191608156033046298591799)
                ·
                  refine ⟨6287412234049569447887699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4191608156033046298591799 6287412234049569447887699)
                  ·
                    refine ⟨9431118351074354171831549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6287412234049569447887699 9431118351074354171831549)
                    ·
                      refine ⟨3536669381652882814436831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9431118351074354171831549 3536669381652882814436831)
                      ·
                        rfl

theorem cell23_6887639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 7, 1, 1, 3].length) (baseStart_6887639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887639 prefixEnd_6887639 := by exact prefixLift 6887639
  have htrace : WordTrace (prefixWord ++ tailWord_6887639) baseStart_6887639 baseEnd_6887639 := by
    simpa [prefixWord, tailWord_6887639, baseEnd_6887639] using wordTrace_append hprefix tailTrace_6887639
  have hstable : (prefixWord ++ tailWord_6887639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887639).length < 2 ^ (prefixWord ++ tailWord_6887639).sum := by decide
  have hdescent : baseEnd_6887639 < baseStart_6887639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887650 : List Nat := [3, 3, 4, 1, 1, 1, 1, 4, 1, 4]
def baseStart_6887650 : Nat := 118140960795 + 6887650 * 2 ^ 59
def prefixEnd_6887650 : Nat := 4983230072969 + 3 ^ 40 * 6887650 * 2
def baseEnd_6887650 : Nat := 1178891676646694090466427

theorem tailTrace_6887650 : CollatzResearch.WordTrace tailWord_6887650 prefixEnd_6887650 1178891676646694090466427 := by
  unfold tailWord_6887650
  simp only [CollatzResearch.WordTrace]
  refine ⟨62803308374306960453433101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167475488998151894542488269 62803308374306960453433101)
  ·
    refine ⟨23551240640365110170037413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62803308374306960453433101 23551240640365110170037413)
    ·
      refine ⟨4415857620068458156882015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23551240640365110170037413 4415857620068458156882015)
      ·
        refine ⟨6623786430102687235323023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4415857620068458156882015 6623786430102687235323023)
        ·
          refine ⟨9935679645154030852984535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6623786430102687235323023 9935679645154030852984535)
          ·
            refine ⟨14903519467731046279476803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9935679645154030852984535 14903519467731046279476803)
            ·
              refine ⟨22355279201596569419215205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14903519467731046279476803 22355279201596569419215205)
              ·
                refine ⟨4191614850299356766102851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22355279201596569419215205 4191614850299356766102851)
                ·
                  refine ⟨6287422275449035149154277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4191614850299356766102851 6287422275449035149154277)
                  ·
                    refine ⟨1178891676646694090466427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6287422275449035149154277 1178891676646694090466427)
                    ·
                      rfl

theorem cell23_6887650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_6887650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887650 prefixEnd_6887650 := by exact prefixLift 6887650
  have htrace : WordTrace (prefixWord ++ tailWord_6887650) baseStart_6887650 baseEnd_6887650 := by
    simpa [prefixWord, tailWord_6887650, baseEnd_6887650] using wordTrace_append hprefix tailTrace_6887650
  have hstable : (prefixWord ++ tailWord_6887650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887650).length < 2 ^ (prefixWord ++ tailWord_6887650).sum := by decide
  have hdescent : baseEnd_6887650 < baseStart_6887650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887656 : List Nat := [2, 1, 4, 1, 2, 3, 1, 4, 1, 1, 3]
def baseStart_6887656 : Nat := 118140960795 + 6887656 * 2 ^ 59
def prefixEnd_6887656 : Nat := 4983230072969 + 3 ^ 40 * 6887656 * 2
def baseEnd_6887656 : Nat := 3536678110824009247924253

theorem tailTrace_6887656 : CollatzResearch.WordTrace tailWord_6887656 prefixEnd_6887656 3536678110824009247924253 := by
  unfold tailWord_6887656
  simp only [CollatzResearch.WordTrace]
  refine ⟨125606726167603052419225411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167475634890137403225633881 125606726167603052419225411)
  ·
    refine ⟨188410089251404578628838117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125606726167603052419225411 188410089251404578628838117)
    ·
      refine ⟨35326891734638358492907147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188410089251404578628838117 35326891734638358492907147)
      ·
        refine ⟨52990337601957537739360721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35326891734638358492907147 52990337601957537739360721)
        ·
          refine ⟨39742753201468153304520541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52990337601957537739360721 39742753201468153304520541)
          ·
            refine ⟨14903532450550557489195203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39742753201468153304520541 14903532450550557489195203)
            ·
              refine ⟨22355298675825836233792805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14903532450550557489195203 22355298675825836233792805)
              ·
                refine ⟨4191618501717344293836151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22355298675825836233792805 4191618501717344293836151)
                ·
                  refine ⟨6287427752576016440754227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4191618501717344293836151 6287427752576016440754227)
                  ·
                    refine ⟨9431141628864024661131341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6287427752576016440754227 9431141628864024661131341)
                    ·
                      refine ⟨3536678110824009247924253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9431141628864024661131341 3536678110824009247924253)
                      ·
                        rfl

theorem cell23_6887656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_6887656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887656 prefixEnd_6887656 := by exact prefixLift 6887656
  have htrace : WordTrace (prefixWord ++ tailWord_6887656) baseStart_6887656 baseEnd_6887656 := by
    simpa [prefixWord, tailWord_6887656, baseEnd_6887656] using wordTrace_append hprefix tailTrace_6887656
  have hstable : (prefixWord ++ tailWord_6887656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887656).length < 2 ^ (prefixWord ++ tailWord_6887656).sum := by decide
  have hdescent : baseEnd_6887656 < baseStart_6887656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887662 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 2, 6, 2]
def baseStart_6887662 : Nat := 118140960795 + 6887662 * 2 ^ 59
def prefixEnd_6887662 : Nat := 4983230072969 + 3 ^ 40 * 6887662 * 2
def baseEnd_6887662 : Nat := 3536681191707936224449225

theorem tailTrace_6887662 : CollatzResearch.WordTrace tailWord_6887662 prefixEnd_6887662 3536681191707936224449225 := by
  unfold tailWord_6887662
  simp only [CollatzResearch.WordTrace]
  refine ⟨31401708896648045982896155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167475780782122911908779493 31401708896648045982896155)
  ·
    refine ⟨47102563344972068974344233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31401708896648045982896155 47102563344972068974344233)
    ·
      refine ⟨35326922508729051730758175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47102563344972068974344233 35326922508729051730758175)
      ·
        refine ⟨52990383763093577596137263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35326922508729051730758175 52990383763093577596137263)
        ·
          refine ⟨79485575644640366394205895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52990383763093577596137263 79485575644640366394205895)
          ·
            refine ⟨119228363466960549591308843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79485575644640366394205895 119228363466960549591308843)
            ·
              refine ⟨178842545200440824386963265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119228363466960549591308843 178842545200440824386963265)
              ·
                refine ⟨134131908900330618290222449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178842545200440824386963265 134131908900330618290222449)
                ·
                  refine ⟨100598931675247963717666837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134131908900330618290222449 100598931675247963717666837)
                  ·
                    refine ⟨4715574922277248299265633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100598931675247963717666837 4715574922277248299265633)
                    ·
                      refine ⟨3536681191707936224449225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4715574922277248299265633 3536681191707936224449225)
                      ·
                        rfl

theorem cell23_6887662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_6887662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887662 prefixEnd_6887662 := by exact prefixLift 6887662
  have htrace : WordTrace (prefixWord ++ tailWord_6887662) baseStart_6887662 baseEnd_6887662 := by
    simpa [prefixWord, tailWord_6887662, baseEnd_6887662] using wordTrace_append hprefix tailTrace_6887662
  have hstable : (prefixWord ++ tailWord_6887662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887662).length < 2 ^ (prefixWord ++ tailWord_6887662).sum := by decide
  have hdescent : baseEnd_6887662 < baseStart_6887662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887665 : List Nat := [1, 2, 2, 2, 2, 1, 2, 4, 1, 1, 5]
def baseStart_6887665 : Nat := 118140960795 + 6887665 * 2 ^ 59
def prefixEnd_6887665 : Nat := 4983230072969 + 3 ^ 40 * 6887665 * 2
def baseEnd_6887665 : Nat := 3536682732149899712711711

theorem tailTrace_6887665 : CollatzResearch.WordTrace tailWord_6887665 prefixEnd_6887665 3536682732149899712711711 := by
  unfold tailWord_6887665
  simp only [CollatzResearch.WordTrace]
  refine ⟨251213780592173499375528449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167475853728115666250352299 251213780592173499375528449)
  ·
    refine ⟨188410335444130124531646337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251213780592173499375528449 188410335444130124531646337)
    ·
      refine ⟨141307751583097593398734753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188410335444130124531646337 141307751583097593398734753)
      ·
        refine ⟨105980813687323195049051065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141307751583097593398734753 105980813687323195049051065)
        ·
          refine ⟨79485610265492396286788299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105980813687323195049051065 79485610265492396286788299)
          ·
            refine ⟨119228415398238594430182449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79485610265492396286788299 119228415398238594430182449)
            ·
              refine ⟨89421311548678945822636837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119228415398238594430182449 89421311548678945822636837)
              ·
                refine ⟨16766495915377302341744407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89421311548678945822636837 16766495915377302341744407)
                ·
                  refine ⟨25149743873065953512616611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16766495915377302341744407 25149743873065953512616611)
                  ·
                    refine ⟨37724615809598930268924917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25149743873065953512616611 37724615809598930268924917)
                    ·
                      refine ⟨3536682732149899712711711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37724615809598930268924917 3536682732149899712711711)
                      ·
                        rfl

theorem cell23_6887665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_6887665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887665 prefixEnd_6887665 := by exact prefixLift 6887665
  have htrace : WordTrace (prefixWord ++ tailWord_6887665) baseStart_6887665 baseEnd_6887665 := by
    simpa [prefixWord, tailWord_6887665, baseEnd_6887665] using wordTrace_append hprefix tailTrace_6887665
  have hstable : (prefixWord ++ tailWord_6887665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887665).length < 2 ^ (prefixWord ++ tailWord_6887665).sum := by decide
  have hdescent : baseEnd_6887665 < baseStart_6887665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887679 : List Nat := [1, 1, 2, 2, 1, 4, 3, 2, 3, 2, 2]
def baseStart_6887679 : Nat := 118140960795 + 6887679 * 2 ^ 59
def prefixEnd_6887679 : Nat := 4983230072969 + 3 ^ 40 * 6887679 * 2
def baseEnd_6887679 : Nat := 3536689920879062657936647

theorem tailTrace_6887679 : CollatzResearch.WordTrace tailWord_6887679 prefixEnd_6887679 3536689920879062657936647 := by
  unfold tailWord_6887679
  simp only [CollatzResearch.WordTrace]
  refine ⟨251214291214122779766538091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167476194142748519844358727 251214291214122779766538091)
  ·
    refine ⟨376821436821184169649807137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251214291214122779766538091 376821436821184169649807137)
    ·
      refine ⟨282616077615888127237355353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376821436821184169649807137 282616077615888127237355353)
      ·
        refine ⟨211962058211916095428016515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282616077615888127237355353 211962058211916095428016515)
        ·
          refine ⟨317943087317874143142024773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211962058211916095428016515 317943087317874143142024773)
          ·
            refine ⟨59614328872101401839129645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 317943087317874143142024773 59614328872101401839129645)
            ·
              refine ⟨22355373327038025689673617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59614328872101401839129645 22355373327038025689673617)
              ·
                refine ⟨16766529995278519267255213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22355373327038025689673617 16766529995278519267255213)
                ·
                  refine ⟨6287448748229444725220705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16766529995278519267255213 6287448748229444725220705)
                  ·
                    refine ⟨4715586561172083543915529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6287448748229444725220705 4715586561172083543915529)
                    ·
                      refine ⟨3536689920879062657936647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4715586561172083543915529 3536689920879062657936647)
                      ·
                        rfl

theorem cell23_6887679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 3, 2, 2].length) (baseStart_6887679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887679 prefixEnd_6887679 := by exact prefixLift 6887679
  have htrace : WordTrace (prefixWord ++ tailWord_6887679) baseStart_6887679 baseEnd_6887679 := by
    simpa [prefixWord, tailWord_6887679, baseEnd_6887679] using wordTrace_append hprefix tailTrace_6887679
  have hstable : (prefixWord ++ tailWord_6887679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887679).length < 2 ^ (prefixWord ++ tailWord_6887679).sum := by decide
  have hdescent : baseEnd_6887679 < baseStart_6887679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887706 : List Nat := [3, 1, 1, 3, 4, 2, 1, 2, 2, 4]
def baseStart_6887706 : Nat := 118140960795 + 6887706 * 2 ^ 59
def prefixEnd_6887706 : Nat := 4983230072969 + 3 ^ 40 * 6887706 * 2
def baseEnd_6887706 : Nat := 1178901261618911350766341

theorem tailTrace_6887706 : CollatzResearch.WordTrace tailWord_6887706 prefixEnd_6887706 1178901261618911350766341 := by
  unfold tailWord_6887706
  simp only [CollatzResearch.WordTrace]
  refine ⟨62803818996256240844442743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167476850656683308918513981 62803818996256240844442743)
  ·
    refine ⟨94205728494384361266664115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62803818996256240844442743 94205728494384361266664115)
    ·
      refine ⟨141308592741576541899996173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94205728494384361266664115 141308592741576541899996173)
      ·
        refine ⟨52990722278091203212498565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141308592741576541899996173 52990722278091203212498565)
        ·
          refine ⟨9935760427142100602343481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52990722278091203212498565 9935760427142100602343481)
          ·
            refine ⟨7451820320356575451757611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9935760427142100602343481 7451820320356575451757611)
            ·
              refine ⟨11177730480534863177636417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7451820320356575451757611 11177730480534863177636417)
              ·
                refine ⟨8383297860401147383227313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11177730480534863177636417 8383297860401147383227313)
                ·
                  refine ⟨6287473395300860537420485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8383297860401147383227313 6287473395300860537420485)
                  ·
                    refine ⟨1178901261618911350766341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6287473395300860537420485 1178901261618911350766341)
                    ·
                      rfl

theorem cell23_6887706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 2, 4].length) (baseStart_6887706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887706 prefixEnd_6887706 := by exact prefixLift 6887706
  have htrace : WordTrace (prefixWord ++ tailWord_6887706) baseStart_6887706 baseEnd_6887706 := by
    simpa [prefixWord, tailWord_6887706, baseEnd_6887706] using wordTrace_append hprefix tailTrace_6887706
  have hstable : (prefixWord ++ tailWord_6887706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887706).length < 2 ^ (prefixWord ++ tailWord_6887706).sum := by decide
  have hdescent : baseEnd_6887706 < baseStart_6887706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887735 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 4]
def baseStart_6887735 : Nat := 118140960795 + 6887735 * 2 ^ 59
def prefixEnd_6887735 : Nat := 4983230072969 + 3 ^ 40 * 6887735 * 2
def baseEnd_6887735 : Nat := 3536718675795714438836389

theorem tailTrace_6887735 : CollatzResearch.WordTrace tailWord_6887735 prefixEnd_6887735 3536718675795714438836389 := by
  unfold tailWord_6887735
  simp only [CollatzResearch.WordTrace]
  refine ⟨251216333701919901330576659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167477555801279934220384439 251216333701919901330576659)
  ·
    refine ⟨376824500552879851995864989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251216333701919901330576659 376824500552879851995864989)
    ·
      refine ⟨141309187707329944498449371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 376824500552879851995864989 141309187707329944498449371)
      ·
        refine ⟨211963781560994916747674057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141309187707329944498449371 211963781560994916747674057)
        ·
          refine ⟨158972836170746187560755543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211963781560994916747674057 158972836170746187560755543)
          ·
            refine ⟨238459254256119281341133315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158972836170746187560755543 238459254256119281341133315)
            ·
              refine ⟨357688881384178922011699973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238459254256119281341133315 357688881384178922011699973)
              ·
                refine ⟨67066665259533547877193745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 357688881384178922011699973 67066665259533547877193745)
                ·
                  refine ⟨50299998944650160907895309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67066665259533547877193745 50299998944650160907895309)
                  ·
                    refine ⟨18862499604243810340460741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50299998944650160907895309 18862499604243810340460741)
                    ·
                      refine ⟨3536718675795714438836389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18862499604243810340460741 3536718675795714438836389)
                      ·
                        rfl

theorem cell23_6887735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_6887735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887735 prefixEnd_6887735 := by exact prefixLift 6887735
  have htrace : WordTrace (prefixWord ++ tailWord_6887735) baseStart_6887735 baseEnd_6887735 := by
    simpa [prefixWord, tailWord_6887735, baseEnd_6887735] using wordTrace_append hprefix tailTrace_6887735
  have hstable : (prefixWord ++ tailWord_6887735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887735).length < 2 ^ (prefixWord ++ tailWord_6887735).sum := by decide
  have hdescent : baseEnd_6887735 < baseStart_6887735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887742 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 2, 2, 5]
def baseStart_6887742 : Nat := 118140960795 + 6887742 * 2 ^ 59
def prefixEnd_6887742 : Nat := 4983230072969 + 3 ^ 40 * 6887742 * 2
def baseEnd_6887742 : Nat := 3536722270160295911448857

theorem tailTrace_6887742 : CollatzResearch.WordTrace tailWord_6887742 prefixEnd_6887742 3536722270160295911448857 := by
  unfold tailWord_6887742
  simp only [CollatzResearch.WordTrace]
  refine ⟨31402073626611817690760185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167477726008596361017387653 31402073626611817690760185)
  ·
    refine ⟨23551555219958863268070139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31402073626611817690760185 23551555219958863268070139)
    ·
      refine ⟨35327332829938294902105209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23551555219958863268070139 35327332829938294902105209)
      ·
        refine ⟨26495499622453721176578907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35327332829938294902105209 26495499622453721176578907)
        ·
          refine ⟨39743249433680581764868361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26495499622453721176578907 39743249433680581764868361)
          ·
            refine ⟨29807437075260436323651271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39743249433680581764868361 29807437075260436323651271)
            ·
              refine ⟨44711155612890654485476907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29807437075260436323651271 44711155612890654485476907)
              ·
                refine ⟨67066733419335981728215361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44711155612890654485476907 67066733419335981728215361)
                ·
                  refine ⟨50300050064501986296161521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67066733419335981728215361 50300050064501986296161521)
                  ·
                    refine ⟨37725037548376489722121141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50300050064501986296161521 37725037548376489722121141)
                    ·
                      refine ⟨3536722270160295911448857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37725037548376489722121141 3536722270160295911448857)
                      ·
                        rfl

theorem cell23_6887742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_6887742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887742 prefixEnd_6887742 := by exact prefixLift 6887742
  have htrace : WordTrace (prefixWord ++ tailWord_6887742) baseStart_6887742 baseEnd_6887742 := by
    simpa [prefixWord, tailWord_6887742, baseEnd_6887742] using wordTrace_append hprefix tailTrace_6887742
  have hstable : (prefixWord ++ tailWord_6887742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887742).length < 2 ^ (prefixWord ++ tailWord_6887742).sum := by decide
  have hdescent : baseEnd_6887742 < baseStart_6887742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887774 : List Nat := [4, 4, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_6887774 : Nat := 118140960795 + 6887774 * 2 ^ 59
def prefixEnd_6887774 : Nat := 4983230072969 + 3 ^ 40 * 6887774 * 2
def baseEnd_6887774 : Nat := 1178912900513746595416237

theorem tailTrace_6887774 : CollatzResearch.WordTrace tailWord_6887774 prefixEnd_6887774 1178912900513746595416237 := by
  unfold tailWord_6887774
  simp only [CollatzResearch.WordTrace]
  refine ⟨31402219518597326373905797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167478504099185740660830917 31402219518597326373905797)
  ·
    refine ⟨5887916159736998695107337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31402219518597326373905797 5887916159736998695107337)
    ·
      refine ⟨4415937119802749021330503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5887916159736998695107337 4415937119802749021330503)
      ·
        refine ⟨6623905679704123531995755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4415937119802749021330503 6623905679704123531995755)
        ·
          refine ⟨9935858519556185297993633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6623905679704123531995755 9935858519556185297993633)
          ·
            refine ⟨7451893889667138973495225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9935858519556185297993633 7451893889667138973495225)
            ·
              refine ⟨5588920417250354230121419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7451893889667138973495225 5588920417250354230121419)
              ·
                refine ⟨8383380625875531345182129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5588920417250354230121419 8383380625875531345182129)
                ·
                  refine ⟨6287535469406648508886597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8383380625875531345182129 6287535469406648508886597)
                  ·
                    refine ⟨1178912900513746595416237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6287535469406648508886597 1178912900513746595416237)
                    ·
                      rfl

theorem cell23_6887774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_6887774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887774 prefixEnd_6887774 := by exact prefixLift 6887774
  have htrace : WordTrace (prefixWord ++ tailWord_6887774) baseStart_6887774 baseEnd_6887774 := by
    simpa [prefixWord, tailWord_6887774, baseEnd_6887774] using wordTrace_append hprefix tailTrace_6887774
  have hstable : (prefixWord ++ tailWord_6887774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887774).length < 2 ^ (prefixWord ++ tailWord_6887774).sum := by decide
  have hdescent : baseEnd_6887774 < baseStart_6887774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887825 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 8]
def baseStart_6887825 : Nat := 118140960795 + 6887825 * 2 ^ 59
def prefixEnd_6887825 : Nat := 4983230072969 + 3 ^ 40 * 6887825 * 2
def baseEnd_6887825 : Nat := 3536764889054619086710975

theorem tailTrace_6887825 : CollatzResearch.WordTrace tailWord_6887825 prefixEnd_6887825 3536764889054619086710975 := by
  unfold tailWord_6887825
  simp only [CollatzResearch.WordTrace]
  refine ⟨251219616271593846701352929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167479744181062564467568619 251219616271593846701352929)
  ·
    refine ⟨188414712203695385026014697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251219616271593846701352929 188414712203695385026014697)
    ·
      refine ⟨141311034152771538769511023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188414712203695385026014697 141311034152771538769511023)
      ·
        refine ⟨211966551229157308154266535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141311034152771538769511023 211966551229157308154266535)
        ·
          refine ⟨317949826843735962231399803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211966551229157308154266535 317949826843735962231399803)
          ·
            refine ⟨476924740265603943347099705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317949826843735962231399803 476924740265603943347099705)
            ·
              refine ⟨357693555199202957510324779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 476924740265603943347099705 357693555199202957510324779)
              ·
                refine ⟨536540332798804436265487169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357693555199202957510324779 536540332798804436265487169)
                ·
                  refine ⟨402405249599103327199115377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 536540332798804436265487169 402405249599103327199115377)
                  ·
                    refine ⟨301803937199327495399336533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 402405249599103327199115377 301803937199327495399336533)
                    ·
                      refine ⟨3536764889054619086710975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 301803937199327495399336533 3536764889054619086710975)
                      ·
                        rfl

theorem cell23_6887825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_6887825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887825 prefixEnd_6887825 := by exact prefixLift 6887825
  have htrace : WordTrace (prefixWord ++ tailWord_6887825) baseStart_6887825 baseEnd_6887825 := by
    simpa [prefixWord, tailWord_6887825, baseEnd_6887825] using wordTrace_append hprefix tailTrace_6887825
  have hstable : (prefixWord ++ tailWord_6887825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887825).length < 2 ^ (prefixWord ++ tailWord_6887825).sum := by decide
  have hdescent : baseEnd_6887825 < baseStart_6887825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887860 : List Nat := [2, 5, 2, 2, 1, 1, 2, 3, 5]
def baseStart_6887860 : Nat := 118140960795 + 6887860 * 2 ^ 59
def prefixEnd_6887860 : Nat := 4983230072969 + 3 ^ 40 * 6887860 * 2
def baseEnd_6887860 : Nat := 392975873430836272197035

theorem tailTrace_6887860 : CollatzResearch.WordTrace tailWord_6887860 prefixEnd_6887860 392975873430836272197035 := by
  unfold tailWord_6887860
  simp only [CollatzResearch.WordTrace]
  refine ⟨125610446413233523839438517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167480595217644698452584689 125610446413233523839438517)
  ·
    refine ⟨11775979351240642859947361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125610446413233523839438517 11775979351240642859947361)
    ·
      refine ⟨8831984513430482144960521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11775979351240642859947361 8831984513430482144960521)
      ·
        refine ⟨6623988385072861608720391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8831984513430482144960521 6623988385072861608720391)
        ·
          refine ⟨9935982577609292413080587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6623988385072861608720391 9935982577609292413080587)
          ·
            refine ⟨14903973866413938619620881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9935982577609292413080587 14903973866413938619620881)
            ·
              refine ⟨11177980399810453964715661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14903973866413938619620881 11177980399810453964715661)
              ·
                refine ⟨4191742649928920236768373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11177980399810453964715661 4191742649928920236768373)
                ·
                  refine ⟨392975873430836272197035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4191742649928920236768373 392975873430836272197035)
                  ·
                    rfl

theorem cell23_6887860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_6887860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887860 prefixEnd_6887860 := by exact prefixLift 6887860
  have htrace : WordTrace (prefixWord ++ tailWord_6887860) baseStart_6887860 baseEnd_6887860 := by
    simpa [prefixWord, tailWord_6887860, baseEnd_6887860] using wordTrace_append hprefix tailTrace_6887860
  have hstable : (prefixWord ++ tailWord_6887860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887860).length < 2 ^ (prefixWord ++ tailWord_6887860).sum := by decide
  have hdescent : baseEnd_6887860 < baseStart_6887860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887882 : List Nat := [3, 1, 2, 1, 2, 2, 3, 1, 8]
def baseStart_6887882 : Nat := 118140960795 + 6887882 * 2 ^ 59
def prefixEnd_6887882 : Nat := 4983230072969 + 3 ^ 40 * 6887882 * 2
def baseEnd_6887882 : Nat := 392977128605769484855357

theorem tailTrace_6887882 : CollatzResearch.WordTrace tailWord_6887882 prefixEnd_6887882 392977128605769484855357 := by
  unfold tailWord_6887882
  simp only [CollatzResearch.WordTrace]
  refine ⟨62805423808096836359044475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167481130154924896957451933 62805423808096836359044475)
  ·
    refine ⟨94208135712145254538566713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62805423808096836359044475 94208135712145254538566713)
    ·
      refine ⟨70656101784108940903925035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94208135712145254538566713 70656101784108940903925035)
      ·
        refine ⟨105984152676163411355887553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70656101784108940903925035 105984152676163411355887553)
        ·
          refine ⟨79488114507122558516915665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105984152676163411355887553 79488114507122558516915665)
          ·
            refine ⟨59616085880341918887686749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79488114507122558516915665 59616085880341918887686749)
            ·
              refine ⟨22356032205128219582882531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59616085880341918887686749 22356032205128219582882531)
              ·
                refine ⟨33534048307692329374323797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22356032205128219582882531 33534048307692329374323797)
                ·
                  refine ⟨392977128605769484855357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33534048307692329374323797 392977128605769484855357)
                  ·
                    rfl

theorem cell23_6887882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 8].length) (baseStart_6887882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887882 prefixEnd_6887882 := by exact prefixLift 6887882
  have htrace : WordTrace (prefixWord ++ tailWord_6887882) baseStart_6887882 baseEnd_6887882 := by
    simpa [prefixWord, tailWord_6887882, baseEnd_6887882] using wordTrace_append hprefix tailTrace_6887882
  have hstable : (prefixWord ++ tailWord_6887882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887882).length < 2 ^ (prefixWord ++ tailWord_6887882).sum := by decide
  have hdescent : baseEnd_6887882 < baseStart_6887882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887929 : List Nat := [1, 2, 1, 3, 1, 2, 4, 3, 1, 5]
def baseStart_6887929 : Nat := 118140960795 + 6887929 * 2 ^ 59
def prefixEnd_6887929 : Nat := 4983230072969 + 3 ^ 40 * 6887929 * 2
def baseEnd_6887929 : Nat := 1178939430347562226603499

theorem tailTrace_6887929 : CollatzResearch.WordTrace tailWord_6887929 prefixEnd_6887929 1178939430347562226603499 := by
  unfold tailWord_6887929
  simp only [CollatzResearch.WordTrace]
  refine ⟨251223409463217072463138841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167482272975478048308759227 251223409463217072463138841)
  ·
    refine ⟨188417557097412804347354131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251223409463217072463138841 188417557097412804347354131)
    ·
      refine ⟨282626335646119206521031197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188417557097412804347354131 282626335646119206521031197)
      ·
        refine ⟨105984875867294702445386699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282626335646119206521031197 105984875867294702445386699)
        ·
          refine ⟨158977313800942053668080049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105984875867294702445386699 158977313800942053668080049)
          ·
            refine ⟨119232985350706540251060037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158977313800942053668080049 119232985350706540251060037)
            ·
              refine ⟨22356184753257476297073757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119232985350706540251060037 22356184753257476297073757)
              ·
                refine ⟨8383569282471553611402659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22356184753257476297073757 8383569282471553611402659)
                ·
                  refine ⟨12575353923707330417103989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8383569282471553611402659 12575353923707330417103989)
                  ·
                    refine ⟨1178939430347562226603499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12575353923707330417103989 1178939430347562226603499)
                    ·
                      rfl

theorem cell23_6887929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 5].length) (baseStart_6887929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887929 prefixEnd_6887929 := by exact prefixLift 6887929
  have htrace : WordTrace (prefixWord ++ tailWord_6887929) baseStart_6887929 baseEnd_6887929 := by
    simpa [prefixWord, tailWord_6887929, baseEnd_6887929] using wordTrace_append hprefix tailTrace_6887929
  have hstable : (prefixWord ++ tailWord_6887929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887929).length < 2 ^ (prefixWord ++ tailWord_6887929).sum := by decide
  have hdescent : baseEnd_6887929 < baseStart_6887929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887952 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 5]
def baseStart_6887952 : Nat := 118140960795 + 6887952 * 2 ^ 59
def prefixEnd_6887952 : Nat := 4983230072969 + 3 ^ 40 * 6887952 * 2
def baseEnd_6887952 : Nat := 3536830101097740089822891

theorem tailTrace_6887952 : CollatzResearch.WordTrace tailWord_6887952 prefixEnd_6887952 3536830101097740089822891 := by
  unfold tailWord_6887952
  simp only [CollatzResearch.WordTrace]
  refine ⟨125612124171066873695613055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167482832228089164927484073 125612124171066873695613055)
  ·
    refine ⟨188418186256600310543419583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125612124171066873695613055 188418186256600310543419583)
    ·
      refine ⟨282627279384900465815129375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188418186256600310543419583 282627279384900465815129375)
      ·
        refine ⟨423940919077350698722694063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282627279384900465815129375 423940919077350698722694063)
        ·
          refine ⟨635911378616026048084041095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423940919077350698722694063 635911378616026048084041095)
          ·
            refine ⟨953867067924039072126061643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635911378616026048084041095 953867067924039072126061643)
            ·
              refine ⟨1430800601886058608189092465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 953867067924039072126061643 1430800601886058608189092465)
              ·
                refine ⟨1073100451414543956141819349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1430800601886058608189092465 1073100451414543956141819349)
                ·
                  refine ⟨25150791830028373972073891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1073100451414543956141819349 25150791830028373972073891)
                  ·
                    refine ⟨37726187745042560958110837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25150791830028373972073891 37726187745042560958110837)
                    ·
                      refine ⟨3536830101097740089822891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37726187745042560958110837 3536830101097740089822891)
                      ·
                        rfl

theorem cell23_6887952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 5].length) (baseStart_6887952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887952 prefixEnd_6887952 := by exact prefixLift 6887952
  have htrace : WordTrace (prefixWord ++ tailWord_6887952) baseStart_6887952 baseEnd_6887952 := by
    simpa [prefixWord, tailWord_6887952, baseEnd_6887952] using wordTrace_append hprefix tailTrace_6887952
  have hstable : (prefixWord ++ tailWord_6887952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887952).length < 2 ^ (prefixWord ++ tailWord_6887952).sum := by decide
  have hdescent : baseEnd_6887952 < baseStart_6887952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887976 : List Nat := [2, 1, 5, 2, 1, 2, 1, 2, 1, 6]
def baseStart_6887976 : Nat := 118140960795 + 6887976 * 2 ^ 59
def prefixEnd_6887976 : Nat := 4983230072969 + 3 ^ 40 * 6887976 * 2
def baseEnd_6887976 : Nat := 1178947474877815998640927

theorem tailTrace_6887976 : CollatzResearch.WordTrace tailWord_6887976 prefixEnd_6887976 1178947474877815998640927 := by
  unfold tailWord_6887976
  simp only [CollatzResearch.WordTrace]
  refine ⟨125612561847023399745049891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167483415796031199660066521 125612561847023399745049891)
  ·
    refine ⟨188418842770535099617574837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125612561847023399745049891 188418842770535099617574837)
    ·
      refine ⟨17664266509737665589147641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188418842770535099617574837 17664266509737665589147641)
      ·
        refine ⟨13248199882303249191860731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17664266509737665589147641 13248199882303249191860731)
        ·
          refine ⟨19872299823454873787791097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13248199882303249191860731 19872299823454873787791097)
          ·
            refine ⟨14904224867591155340843323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19872299823454873787791097 14904224867591155340843323)
            ·
              refine ⟨22356337301386733011264985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14904224867591155340843323 22356337301386733011264985)
              ·
                refine ⟨16767252976040049758448739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22356337301386733011264985 16767252976040049758448739)
                ·
                  refine ⟨25150879464060074637673109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16767252976040049758448739 25150879464060074637673109)
                  ·
                    refine ⟨1178947474877815998640927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25150879464060074637673109 1178947474877815998640927)
                    ·
                      rfl

theorem cell23_6887976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_6887976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887976 prefixEnd_6887976 := by exact prefixLift 6887976
  have htrace : WordTrace (prefixWord ++ tailWord_6887976) baseStart_6887976 baseEnd_6887976 := by
    simpa [prefixWord, tailWord_6887976, baseEnd_6887976] using wordTrace_append hprefix tailTrace_6887976
  have hstable : (prefixWord ++ tailWord_6887976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887976).length < 2 ^ (prefixWord ++ tailWord_6887976).sum := by decide
  have hdescent : baseEnd_6887976 < baseStart_6887976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887986 : List Nat := [3, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3]
def baseStart_6887986 : Nat := 118140960795 + 6887986 * 2 ^ 59
def prefixEnd_6887986 : Nat := 4983230072969 + 3 ^ 40 * 6887986 * 2
def baseEnd_6887986 : Nat := 3536847559439992956797735

theorem tailTrace_6887986 : CollatzResearch.WordTrace tailWord_6887986 prefixEnd_6887986 3536847559439992956797735 := by
  unfold tailWord_6887986
  simp only [CollatzResearch.WordTrace]
  refine ⟨62806372106002642799490953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167483658949340380798642541 62806372106002642799490953)
  ·
    refine ⟨47104779079501982099618215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62806372106002642799490953 47104779079501982099618215)
    ·
      refine ⟨70657168619252973149427323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47104779079501982099618215 70657168619252973149427323)
      ·
        refine ⟨105985752928879459724140985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70657168619252973149427323 105985752928879459724140985)
        ·
          refine ⟨79489314696659594793105739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105985752928879459724140985 79489314696659594793105739)
          ·
            refine ⟨119233972044989392189658609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79489314696659594793105739 119233972044989392189658609)
            ·
              refine ⟨89425479033742044142243957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119233972044989392189658609 89425479033742044142243957)
              ·
                refine ⟨8383638659413316638335371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89425479033742044142243957 8383638659413316638335371)
                ·
                  refine ⟨12575457989119974957503057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8383638659413316638335371 12575457989119974957503057)
                  ·
                    refine ⟨9431593491839981218127293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12575457989119974957503057 9431593491839981218127293)
                    ·
                      refine ⟨3536847559439992956797735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9431593491839981218127293 3536847559439992956797735)
                      ·
                        rfl

theorem cell23_6887986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_6887986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887986 prefixEnd_6887986 := by exact prefixLift 6887986
  have htrace : WordTrace (prefixWord ++ tailWord_6887986) baseStart_6887986 baseEnd_6887986 := by
    simpa [prefixWord, tailWord_6887986, baseEnd_6887986] using wordTrace_append hprefix tailTrace_6887986
  have hstable : (prefixWord ++ tailWord_6887986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887986).length < 2 ^ (prefixWord ++ tailWord_6887986).sum := by decide
  have hdescent : baseEnd_6887986 < baseStart_6887986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6887999 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 3, 3, 3]
def baseStart_6887999 : Nat := 118140960795 + 6887999 * 2 ^ 59
def prefixEnd_6887999 : Nat := 4983230072969 + 3 ^ 40 * 6887999 * 2
def baseEnd_6887999 : Nat := 3536854234688501405935175

theorem tailTrace_6887999 : CollatzResearch.WordTrace tailWord_6887999 prefixEnd_6887999 3536854234688501405935175 := by
  unfold tailWord_6887999
  simp only [CollatzResearch.WordTrace]
  refine ⟨251225962572963474418187051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167483975048642316278791367 251225962572963474418187051)
  ·
    refine ⟨376838943859445211627280577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251225962572963474418187051 376838943859445211627280577)
    ·
      refine ⟨282629207894583908720460433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376838943859445211627280577 282629207894583908720460433)
      ·
        refine ⟨211971905920937931540345325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282629207894583908720460433 211971905920937931540345325)
        ·
          refine ⟨79489464720351724327629497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211971905920937931540345325 79489464720351724327629497)
          ·
            refine ⟨59617098540263793245722123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79489464720351724327629497 59617098540263793245722123)
            ·
              refine ⟨89425647810395689868583185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59617098540263793245722123 89425647810395689868583185)
              ·
                refine ⟨67069235857796767401437389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89425647810395689868583185 67069235857796767401437389)
                ·
                  refine ⟨25150963446673787775539021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67069235857796767401437389 25150963446673787775539021)
                  ·
                    refine ⟨9431611292502670415827133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25150963446673787775539021 9431611292502670415827133)
                    ·
                      refine ⟨3536854234688501405935175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9431611292502670415827133 3536854234688501405935175)
                      ·
                        rfl

theorem cell23_6887999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 3, 3].length) (baseStart_6887999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6887999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6887999 prefixEnd_6887999 := by exact prefixLift 6887999
  have htrace : WordTrace (prefixWord ++ tailWord_6887999) baseStart_6887999 baseEnd_6887999 := by
    simpa [prefixWord, tailWord_6887999, baseEnd_6887999] using wordTrace_append hprefix tailTrace_6887999
  have hstable : (prefixWord ++ tailWord_6887999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6887999).length < 2 ^ (prefixWord ++ tailWord_6887999).sum := by decide
  have hdescent : baseEnd_6887999 < baseStart_6887999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6887999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888013 : List Nat := [1, 6, 1, 1, 2, 2, 2, 1, 1, 2, 4]
def baseStart_6888013 : Nat := 118140960795 + 6888013 * 2 ^ 59
def prefixEnd_6888013 : Nat := 4983230072969 + 3 ^ 40 * 6888013 * 2
def baseEnd_6888013 : Nat := 3536861423417664351160111

theorem tailTrace_6888013 : CollatzResearch.WordTrace tailWord_6888013 prefixEnd_6888013 3536861423417664351160111 := by
  unfold tailWord_6888013
  simp only [CollatzResearch.WordTrace]
  refine ⟨251226473194912754809196693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167484315463275169872797795 251226473194912754809196693)
  ·
    refine ⟨11776240931011535381681095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 251226473194912754809196693 11776240931011535381681095)
    ·
      refine ⟨17664361396517303072521643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11776240931011535381681095 17664361396517303072521643)
      ·
        refine ⟨26496542094775954608782465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17664361396517303072521643 26496542094775954608782465)
        ·
          refine ⟨19872406571081965956586849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26496542094775954608782465 19872406571081965956586849)
          ·
            refine ⟨14904304928311474467440137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19872406571081965956586849 14904304928311474467440137)
            ·
              refine ⟨11178228696233605850580103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14904304928311474467440137 11178228696233605850580103)
              ·
                refine ⟨16767343044350408775870155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11178228696233605850580103 16767343044350408775870155)
                ·
                  refine ⟨25151014566525613163805233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16767343044350408775870155 25151014566525613163805233)
                  ·
                    refine ⟨18863260924894209872853925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25151014566525613163805233 18863260924894209872853925)
                    ·
                      refine ⟨3536861423417664351160111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18863260924894209872853925 3536861423417664351160111)
                      ·
                        rfl

theorem cell23_6888013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_6888013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888013 prefixEnd_6888013 := by exact prefixLift 6888013
  have htrace : WordTrace (prefixWord ++ tailWord_6888013) baseStart_6888013 baseEnd_6888013 := by
    simpa [prefixWord, tailWord_6888013, baseEnd_6888013] using wordTrace_append hprefix tailTrace_6888013
  have hstable : (prefixWord ++ tailWord_6888013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888013).length < 2 ^ (prefixWord ++ tailWord_6888013).sum := by decide
  have hdescent : baseEnd_6888013 < baseStart_6888013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888034 : List Nat := [3, 3, 2, 3, 2, 1, 2, 1, 1, 1, 4]
def baseStart_6888034 : Nat := 118140960795 + 6888034 * 2 ^ 59
def prefixEnd_6888034 : Nat := 4983230072969 + 3 ^ 40 * 6888034 * 2
def baseEnd_6888034 : Nat := 3536872206511408768997515

theorem tailTrace_6888034 : CollatzResearch.WordTrace tailWord_6888034 prefixEnd_6888034 3536872206511408768997515 := by
  unfold tailWord_6888034
  simp only [CollatzResearch.WordTrace]
  refine ⟨62806809781959168848927789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167484826085224450263807437 62806809781959168848927789)
  ·
    refine ⟨23552553668234688318347921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62806809781959168848927789 23552553668234688318347921)
    ·
      refine ⟨17664415251176016238760941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23552553668234688318347921 17664415251176016238760941)
      ·
        refine ⟨6624155719191006089535353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17664415251176016238760941 6624155719191006089535353)
        ·
          refine ⟨4968116789393254567151515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6624155719191006089535353 4968116789393254567151515)
          ·
            refine ⟨7452175184089881850727273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4968116789393254567151515 7452175184089881850727273)
            ·
              refine ⟨5589131388067411388045455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7452175184089881850727273 5589131388067411388045455)
              ·
                refine ⟨8383697082101117082068183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5589131388067411388045455 8383697082101117082068183)
                ·
                  refine ⟨12575545623151675623102275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8383697082101117082068183 12575545623151675623102275)
                  ·
                    refine ⟨18863318434727513434653413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12575545623151675623102275 18863318434727513434653413)
                    ·
                      refine ⟨3536872206511408768997515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18863318434727513434653413 3536872206511408768997515)
                      ·
                        rfl

theorem cell23_6888034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_6888034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888034 prefixEnd_6888034 := by exact prefixLift 6888034
  have htrace : WordTrace (prefixWord ++ tailWord_6888034) baseStart_6888034 baseEnd_6888034 := by
    simpa [prefixWord, tailWord_6888034, baseEnd_6888034] using wordTrace_append hprefix tailTrace_6888034
  have hstable : (prefixWord ++ tailWord_6888034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888034).length < 2 ^ (prefixWord ++ tailWord_6888034).sum := by decide
  have hdescent : baseEnd_6888034 < baseStart_6888034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888037 : List Nat := [1, 3, 1, 3, 5, 1, 2, 1, 1, 2, 3]
def baseStart_6888037 : Nat := 118140960795 + 6888037 * 2 ^ 59
def prefixEnd_6888037 : Nat := 4983230072969 + 3 ^ 40 * 6888037 * 2
def baseEnd_6888037 : Nat := 3536873746953372257260001

theorem tailTrace_6888037 : CollatzResearch.WordTrace tailWord_6888037 prefixEnd_6888037 3536873746953372257260001 := by
  unfold tailWord_6888037
  simp only [CollatzResearch.WordTrace]
  refine ⟨251227348546825806908070365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167484899031217204605380243 251227348546825806908070365)
  ·
    refine ⟨94210255705059677590526387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251227348546825806908070365 94210255705059677590526387)
    ·
      refine ⟨141315383557589516385789581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94210255705059677590526387 141315383557589516385789581)
      ·
        refine ⟨52993268834096068644671093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141315383557589516385789581 52993268834096068644671093)
        ·
          refine ⟨4968118953196506435437915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52993268834096068644671093 4968118953196506435437915)
          ·
            refine ⟨7452178429794759653156873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4968118953196506435437915 7452178429794759653156873)
            ·
              refine ⟨5589133822346069739867655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7452178429794759653156873 5589133822346069739867655)
              ·
                refine ⟨8383700733519104609801483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5589133822346069739867655 8383700733519104609801483)
                ·
                  refine ⟨12575551100278656914702225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8383700733519104609801483 12575551100278656914702225)
                  ·
                    refine ⟨9431663325208992686026669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12575551100278656914702225 9431663325208992686026669)
                    ·
                      refine ⟨3536873746953372257260001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9431663325208992686026669 3536873746953372257260001)
                      ·
                        rfl

theorem cell23_6888037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_6888037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888037 prefixEnd_6888037 := by exact prefixLift 6888037
  have htrace : WordTrace (prefixWord ++ tailWord_6888037) baseStart_6888037 baseEnd_6888037 := by
    simpa [prefixWord, tailWord_6888037, baseEnd_6888037] using wordTrace_append hprefix tailTrace_6888037
  have hstable : (prefixWord ++ tailWord_6888037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888037).length < 2 ^ (prefixWord ++ tailWord_6888037).sum := by decide
  have hdescent : baseEnd_6888037 < baseStart_6888037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888059 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 2, 4, 3]
def baseStart_6888059 : Nat := 118140960795 + 6888059 * 2 ^ 59
def prefixEnd_6888059 : Nat := 4983230072969 + 3 ^ 40 * 6888059 * 2
def baseEnd_6888059 : Nat := 3536885043527771171184899

theorem tailTrace_6888059 : CollatzResearch.WordTrace tailWord_6888059 prefixEnd_6888059 3536885043527771171184899 := by
  unfold tailWord_6888059
  simp only [CollatzResearch.WordTrace]
  refine ⟨251228150952746104665371231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167485433968497403110247487 251228150952746104665371231)
  ·
    refine ⟨376842226429119156998056847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251228150952746104665371231 376842226429119156998056847)
    ·
      refine ⟨565263339643678735497085271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376842226429119156998056847 565263339643678735497085271)
      ·
        refine ⟨847895009465518103245627907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565263339643678735497085271 847895009465518103245627907)
        ·
          refine ⟨1271842514198277154868441861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 847895009465518103245627907 1271842514198277154868441861)
          ·
            refine ⟨238470471412176966537832849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1271842514198277154868441861 238470471412176966537832849)
            ·
              refine ⟨178852853559132724903374637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238470471412176966537832849 178852853559132724903374637)
              ·
                refine ⟨67069820084674771838765489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178852853559132724903374637 67069820084674771838765489)
                ·
                  refine ⟨50302365063506078879074117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67069820084674771838765489 50302365063506078879074117)
                  ·
                    refine ⟨9431693449407389789826397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50302365063506078879074117 9431693449407389789826397)
                    ·
                      refine ⟨3536885043527771171184899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9431693449407389789826397 3536885043527771171184899)
                      ·
                        rfl

theorem cell23_6888059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 4, 3].length) (baseStart_6888059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888059 prefixEnd_6888059 := by exact prefixLift 6888059
  have htrace : WordTrace (prefixWord ++ tailWord_6888059) baseStart_6888059 baseEnd_6888059 := by
    simpa [prefixWord, tailWord_6888059, baseEnd_6888059] using wordTrace_append hprefix tailTrace_6888059
  have hstable : (prefixWord ++ tailWord_6888059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888059).length < 2 ^ (prefixWord ++ tailWord_6888059).sum := by decide
  have hdescent : baseEnd_6888059 < baseStart_6888059 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888126 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 4, 5]
def baseStart_6888126 : Nat := 118140960795 + 6888126 * 2 ^ 59
def prefixEnd_6888126 : Nat := 4983230072969 + 3 ^ 40 * 6888126 * 2
def baseEnd_6888126 : Nat := 1178973148910540803015697

theorem tailTrace_6888126 : CollatzResearch.WordTrace tailWord_6888126 prefixEnd_6888126 1178973148910540803015697 := by
  unfold tailWord_6888126
  simp only [CollatzResearch.WordTrace]
  refine ⟨31403824330437921888507529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167487063095668916738706821 31403824330437921888507529)
  ·
    refine ⟨23552868247828441416380647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31403824330437921888507529 23552868247828441416380647)
    ·
      refine ⟨35329302371742662124570971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23552868247828441416380647 35329302371742662124570971)
      ·
        refine ⟨52993953557613993186856457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35329302371742662124570971 52993953557613993186856457)
        ·
          refine ⟨39745465168210494890142343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52993953557613993186856457 39745465168210494890142343)
          ·
            refine ⟨59618197752315742335213515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39745465168210494890142343 59618197752315742335213515)
            ·
              refine ⟨89427296628473613502820273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59618197752315742335213515 89427296628473613502820273)
              ·
                refine ⟨67070472471355210127115205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89427296628473613502820273 67070472471355210127115205)
                ·
                  refine ⟨12575713588379101898834101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67070472471355210127115205 12575713588379101898834101)
                  ·
                    refine ⟨1178973148910540803015697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12575713588379101898834101 1178973148910540803015697)
                    ·
                      rfl

theorem cell23_6888126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_6888126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888126 prefixEnd_6888126 := by exact prefixLift 6888126
  have htrace : WordTrace (prefixWord ++ tailWord_6888126) baseStart_6888126 baseEnd_6888126 := by
    simpa [prefixWord, tailWord_6888126, baseEnd_6888126] using wordTrace_append hprefix tailTrace_6888126
  have hstable : (prefixWord ++ tailWord_6888126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888126).length < 2 ^ (prefixWord ++ tailWord_6888126).sum := by decide
  have hdescent : baseEnd_6888126 < baseStart_6888126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888163 : List Nat := [1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 4]
def baseStart_6888163 : Nat := 118140960795 + 6888163 * 2 ^ 59
def prefixEnd_6888163 : Nat := 4983230072969 + 3 ^ 40 * 6888163 * 2
def baseEnd_6888163 : Nat := 3536938445515838764284421

theorem tailTrace_6888163 : CollatzResearch.WordTrace tailWord_6888163 prefixEnd_6888163 3536938445515838764284421 := by
  unfold tailWord_6888163
  simp only [CollatzResearch.WordTrace]
  refine ⟨251231944144369330427157143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167487962762912886951438095 251231944144369330427157143)
  ·
    refine ⟨376847916216553995640735715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251231944144369330427157143 376847916216553995640735715)
    ·
      refine ⟨565271874324830993461103573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376847916216553995640735715 565271874324830993461103573)
      ·
        refine ⟨13248559554488226409244615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 565271874324830993461103573 13248559554488226409244615)
        ·
          refine ⟨19872839331732339613866923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13248559554488226409244615 19872839331732339613866923)
          ·
            refine ⟨29809258997598509420800385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19872839331732339613866923 29809258997598509420800385)
            ·
              refine ⟨22356944248198882065600289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29809258997598509420800385 22356944248198882065600289)
              ·
                refine ⟨16767708186149161549200217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22356944248198882065600289 16767708186149161549200217)
                ·
                  refine ⟨12575781139611871161900163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16767708186149161549200217 12575781139611871161900163)
                  ·
                    refine ⟨18863671709417806742850245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12575781139611871161900163 18863671709417806742850245)
                    ·
                      refine ⟨3536938445515838764284421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18863671709417806742850245 3536938445515838764284421)
                      ·
                        rfl

theorem cell23_6888163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_6888163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888163 prefixEnd_6888163 := by exact prefixLift 6888163
  have htrace : WordTrace (prefixWord ++ tailWord_6888163) baseStart_6888163 baseEnd_6888163 := by
    simpa [prefixWord, tailWord_6888163, baseEnd_6888163] using wordTrace_append hprefix tailTrace_6888163
  have hstable : (prefixWord ++ tailWord_6888163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888163).length < 2 ^ (prefixWord ++ tailWord_6888163).sum := by decide
  have hdescent : baseEnd_6888163 < baseStart_6888163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888169 : List Nat := [1, 2, 1, 1, 1, 2, 4, 3, 8]
def baseStart_6888169 : Nat := 118140960795 + 6888169 * 2 ^ 59
def prefixEnd_6888169 : Nat := 4983230072969 + 3 ^ 40 * 6888169 * 2
def baseEnd_6888169 : Nat := 392993502933307304534377

theorem tailTrace_6888169 : CollatzResearch.WordTrace tailWord_6888169 prefixEnd_6888169 392993502933307304534377 := by
  unfold tailWord_6888169
  simp only [CollatzResearch.WordTrace]
  refine ⟨251232162982347593451875561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167488108654898395634583707 251232162982347593451875561)
  ·
    refine ⟨188424122236760695088906671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251232162982347593451875561 188424122236760695088906671)
    ·
      refine ⟨282636183355141042633360007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188424122236760695088906671 282636183355141042633360007)
      ·
        refine ⟨423954275032711563950040011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282636183355141042633360007 423954275032711563950040011)
        ·
          refine ⟨635931412549067345925060017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423954275032711563950040011 635931412549067345925060017)
          ·
            refine ⟨476948559411800509443795013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 635931412549067345925060017 476948559411800509443795013)
            ·
              refine ⟨89427854889712595520711565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 476948559411800509443795013 89427854889712595520711565)
              ·
                refine ⟨33535445583642223320266837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89427854889712595520711565 33535445583642223320266837)
                ·
                  refine ⟨392993502933307304534377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33535445583642223320266837 392993502933307304534377)
                  ·
                    rfl

theorem cell23_6888169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 8].length) (baseStart_6888169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888169 prefixEnd_6888169 := by exact prefixLift 6888169
  have htrace : WordTrace (prefixWord ++ tailWord_6888169) baseStart_6888169 baseEnd_6888169 := by
    simpa [prefixWord, tailWord_6888169, baseEnd_6888169] using wordTrace_append hprefix tailTrace_6888169
  have hstable : (prefixWord ++ tailWord_6888169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888169).length < 2 ^ (prefixWord ++ tailWord_6888169).sum := by decide
  have hdescent : baseEnd_6888169 < baseStart_6888169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888173 : List Nat := [1, 5, 1, 2, 1, 1, 2, 3, 3, 4]
def baseStart_6888173 : Nat := 118140960795 + 6888173 * 2 ^ 59
def prefixEnd_6888173 : Nat := 4983230072969 + 3 ^ 40 * 6888173 * 2
def baseEnd_6888173 : Nat := 1178981193440794575053125

theorem tailTrace_6888173 : CollatzResearch.WordTrace tailWord_6888173 prefixEnd_6888173 1178981193440794575053125 := by
  unfold tailWord_6888173
  simp only [CollatzResearch.WordTrace]
  refine ⟨251232308874333102135021173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167488205916222068090014115 251232308874333102135021173)
  ·
    refine ⟨23553028956968728325158235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 251232308874333102135021173 23553028956968728325158235)
    ·
      refine ⟨35329543435453092487737353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23553028956968728325158235 35329543435453092487737353)
      ·
        refine ⟨26497157576589819365803015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35329543435453092487737353 26497157576589819365803015)
        ·
          refine ⟨39745736364884729048704523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26497157576589819365803015 39745736364884729048704523)
          ·
            refine ⟨59618604547327093573056785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39745736364884729048704523 59618604547327093573056785)
            ·
              refine ⟨44713953410495320179792589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59618604547327093573056785 44713953410495320179792589)
              ·
                refine ⟨16767732528935745067422221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44713953410495320179792589 16767732528935745067422221)
                ·
                  refine ⟨6287899698350904400283333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16767732528935745067422221 6287899698350904400283333)
                  ·
                    refine ⟨1178981193440794575053125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6287899698350904400283333 1178981193440794575053125)
                    ·
                      rfl

theorem cell23_6888173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_6888173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888173 prefixEnd_6888173 := by exact prefixLift 6888173
  have htrace : WordTrace (prefixWord ++ tailWord_6888173) baseStart_6888173 baseEnd_6888173 := by
    simpa [prefixWord, tailWord_6888173, baseEnd_6888173] using wordTrace_append hprefix tailTrace_6888173
  have hstable : (prefixWord ++ tailWord_6888173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888173).length < 2 ^ (prefixWord ++ tailWord_6888173).sum := by decide
  have hdescent : baseEnd_6888173 < baseStart_6888173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888186 : List Nat := [3, 1, 1, 1, 1, 3, 4, 3, 6]
def baseStart_6888186 : Nat := 118140960795 + 6888186 * 2 ^ 59
def prefixEnd_6888186 : Nat := 4983230072969 + 3 ^ 40 * 6888186 * 2
def baseEnd_6888186 : Nat := 392994472841210241588535

theorem tailTrace_6888186 : CollatzResearch.WordTrace tailWord_6888186 prefixEnd_6888186 392994472841210241588535 := by
  unfold tailWord_6888186
  simp only [CollatzResearch.WordTrace]
  refine ⟨62808195755821501338811103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167488522015524003570162941 62808195755821501338811103)
  ·
    refine ⟨94212293633732252008216655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62808195755821501338811103 94212293633732252008216655)
    ·
      refine ⟨141318440450598378012324983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94212293633732252008216655 141318440450598378012324983)
      ·
        refine ⟨211977660675897567018487475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141318440450598378012324983 211977660675897567018487475)
        ·
          refine ⟨317966491013846350527731213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211977660675897567018487475 317966491013846350527731213)
          ·
            refine ⟨119237434130192381447899205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317966491013846350527731213 119237434130192381447899205)
            ·
              refine ⟨22357018899411071521481101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119237434130192381447899205 22357018899411071521481101)
              ·
                refine ⟨8383882087279151820555413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22357018899411071521481101 8383882087279151820555413)
                ·
                  refine ⟨392994472841210241588535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8383882087279151820555413 392994472841210241588535)
                  ·
                    rfl

theorem cell23_6888186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 6].length) (baseStart_6888186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888186 prefixEnd_6888186 := by exact prefixLift 6888186
  have htrace : WordTrace (prefixWord ++ tailWord_6888186) baseStart_6888186 baseEnd_6888186 := by
    simpa [prefixWord, tailWord_6888186, baseEnd_6888186] using wordTrace_append hprefix tailTrace_6888186
  have hstable : (prefixWord ++ tailWord_6888186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888186).length < 2 ^ (prefixWord ++ tailWord_6888186).sum := by decide
  have hdescent : baseEnd_6888186 < baseStart_6888186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888190 : List Nat := [4, 2, 2, 1, 2, 2, 1, 2, 3, 4]
def baseStart_6888190 : Nat := 118140960795 + 6888190 * 2 ^ 59
def prefixEnd_6888190 : Nat := 4983230072969 + 3 ^ 40 * 6888190 * 2
def baseEnd_6888190 : Nat := 1178984103164503386215599

theorem tailTrace_6888190 : CollatzResearch.WordTrace tailWord_6888190 prefixEnd_6888190 1178984103164503386215599 := by
  unfold tailWord_6888190
  simp only [CollatzResearch.WordTrace]
  refine ⟨31404116114408939254798753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167488619276847676025593349 31404116114408939254798753)
  ·
    refine ⟨23553087085806704441099065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31404116114408939254798753 23553087085806704441099065)
    ·
      refine ⟨17664815314355028330824299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23553087085806704441099065 17664815314355028330824299)
      ·
        refine ⟨26497222971532542496236449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17664815314355028330824299 26497222971532542496236449)
        ·
          refine ⟨19872917228649406872177337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26497222971532542496236449 19872917228649406872177337)
          ·
            refine ⟨14904687921487055154133003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19872917228649406872177337 14904687921487055154133003)
            ·
              refine ⟨22357031882230582731199505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14904687921487055154133003 22357031882230582731199505)
              ·
                refine ⟨16767773911672937048399629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22357031882230582731199505 16767773911672937048399629)
                ·
                  refine ⟨6287915216877351393149861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16767773911672937048399629 6287915216877351393149861)
                  ·
                    refine ⟨1178984103164503386215599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6287915216877351393149861 1178984103164503386215599)
                    ·
                      rfl

theorem cell23_6888190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_6888190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888190 prefixEnd_6888190 := by exact prefixLift 6888190
  have htrace : WordTrace (prefixWord ++ tailWord_6888190) baseStart_6888190 baseEnd_6888190 := by
    simpa [prefixWord, tailWord_6888190, baseEnd_6888190] using wordTrace_append hprefix tailTrace_6888190
  have hstable : (prefixWord ++ tailWord_6888190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888190).length < 2 ^ (prefixWord ++ tailWord_6888190).sum := by decide
  have hdescent : baseEnd_6888190 < baseStart_6888190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888200 : List Nat := [2, 1, 3, 2, 2, 4, 1, 1, 2, 2, 3]
def baseStart_6888200 : Nat := 118140960795 + 6888200 * 2 ^ 59
def prefixEnd_6888200 : Nat := 4983230072969 + 3 ^ 40 * 6888200 * 2
def baseEnd_6888200 : Nat := 3536957444300055119521751

theorem tailTrace_6888200 : CollatzResearch.WordTrace tailWord_6888200 prefixEnd_6888200 3536957444300055119521751 := by
  unfold tailWord_6888200
  simp only [CollatzResearch.WordTrace]
  refine ⟨125616646822617642873127027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167488862430156857164169369 125616646822617642873127027)
  ·
    refine ⟨188424970233926464309690541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125616646822617642873127027 188424970233926464309690541)
    ·
      refine ⟨70659363837722424116133953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188424970233926464309690541 70659363837722424116133953)
      ·
        refine ⟨52994522878291818087100465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70659363837722424116133953 52994522878291818087100465)
        ·
          refine ⟨39745892158718863565325349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52994522878291818087100465 39745892158718863565325349)
          ·
            refine ⟨7452354779759786918498503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39745892158718863565325349 7452354779759786918498503)
            ·
              refine ⟨11178532169639680377747755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7452354779759786918498503 11178532169639680377747755)
              ·
                refine ⟨16767798254459520566621633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11178532169639680377747755 16767798254459520566621633)
                ·
                  refine ⟨12575848690844640424966225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16767798254459520566621633 12575848690844640424966225)
                  ·
                    refine ⟨9431886518133480318724669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12575848690844640424966225 9431886518133480318724669)
                    ·
                      refine ⟨3536957444300055119521751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9431886518133480318724669 3536957444300055119521751)
                      ·
                        rfl

theorem cell23_6888200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_6888200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888200 prefixEnd_6888200 := by exact prefixLift 6888200
  have htrace : WordTrace (prefixWord ++ tailWord_6888200) baseStart_6888200 baseEnd_6888200 := by
    simpa [prefixWord, tailWord_6888200, baseEnd_6888200] using wordTrace_append hprefix tailTrace_6888200
  have hstable : (prefixWord ++ tailWord_6888200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888200).length < 2 ^ (prefixWord ++ tailWord_6888200).sum := by decide
  have hdescent : baseEnd_6888200 < baseStart_6888200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888213 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 5, 1, 3]
def baseStart_6888213 : Nat := 118140960795 + 6888213 * 2 ^ 59
def prefixEnd_6888213 : Nat := 4983230072969 + 3 ^ 40 * 6888213 * 2
def baseEnd_6888213 : Nat := 3536964119548563568659191

theorem tailTrace_6888213 : CollatzResearch.WordTrace tailWord_6888213 prefixEnd_6888213 3536964119548563568659191 := by
  unfold tailWord_6888213
  simp only [CollatzResearch.WordTrace]
  refine ⟨251233767794188188966477293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167489178529458792644318195 251233767794188188966477293)
  ·
    refine ⟨94212662922820570862428985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251233767794188188966477293 94212662922820570862428985)
    ·
      refine ⟨70659497192115428146821739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94212662922820570862428985 70659497192115428146821739)
      ·
        refine ⟨105989245788173142220232609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70659497192115428146821739 105989245788173142220232609)
        ·
          refine ⟨79491934341129856665174457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105989245788173142220232609 79491934341129856665174457)
          ·
            refine ⟨59618950755847392498880843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79491934341129856665174457 59618950755847392498880843)
            ·
              refine ⟨89428426133771088748321265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59618950755847392498880843 89428426133771088748321265)
              ·
                refine ⟨67071319600328316561240949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89428426133771088748321265 67071319600328316561240949)
                ·
                  refine ⟨6287936212530779677616339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67071319600328316561240949 6287936212530779677616339)
                  ·
                    refine ⟨9431904318796169516424509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6287936212530779677616339 9431904318796169516424509)
                    ·
                      refine ⟨3536964119548563568659191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9431904318796169516424509 3536964119548563568659191)
                      ·
                        rfl

theorem cell23_6888213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_6888213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888213 prefixEnd_6888213 := by exact prefixLift 6888213
  have htrace : WordTrace (prefixWord ++ tailWord_6888213) baseStart_6888213 baseEnd_6888213 := by
    simpa [prefixWord, tailWord_6888213, baseEnd_6888213] using wordTrace_append hprefix tailTrace_6888213
  have hstable : (prefixWord ++ tailWord_6888213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888213).length < 2 ^ (prefixWord ++ tailWord_6888213).sum := by decide
  have hdescent : baseEnd_6888213 < baseStart_6888213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888250 : List Nat := [3, 1, 1, 1, 6, 1, 2, 2, 1, 5]
def baseStart_6888250 : Nat := 118140960795 + 6888250 * 2 ^ 59
def prefixEnd_6888250 : Nat := 4983230072969 + 3 ^ 40 * 6888250 * 2
def baseEnd_6888250 : Nat := 1178994372777593307965507

theorem tailTrace_6888250 : CollatzResearch.WordTrace tailWord_6888250 prefixEnd_6888250 1178994372777593307965507 := by
  unfold tailWord_6888250
  simp only [CollatzResearch.WordTrace]
  refine ⟨62808779323763536071393551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167490078196702762857049469 62808779323763536071393551)
  ·
    refine ⟨94213168985645304107090327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62808779323763536071393551 94213168985645304107090327)
    ·
      refine ⟨141319753478467956160635491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94213168985645304107090327 141319753478467956160635491)
      ·
        refine ⟨211979630217701934240953237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141319753478467956160635491 211979630217701934240953237)
        ·
          refine ⟨9936545166454778167544683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 211979630217701934240953237 9936545166454778167544683)
          ·
            refine ⟨14904817749682167251317025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9936545166454778167544683 14904817749682167251317025)
            ·
              refine ⟨11178613312261625438487769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14904817749682167251317025 11178613312261625438487769)
              ·
                refine ⟨8383959984196219078865827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11178613312261625438487769 8383959984196219078865827)
                ·
                  refine ⟨12575939976294328618298741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8383959984196219078865827 12575939976294328618298741)
                  ·
                    refine ⟨1178994372777593307965507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12575939976294328618298741 1178994372777593307965507)
                    ·
                      rfl

theorem cell23_6888250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 1, 5].length) (baseStart_6888250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888250 prefixEnd_6888250 := by exact prefixLift 6888250
  have htrace : WordTrace (prefixWord ++ tailWord_6888250) baseStart_6888250 baseEnd_6888250 := by
    simpa [prefixWord, tailWord_6888250, baseEnd_6888250] using wordTrace_append hprefix tailTrace_6888250
  have hstable : (prefixWord ++ tailWord_6888250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888250).length < 2 ^ (prefixWord ++ tailWord_6888250).sum := by decide
  have hdescent : baseEnd_6888250 < baseStart_6888250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888256 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 3]
def baseStart_6888256 : Nat := 118140960795 + 6888256 * 2 ^ 59
def prefixEnd_6888256 : Nat := 4983230072969 + 3 ^ 40 * 6888256 * 2
def baseEnd_6888256 : Nat := 3536986199216706900421493

theorem tailTrace_6888256 : CollatzResearch.WordTrace tailWord_6888256 prefixEnd_6888256 3536986199216706900421493 := by
  unfold tailWord_6888256
  simp only [CollatzResearch.WordTrace]
  refine ⟨125617668066516203655146311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167490224088688271540195081 125617668066516203655146311)
  ·
    refine ⟨188426502099774305482719467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125617668066516203655146311 188426502099774305482719467)
    ·
      refine ⟨282639753149661458224079201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188426502099774305482719467 282639753149661458224079201)
      ·
        refine ⟨211979814862246093668059401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282639753149661458224079201 211979814862246093668059401)
        ·
          refine ⟨158984861146684570251044551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211979814862246093668059401 158984861146684570251044551)
          ·
            refine ⟨238477291720026855376566827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158984861146684570251044551 238477291720026855376566827)
            ·
              refine ⟨357715937580040283064850241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238477291720026855376566827 357715937580040283064850241)
              ·
                refine ⟨268286953185030212298637681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 357715937580040283064850241 268286953185030212298637681)
                ·
                  refine ⟨201215214888772659223978261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 268286953185030212298637681 201215214888772659223978261)
                  ·
                    refine ⟨9431963197911218401123981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 201215214888772659223978261 9431963197911218401123981)
                    ·
                      refine ⟨3536986199216706900421493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9431963197911218401123981 3536986199216706900421493)
                      ·
                        rfl

theorem cell23_6888256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 3].length) (baseStart_6888256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888256 prefixEnd_6888256 := by exact prefixLift 6888256
  have htrace : WordTrace (prefixWord ++ tailWord_6888256) baseStart_6888256 baseEnd_6888256 := by
    simpa [prefixWord, tailWord_6888256, baseEnd_6888256] using wordTrace_append hprefix tailTrace_6888256
  have hstable : (prefixWord ++ tailWord_6888256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888256).length < 2 ^ (prefixWord ++ tailWord_6888256).sum := by decide
  have hdescent : baseEnd_6888256 < baseStart_6888256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888270 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2]
def baseStart_6888270 : Nat := 118140960795 + 6888270 * 2 ^ 59
def prefixEnd_6888270 : Nat := 4983230072969 + 3 ^ 40 * 6888270 * 2
def baseEnd_6888270 : Nat := 3536993387945869845646429

theorem tailTrace_6888270 : CollatzResearch.WordTrace tailWord_6888270 prefixEnd_6888270 3536993387945869845646429 := by
  unfold tailWord_6888270
  simp only [CollatzResearch.WordTrace]
  refine ⟨31404480844372710962662783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167490564503321125134201509 31404480844372710962662783)
  ·
    refine ⟨47106721266559066443994175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31404480844372710962662783 47106721266559066443994175)
    ·
      refine ⟨70660081899838599665991263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47106721266559066443994175 70660081899838599665991263)
      ·
        refine ⟨105990122849757899498986895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70660081899838599665991263 105990122849757899498986895)
        ·
          refine ⟨158985184274636849248480343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105990122849757899498986895 158985184274636849248480343)
          ·
            refine ⟨238477776411955273872720515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158985184274636849248480343 238477776411955273872720515)
            ·
              refine ⟨357716664617932910809080773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238477776411955273872720515 357716664617932910809080773)
              ·
                refine ⟨67071874615862420776702645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 357716664617932910809080773 67071874615862420776702645)
                ·
                  refine ⟨6287988245237101947815873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67071874615862420776702645 6287988245237101947815873)
                  ·
                    refine ⟨4715991183927826460861905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6287988245237101947815873 4715991183927826460861905)
                    ·
                      refine ⟨3536993387945869845646429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4715991183927826460861905 3536993387945869845646429)
                      ·
                        rfl

theorem cell23_6888270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2].length) (baseStart_6888270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888270 prefixEnd_6888270 := by exact prefixLift 6888270
  have htrace : WordTrace (prefixWord ++ tailWord_6888270) baseStart_6888270 baseEnd_6888270 := by
    simpa [prefixWord, tailWord_6888270, baseEnd_6888270] using wordTrace_append hprefix tailTrace_6888270
  have hstable : (prefixWord ++ tailWord_6888270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888270).length < 2 ^ (prefixWord ++ tailWord_6888270).sum := by decide
  have hdescent : baseEnd_6888270 < baseStart_6888270 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888316 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 1, 4, 5]
def baseStart_6888316 : Nat := 118140960795 + 6888316 * 2 ^ 59
def prefixEnd_6888316 : Nat := 4983230072969 + 3 ^ 40 * 6888316 * 2
def baseEnd_6888316 : Nat := 3537017008055976665671217

theorem tailTrace_6888316 : CollatzResearch.WordTrace tailWord_6888316 prefixEnd_6888316 3537017008055976665671217 := by
  unfold tailWord_6888316
  simp only [CollatzResearch.WordTrace]
  refine ⟨125618762256407518778738401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167491683008543358371651201 125618762256407518778738401)
  ·
    refine ⟨94214071692305639084053801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125618762256407518778738401 94214071692305639084053801)
    ·
      refine ⟨70660553769229229313040351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94214071692305639084053801 70660553769229229313040351)
      ·
        refine ⟨105990830653843843969560527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70660553769229229313040351 105990830653843843969560527)
        ·
          refine ⟨158986245980765765954340791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105990830653843843969560527 158986245980765765954340791)
          ·
            refine ⟨238479368971148648931511187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158986245980765765954340791 238479368971148648931511187)
            ·
              refine ⟨357719053456722973397266781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238479368971148648931511187 357719053456722973397266781)
              ·
                refine ⟨134144645046271115023975043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 357719053456722973397266781 134144645046271115023975043)
                ·
                  refine ⟨201216967569406672535962565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134144645046271115023975043 201216967569406672535962565)
                  ·
                    refine ⟨37728181419263751100492981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 201216967569406672535962565 37728181419263751100492981)
                    ·
                      refine ⟨3537017008055976665671217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37728181419263751100492981 3537017008055976665671217)
                      ·
                        rfl

theorem cell23_6888316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_6888316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888316 prefixEnd_6888316 := by exact prefixLift 6888316
  have htrace : WordTrace (prefixWord ++ tailWord_6888316) baseStart_6888316 baseEnd_6888316 := by
    simpa [prefixWord, tailWord_6888316, baseEnd_6888316] using wordTrace_append hprefix tailTrace_6888316
  have hstable : (prefixWord ++ tailWord_6888316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888316).length < 2 ^ (prefixWord ++ tailWord_6888316).sum := by decide
  have hdescent : baseEnd_6888316 < baseStart_6888316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888353 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 1, 8]
def baseStart_6888353 : Nat := 118140960795 + 6888353 * 2 ^ 59
def prefixEnd_6888353 : Nat := 4983230072969 + 3 ^ 40 * 6888353 * 2
def baseEnd_6888353 : Nat := 1179012002280064340302849

theorem tailTrace_6888353 : CollatzResearch.WordTrace tailWord_6888353 prefixEnd_6888353 1179012002280064340302849 := by
  unfold tailWord_6888353
  simp only [CollatzResearch.WordTrace]
  refine ⟨251238874013680992876573713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167492582675787328584382475 251238874013680992876573713)
  ·
    refine ⟨188429155510260744657430285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251238874013680992876573713 188429155510260744657430285)
    ·
      refine ⟨70660933316347779246536357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188429155510260744657430285 70660933316347779246536357)
      ·
        refine ⟨13248924996815208608725567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70660933316347779246536357 13248924996815208608725567)
        ·
          refine ⟨19873387495222812913088351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13248924996815208608725567 19873387495222812913088351)
          ·
            refine ⟨29810081242834219369632527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19873387495222812913088351 29810081242834219369632527)
            ·
              refine ⟨44715121864251329054448791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29810081242834219369632527 44715121864251329054448791)
              ·
                refine ⟨67072682796376993581673187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44715121864251329054448791 67072682796376993581673187)
                ·
                  refine ⟨100609024194565490372509781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67072682796376993581673187 100609024194565490372509781)
                  ·
                    refine ⟨1179012002280064340302849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100609024194565490372509781 1179012002280064340302849)
                    ·
                      rfl

theorem cell23_6888353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_6888353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888353 prefixEnd_6888353 := by exact prefixLift 6888353
  have htrace : WordTrace (prefixWord ++ tailWord_6888353) baseStart_6888353 baseEnd_6888353 := by
    simpa [prefixWord, tailWord_6888353, baseEnd_6888353] using wordTrace_append hprefix tailTrace_6888353
  have hstable : (prefixWord ++ tailWord_6888353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888353).length < 2 ^ (prefixWord ++ tailWord_6888353).sum := by decide
  have hdescent : baseEnd_6888353 < baseStart_6888353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888373 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 1, 4, 4]
def baseStart_6888373 : Nat := 118140960795 + 6888373 * 2 ^ 59
def prefixEnd_6888373 : Nat := 4983230072969 + 3 ^ 40 * 6888373 * 2
def baseEnd_6888373 : Nat := 3537046276453282942658455

theorem tailTrace_6888373 : CollatzResearch.WordTrace tailWord_6888373 prefixEnd_6888373 3537046276453282942658455 := by
  unfold tailWord_6888373
  simp only [CollatzResearch.WordTrace]
  refine ⟨251239603473608536292301773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167493068982405690861534515 251239603473608536292301773)
  ·
    refine ⟨94214851302603201109613165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251239603473608536292301773 94214851302603201109613165)
    ·
      refine ⟨35330569238476200416104937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94214851302603201109613165 35330569238476200416104937)
      ·
        refine ⟨26497926928857150312078703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35330569238476200416104937 26497926928857150312078703)
        ·
          refine ⟨39746890393285725468118055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26497926928857150312078703 39746890393285725468118055)
          ·
            refine ⟨59620335589928588202177083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39746890393285725468118055 59620335589928588202177083)
            ·
              refine ⟨89430503384892882303265625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59620335589928588202177083 89430503384892882303265625)
              ·
                refine ⟨67072877538669661727449219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89430503384892882303265625 67072877538669661727449219)
                ·
                  refine ⟨100609316308004492591173829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67072877538669661727449219 100609316308004492591173829)
                  ·
                    refine ⟨18864246807750842360845093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100609316308004492591173829 18864246807750842360845093)
                    ·
                      refine ⟨3537046276453282942658455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18864246807750842360845093 3537046276453282942658455)
                      ·
                        rfl

theorem cell23_6888373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_6888373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888373 prefixEnd_6888373 := by exact prefixLift 6888373
  have htrace : WordTrace (prefixWord ++ tailWord_6888373) baseStart_6888373 baseEnd_6888373 := by
    simpa [prefixWord, tailWord_6888373, baseEnd_6888373] using wordTrace_append hprefix tailTrace_6888373
  have hstable : (prefixWord ++ tailWord_6888373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888373).length < 2 ^ (prefixWord ++ tailWord_6888373).sum := by decide
  have hdescent : baseEnd_6888373 < baseStart_6888373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888381 : List Nat := [1, 4, 1, 2, 4, 2, 2, 1, 1, 3, 2]
def baseStart_6888381 : Nat := 118140960795 + 6888381 * 2 ^ 59
def prefixEnd_6888381 : Nat := 4983230072969 + 3 ^ 40 * 6888381 * 2
def baseEnd_6888381 : Nat := 3537050384298518911358419

theorem tailTrace_6888381 : CollatzResearch.WordTrace tailWord_6888381 prefixEnd_6888381 3537050384298518911358419 := by
  unfold tailWord_6888381
  simp only [CollatzResearch.WordTrace]
  refine ⟨251239895257579553658592997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167493263505053035772395331 251239895257579553658592997)
  ·
    refine ⟨47107480360796166310986187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251239895257579553658592997 47107480360796166310986187)
    ·
      refine ⟨70661220541194249466479281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47107480360796166310986187 70661220541194249466479281)
      ·
        refine ⟨52995915405895687099859461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70661220541194249466479281 52995915405895687099859461)
        ·
          refine ⟨9936734138605441331223649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52995915405895687099859461 9936734138605441331223649)
          ·
            refine ⟨7452550603954080998417737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9936734138605441331223649 7452550603954080998417737)
            ·
              refine ⟨5589412952965560748813303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7452550603954080998417737 5589412952965560748813303)
              ·
                refine ⟨8384119429448341123219955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5589412952965560748813303 8384119429448341123219955)
                ·
                  refine ⟨12576179144172511684829933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8384119429448341123219955 12576179144172511684829933)
                  ·
                    refine ⟨4716067179064691881811225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12576179144172511684829933 4716067179064691881811225)
                    ·
                      refine ⟨3537050384298518911358419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4716067179064691881811225 3537050384298518911358419)
                      ·
                        rfl

theorem cell23_6888381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_6888381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888381 prefixEnd_6888381 := by exact prefixLift 6888381
  have htrace : WordTrace (prefixWord ++ tailWord_6888381) baseStart_6888381 baseEnd_6888381 := by
    simpa [prefixWord, tailWord_6888381, baseEnd_6888381] using wordTrace_append hprefix tailTrace_6888381
  have hstable : (prefixWord ++ tailWord_6888381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888381).length < 2 ^ (prefixWord ++ tailWord_6888381).sum := by decide
  have hdescent : baseEnd_6888381 < baseStart_6888381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888388 : List Nat := [2, 3, 3, 3, 2, 1, 1, 2, 2, 1, 3]
def baseStart_6888388 : Nat := 118140960795 + 6888388 * 2 ^ 59
def prefixEnd_6888388 : Nat := 4983230072969 + 3 ^ 40 * 6888388 * 2
def baseEnd_6888388 : Nat := 3537053978663100383970887

theorem tailTrace_6888388 : CollatzResearch.WordTrace tailWord_6888388 prefixEnd_6888388 3537053978663100383970887 := by
  unfold tailWord_6888388
  simp only [CollatzResearch.WordTrace]
  refine ⟨125620075284277096927048909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167493433712369462569398545 125620075284277096927048909)
  ·
    refine ⟨47107528231603911347643341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125620075284277096927048909 47107528231603911347643341)
    ·
      refine ⟨17665323086851466755366253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47107528231603911347643341 17665323086851466755366253)
      ·
        refine ⟨6624496157569300033262345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17665323086851466755366253 6624496157569300033262345)
        ·
          refine ⟨4968372118176975024946759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6624496157569300033262345 4968372118176975024946759)
          ·
            refine ⟨7452558177265462537420139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4968372118176975024946759 7452558177265462537420139)
            ·
              refine ⟨11178837265898193806130209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7452558177265462537420139 11178837265898193806130209)
              ·
                refine ⟨8384127949423645354597657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11178837265898193806130209 8384127949423645354597657)
                ·
                  refine ⟨6288095962067734015948243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8384127949423645354597657 6288095962067734015948243)
                  ·
                    refine ⟨9432143943101601023922365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6288095962067734015948243 9432143943101601023922365)
                    ·
                      refine ⟨3537053978663100383970887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9432143943101601023922365 3537053978663100383970887)
                      ·
                        rfl

theorem cell23_6888388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_6888388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888388 prefixEnd_6888388 := by exact prefixLift 6888388
  have htrace : WordTrace (prefixWord ++ tailWord_6888388) baseStart_6888388 baseEnd_6888388 := by
    simpa [prefixWord, tailWord_6888388, baseEnd_6888388] using wordTrace_append hprefix tailTrace_6888388
  have hstable : (prefixWord ++ tailWord_6888388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888388).length < 2 ^ (prefixWord ++ tailWord_6888388).sum := by decide
  have hdescent : baseEnd_6888388 < baseStart_6888388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888410 : List Nat := [3, 1, 1, 2, 4, 1, 2, 1, 2, 3, 3]
def baseStart_6888410 : Nat := 118140960795 + 6888410 * 2 ^ 59
def prefixEnd_6888410 : Nat := 4983230072969 + 3 ^ 40 * 6888410 * 2
def baseEnd_6888410 : Nat := 3537065275237499297895785

theorem tailTrace_6888410 : CollatzResearch.WordTrace tailWord_6888410 prefixEnd_6888410 3537065275237499297895785 := by
  unfold tailWord_6888410
  simp only [CollatzResearch.WordTrace]
  refine ⟨62810238243618622902849671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167493968649649661074265789 62810238243618622902849671)
  ·
    refine ⟨94215357365427934354274507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62810238243618622902849671 94215357365427934354274507)
    ·
      refine ⟨141323036048141901531411761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94215357365427934354274507 141323036048141901531411761)
      ·
        refine ⟨105992277036106426148558821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141323036048141901531411761 105992277036106426148558821)
        ·
          refine ⟨19873551944269954902854779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105992277036106426148558821 19873551944269954902854779)
          ·
            refine ⟨29810327916404932354282169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19873551944269954902854779 29810327916404932354282169)
            ·
              refine ⟨22357745937303699265711627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29810327916404932354282169 22357745937303699265711627)
              ·
                refine ⟨33536618905955548898567441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22357745937303699265711627 33536618905955548898567441)
                ·
                  refine ⟨25152464179466661673925581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33536618905955548898567441 25152464179466661673925581)
                  ·
                    refine ⟨9432174067299998127722093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25152464179466661673925581 9432174067299998127722093)
                    ·
                      refine ⟨3537065275237499297895785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9432174067299998127722093 3537065275237499297895785)
                      ·
                        rfl

theorem cell23_6888410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_6888410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888410 prefixEnd_6888410 := by exact prefixLift 6888410
  have htrace : WordTrace (prefixWord ++ tailWord_6888410) baseStart_6888410 baseEnd_6888410 := by
    simpa [prefixWord, tailWord_6888410, baseEnd_6888410] using wordTrace_append hprefix tailTrace_6888410
  have hstable : (prefixWord ++ tailWord_6888410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888410).length < 2 ^ (prefixWord ++ tailWord_6888410).sum := by decide
  have hdescent : baseEnd_6888410 < baseStart_6888410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888494 : List Nat := [4, 1, 3, 1, 1, 1, 2, 5, 1, 4]
def baseStart_6888494 : Nat := 118140960795 + 6888494 * 2 ^ 59
def prefixEnd_6888494 : Nat := 4983230072969 + 3 ^ 40 * 6888494 * 2
def baseEnd_6888494 : Nat := 1179036135870825656415133

theorem tailTrace_6888494 : CollatzResearch.WordTrace tailWord_6888494 prefixEnd_6888494 1179036135870825656415133 := by
  unfold tailWord_6888494
  simp only [CollatzResearch.WordTrace]
  refine ⟨31405502088271271744682067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167496011137446782638304357 31405502088271271744682067)
  ·
    refine ⟨47108253132406907617023101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31405502088271271744682067 47108253132406907617023101)
    ·
      refine ⟨17665594924652590356383663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47108253132406907617023101 17665594924652590356383663)
      ·
        refine ⟨26498392386978885534575495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17665594924652590356383663 26498392386978885534575495)
        ·
          refine ⟨39747588580468328301863243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26498392386978885534575495 39747588580468328301863243)
          ·
            refine ⟨59621382870702492452794865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39747588580468328301863243 59621382870702492452794865)
            ·
              refine ⟨44716037153026869339596149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59621382870702492452794865 44716037153026869339596149)
              ·
                refine ⟨4192128483096269000587139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44716037153026869339596149 4192128483096269000587139)
                ·
                  refine ⟨6288192724644403500880709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4192128483096269000587139 6288192724644403500880709)
                  ·
                    refine ⟨1179036135870825656415133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6288192724644403500880709 1179036135870825656415133)
                    ·
                      rfl

theorem cell23_6888494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_6888494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888494 prefixEnd_6888494 := by exact prefixLift 6888494
  have htrace : WordTrace (prefixWord ++ tailWord_6888494) baseStart_6888494 baseEnd_6888494 := by
    simpa [prefixWord, tailWord_6888494, baseEnd_6888494] using wordTrace_append hprefix tailTrace_6888494
  have hstable : (prefixWord ++ tailWord_6888494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888494).length < 2 ^ (prefixWord ++ tailWord_6888494).sum := by decide
  have hdescent : baseEnd_6888494 < baseStart_6888494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888523 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 4]
def baseStart_6888523 : Nat := 118140960795 + 6888523 * 2 ^ 59
def prefixEnd_6888523 : Nat := 4983230072969 + 3 ^ 40 * 6888523 * 2
def baseEnd_6888523 : Nat := 3537123298551457355782765

theorem tailTrace_6888523 : CollatzResearch.WordTrace tailWord_6888523 prefixEnd_6888523 3537123298551457355782765 := by
  unfold tailWord_6888523
  simp only [CollatzResearch.WordTrace]
  refine ⟨251245074423065111910262223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167496716282043407940174815 251245074423065111910262223)
  ·
    refine ⟨376867611634597667865393335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251245074423065111910262223 376867611634597667865393335)
    ·
      refine ⟨565301417451896501798090003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376867611634597667865393335 565301417451896501798090003)
      ·
        refine ⟨847952126177844752697135005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565301417451896501798090003 847952126177844752697135005)
        ·
          refine ⟨317982047316691782261425627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 847952126177844752697135005 317982047316691782261425627)
          ·
            refine ⟨476973070975037673392138441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317982047316691782261425627 476973070975037673392138441)
            ·
              refine ⟨357729803231278255044103831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 476973070975037673392138441 357729803231278255044103831)
              ·
                refine ⟨536594704846917382566155747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357729803231278255044103831 536594704846917382566155747)
                ·
                  refine ⟨804892057270376073849233621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 536594704846917382566155747 804892057270376073849233621)
                  ·
                    refine ⟨18864657592274439230841413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 804892057270376073849233621 18864657592274439230841413)
                    ·
                      refine ⟨3537123298551457355782765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18864657592274439230841413 3537123298551457355782765)
                      ·
                        rfl

theorem cell23_6888523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 4].length) (baseStart_6888523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888523 prefixEnd_6888523 := by exact prefixLift 6888523
  have htrace : WordTrace (prefixWord ++ tailWord_6888523) baseStart_6888523 baseEnd_6888523 := by
    simpa [prefixWord, tailWord_6888523, baseEnd_6888523] using wordTrace_append hprefix tailTrace_6888523
  have hstable : (prefixWord ++ tailWord_6888523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888523).length < 2 ^ (prefixWord ++ tailWord_6888523).sum := by decide
  have hdescent : baseEnd_6888523 < baseStart_6888523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888551 : List Nat := [1, 1, 5, 1, 1, 4, 2, 3, 1, 1, 3]
def baseStart_6888551 : Nat := 118140960795 + 6888551 * 2 ^ 59
def prefixEnd_6888551 : Nat := 4983230072969 + 3 ^ 40 * 6888551 * 2
def baseEnd_6888551 : Nat := 3537137676009783246232637

theorem tailTrace_6888551 : CollatzResearch.WordTrace tailWord_6888551 prefixEnd_6888551 3537137676009783246232637 := by
  unfold tailWord_6888551
  simp only [CollatzResearch.WordTrace]
  refine ⟨251246095666963672692281507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167497397111309115128187671 251246095666963672692281507)
  ·
    refine ⟨376869143500445509038422261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251246095666963672692281507 376869143500445509038422261)
    ·
      refine ⟨35331482203166766472352087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 376869143500445509038422261 35331482203166766472352087)
      ·
        refine ⟨52997223304750149708528131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35331482203166766472352087 52997223304750149708528131)
        ·
          refine ⟨79495834957125224562792197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52997223304750149708528131 79495834957125224562792197)
          ·
            refine ⟨14905469054460979605523537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79495834957125224562792197 14905469054460979605523537)
            ·
              refine ⟨11179101790845734704142653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14905469054460979605523537 11179101790845734704142653)
              ·
                refine ⟨4192163171567150514053495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11179101790845734704142653 4192163171567150514053495)
                ·
                  refine ⟨6288244757350725771080243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4192163171567150514053495 6288244757350725771080243)
                  ·
                    refine ⟨9432367136026088656620365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6288244757350725771080243 9432367136026088656620365)
                    ·
                      refine ⟨3537137676009783246232637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9432367136026088656620365 3537137676009783246232637)
                      ·
                        rfl

theorem cell23_6888551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_6888551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888551 prefixEnd_6888551 := by exact prefixLift 6888551
  have htrace : WordTrace (prefixWord ++ tailWord_6888551) baseStart_6888551 baseEnd_6888551 := by
    simpa [prefixWord, tailWord_6888551, baseEnd_6888551] using wordTrace_append hprefix tailTrace_6888551
  have hstable : (prefixWord ++ tailWord_6888551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888551).length < 2 ^ (prefixWord ++ tailWord_6888551).sum := by decide
  have hdescent : baseEnd_6888551 < baseStart_6888551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888554 : List Nat := [3, 1, 3, 2, 2, 1, 4, 1, 1, 5]
def baseStart_6888554 : Nat := 118140960795 + 6888554 * 2 ^ 59
def prefixEnd_6888554 : Nat := 4983230072969 + 3 ^ 40 * 6888554 * 2
def baseEnd_6888554 : Nat := 1179046405483915578165041

theorem tailTrace_6888554 : CollatzResearch.WordTrace tailWord_6888554 prefixEnd_6888554 1179046405483915578165041 := by
  unfold tailWord_6888554
  simp only [CollatzResearch.WordTrace]
  refine ⟨62811551271488201051160179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167497470057301869469760477 62811551271488201051160179)
  ·
    refine ⟨94217326907232301576740269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62811551271488201051160179 94217326907232301576740269)
    ·
      refine ⟨35331497590212113091277601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94217326907232301576740269 35331497590212113091277601)
      ·
        refine ⟨26498623192659084818458201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35331497590212113091277601 26498623192659084818458201)
        ·
          refine ⟨19873967394494313613843651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26498623192659084818458201 19873967394494313613843651)
          ·
            refine ⟨29810951091741470420765477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19873967394494313613843651 29810951091741470420765477)
            ·
              refine ⟨5589553329701525703893527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29810951091741470420765477 5589553329701525703893527)
              ·
                refine ⟨8384329994552288555840291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5589553329701525703893527 8384329994552288555840291)
                ·
                  refine ⟨12576494991828432833760437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8384329994552288555840291 12576494991828432833760437)
                  ·
                    refine ⟨1179046405483915578165041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12576494991828432833760437 1179046405483915578165041)
                    ·
                      rfl

theorem cell23_6888554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_6888554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888554 prefixEnd_6888554 := by exact prefixLift 6888554
  have htrace : WordTrace (prefixWord ++ tailWord_6888554) baseStart_6888554 baseEnd_6888554 := by
    simpa [prefixWord, tailWord_6888554, baseEnd_6888554] using wordTrace_append hprefix tailTrace_6888554
  have hstable : (prefixWord ++ tailWord_6888554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888554).length < 2 ^ (prefixWord ++ tailWord_6888554).sum := by decide
  have hdescent : baseEnd_6888554 < baseStart_6888554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888560 : List Nat := [2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 5]
def baseStart_6888560 : Nat := 118140960795 + 6888560 * 2 ^ 59
def prefixEnd_6888560 : Nat := 4983230072969 + 3 ^ 40 * 6888560 * 2
def baseEnd_6888560 : Nat := 3537142297335673711020095

theorem tailTrace_6888560 : CollatzResearch.WordTrace tailWord_6888560 prefixEnd_6888560 3537142297335673711020095 := by
  unfold tailWord_6888560
  simp only [CollatzResearch.WordTrace]
  refine ⟨125623211961965533614679567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167497615949287378152906089 125623211961965533614679567)
  ·
    refine ⟨188434817942948300422019351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125623211961965533614679567 188434817942948300422019351)
    ·
      refine ⟨282652226914422450633029027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188434817942948300422019351 282652226914422450633029027)
      ·
        refine ⟨423978340371633675949543541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282652226914422450633029027 423978340371633675949543541)
        ·
          refine ⟨39747969409840657120269707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 423978340371633675949543541 39747969409840657120269707)
          ·
            refine ⟨59621954114760985680404561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39747969409840657120269707 59621954114760985680404561)
            ·
              refine ⟨44716465586070739260303421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59621954114760985680404561 44716465586070739260303421)
              ·
                refine ⟨16768674594776527222613783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44716465586070739260303421 16768674594776527222613783)
                ·
                  refine ⟨25153011892164790833920675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16768674594776527222613783 25153011892164790833920675)
                  ·
                    refine ⟨37729517838247186250881013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25153011892164790833920675 37729517838247186250881013)
                    ·
                      refine ⟨3537142297335673711020095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37729517838247186250881013 3537142297335673711020095)
                      ·
                        rfl

theorem cell23_6888560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 5].length) (baseStart_6888560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888560 prefixEnd_6888560 := by exact prefixLift 6888560
  have htrace : WordTrace (prefixWord ++ tailWord_6888560) baseStart_6888560 baseEnd_6888560 := by
    simpa [prefixWord, tailWord_6888560, baseEnd_6888560] using wordTrace_append hprefix tailTrace_6888560
  have hstable : (prefixWord ++ tailWord_6888560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888560).length < 2 ^ (prefixWord ++ tailWord_6888560).sum := by decide
  have hdescent : baseEnd_6888560 < baseStart_6888560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888577 : List Nat := [1, 2, 4, 2, 2, 2, 1, 2, 1, 1, 5]
def baseStart_6888577 : Nat := 118140960795 + 6888577 * 2 ^ 59
def prefixEnd_6888577 : Nat := 4983230072969 + 3 ^ 40 * 6888577 * 2
def baseEnd_6888577 : Nat := 3537151026506800144507517

theorem tailTrace_6888577 : CollatzResearch.WordTrace tailWord_6888577 prefixEnd_6888577 3537151026506800144507517 := by
  unfold tailWord_6888577
  simp only [CollatzResearch.WordTrace]
  refine ⟨251247043964869479132727985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167498029309912986088485323 251247043964869479132727985)
  ·
    refine ⟨188435282973652109349545989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251247043964869479132727985 188435282973652109349545989)
    ·
      refine ⟨35331615557559770503039873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188435282973652109349545989 35331615557559770503039873)
      ·
        refine ⟨26498711668169827877279905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35331615557559770503039873 26498711668169827877279905)
        ·
          refine ⟨19874033751127370907959929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26498711668169827877279905 19874033751127370907959929)
          ·
            refine ⟨14905525313345528180969947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19874033751127370907959929 14905525313345528180969947)
            ·
              refine ⟨22358287970018292271454921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14905525313345528180969947 22358287970018292271454921)
              ·
                refine ⟨16768715977513719203591191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22358287970018292271454921 16768715977513719203591191)
                ·
                  refine ⟨25153073966270578805386787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16768715977513719203591191 25153073966270578805386787)
                  ·
                    refine ⟨37729610949405868208080181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25153073966270578805386787 37729610949405868208080181)
                    ·
                      refine ⟨3537151026506800144507517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37729610949405868208080181 3537151026506800144507517)
                      ·
                        rfl

theorem cell23_6888577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_6888577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888577 prefixEnd_6888577 := by exact prefixLift 6888577
  have htrace : WordTrace (prefixWord ++ tailWord_6888577) baseStart_6888577 baseEnd_6888577 := by
    simpa [prefixWord, tailWord_6888577, baseEnd_6888577] using wordTrace_append hprefix tailTrace_6888577
  have hstable : (prefixWord ++ tailWord_6888577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888577).length < 2 ^ (prefixWord ++ tailWord_6888577).sum := by decide
  have hdescent : baseEnd_6888577 < baseStart_6888577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888584 : List Nat := [2, 1, 3, 4, 2, 2, 1, 1, 1, 6]
def baseStart_6888584 : Nat := 118140960795 + 6888584 * 2 ^ 59
def prefixEnd_6888584 : Nat := 4983230072969 + 3 ^ 40 * 6888584 * 2
def baseEnd_6888584 : Nat := 1179051540290460539039995

theorem tailTrace_6888584 : CollatzResearch.WordTrace tailWord_6888584 prefixEnd_6888584 1179051540290460539039995 := by
  unfold tailWord_6888584
  simp only [CollatzResearch.WordTrace]
  refine ⟨125623649637922059664116403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167498199517229412885488537 125623649637922059664116403)
  ·
    refine ⟨188435474456883089496174605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125623649637922059664116403 188435474456883089496174605)
    ·
      refine ⟨70663302921331158561065477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188435474456883089496174605 70663302921331158561065477)
      ·
        refine ⟨13249369297749592230199777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70663302921331158561065477 13249369297749592230199777)
        ·
          refine ⟨9937026973312194172649833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13249369297749592230199777 9937026973312194172649833)
          ·
            refine ⟨7452770229984145629487375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9937026973312194172649833 7452770229984145629487375)
            ·
              refine ⟨11179155344976218444231063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7452770229984145629487375 11179155344976218444231063)
              ·
                refine ⟨16768733017464327666346595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11179155344976218444231063 16768733017464327666346595)
                ·
                  refine ⟨25153099526196491499519893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16768733017464327666346595 25153099526196491499519893)
                  ·
                    refine ⟨1179051540290460539039995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25153099526196491499519893 1179051540290460539039995)
                    ·
                      rfl

theorem cell23_6888584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_6888584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888584 prefixEnd_6888584 := by exact prefixLift 6888584
  have htrace : WordTrace (prefixWord ++ tailWord_6888584) baseStart_6888584 baseEnd_6888584 := by
    simpa [prefixWord, tailWord_6888584, baseEnd_6888584] using wordTrace_append hprefix tailTrace_6888584
  have hstable : (prefixWord ++ tailWord_6888584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888584).length < 2 ^ (prefixWord ++ tailWord_6888584).sum := by decide
  have hdescent : baseEnd_6888584 < baseStart_6888584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888594 : List Nat := [3, 2, 3, 1, 1, 2, 1, 4, 1, 2, 3]
def baseStart_6888594 : Nat := 118140960795 + 6888594 * 2 ^ 59
def prefixEnd_6888594 : Nat := 4983230072969 + 3 ^ 40 * 6888594 * 2
def baseEnd_6888594 : Nat := 3537159755677926577994939

theorem tailTrace_6888594 : CollatzResearch.WordTrace tailWord_6888594 prefixEnd_6888594 3537159755677926577994939 := by
  unfold tailWord_6888594
  simp only [CollatzResearch.WordTrace]
  refine ⟨62811916001451972759024209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167498442670538594024064557 62811916001451972759024209)
  ·
    refine ⟨47108937001088979569268157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62811916001451972759024209 47108937001088979569268157)
    ·
      refine ⟨17665851375408367338475559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47108937001088979569268157 17665851375408367338475559)
      ·
        refine ⟨26498777063112551007713339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17665851375408367338475559 26498777063112551007713339)
        ·
          refine ⟨39748165594668826511570009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26498777063112551007713339 39748165594668826511570009)
          ·
            refine ⟨29811124196001619883677507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39748165594668826511570009 29811124196001619883677507)
            ·
              refine ⟨44716686294002429825516261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29811124196001619883677507 44716686294002429825516261)
              ·
                refine ⟨8384378680125455592284299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44716686294002429825516261 8384378680125455592284299)
                ·
                  refine ⟨12576568020188183388426449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8384378680125455592284299 12576568020188183388426449)
                  ·
                    refine ⟨9432426015141137541319837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12576568020188183388426449 9432426015141137541319837)
                    ·
                      refine ⟨3537159755677926577994939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9432426015141137541319837 3537159755677926577994939)
                      ·
                        rfl

theorem cell23_6888594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_6888594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888594 prefixEnd_6888594 := by exact prefixLift 6888594
  have htrace : WordTrace (prefixWord ++ tailWord_6888594) baseStart_6888594 baseEnd_6888594 := by
    simpa [prefixWord, tailWord_6888594, baseEnd_6888594] using wordTrace_append hprefix tailTrace_6888594
  have hstable : (prefixWord ++ tailWord_6888594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888594).length < 2 ^ (prefixWord ++ tailWord_6888594).sum := by decide
  have hdescent : baseEnd_6888594 < baseStart_6888594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888625 : List Nat := [1, 2, 2, 5, 1, 2, 3, 2, 1, 2, 2]
def baseStart_6888625 : Nat := 118140960795 + 6888625 * 2 ^ 59
def prefixEnd_6888625 : Nat := 4983230072969 + 3 ^ 40 * 6888625 * 2
def baseEnd_6888625 : Nat := 3537175673578215956707297

theorem tailTrace_6888625 : CollatzResearch.WordTrace tailWord_6888625 prefixEnd_6888625 3537175673578215956707297 := by
  unfold tailWord_6888625
  simp only [CollatzResearch.WordTrace]
  refine ⟨251248794668695583330475329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167499196445797055553650219 251248794668695583330475329)
  ·
    refine ⟨188436596001521687497856497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251248794668695583330475329 188436596001521687497856497)
    ·
      refine ⟨141327447001141265623392373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188436596001521687497856497 141327447001141265623392373)
      ·
        refine ⟨13249448156356993652193035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141327447001141265623392373 13249448156356993652193035)
        ·
          refine ⟨19874172234535490478289553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13249448156356993652193035 19874172234535490478289553)
          ·
            refine ⟨14905629175901617858717165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19874172234535490478289553 14905629175901617858717165)
            ·
              refine ⟨5589610940963106697018937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14905629175901617858717165 5589610940963106697018937)
              ·
                refine ⟨4192208205722330022764203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5589610940963106697018937 4192208205722330022764203)
                ·
                  refine ⟨6288312308583495034146305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4192208205722330022764203 6288312308583495034146305)
                  ·
                    refine ⟨4716234231437621275609729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6288312308583495034146305 4716234231437621275609729)
                    ·
                      refine ⟨3537175673578215956707297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4716234231437621275609729 3537175673578215956707297)
                      ·
                        rfl

theorem cell23_6888625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_6888625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888625 prefixEnd_6888625 := by exact prefixLift 6888625
  have htrace : WordTrace (prefixWord ++ tailWord_6888625) baseStart_6888625 baseEnd_6888625 := by
    simpa [prefixWord, tailWord_6888625, baseEnd_6888625] using wordTrace_append hprefix tailTrace_6888625
  have hstable : (prefixWord ++ tailWord_6888625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888625).length < 2 ^ (prefixWord ++ tailWord_6888625).sum := by decide
  have hdescent : baseEnd_6888625 < baseStart_6888625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888647 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 5, 4, 2]
def baseStart_6888647 : Nat := 118140960795 + 6888647 * 2 ^ 59
def prefixEnd_6888647 : Nat := 4983230072969 + 3 ^ 40 * 6888647 * 2
def baseEnd_6888647 : Nat := 3537186970152614870632195

theorem tailTrace_6888647 : CollatzResearch.WordTrace tailWord_6888647 prefixEnd_6888647 3537186970152614870632195 := by
  unfold tailWord_6888647
  simp only [CollatzResearch.WordTrace]
  refine ⟨251249597074615881087776195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167499731383077254058517463 251249597074615881087776195)
  ·
    refine ⟨376874395611923821631664293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251249597074615881087776195 376874395611923821631664293)
    ·
      refine ⟨70663949177235716555937055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 376874395611923821631664293 70663949177235716555937055)
      ·
        refine ⟨105995923765853574833905583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70663949177235716555937055 105995923765853574833905583)
        ·
          refine ⟨158993885648780362250858375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105995923765853574833905583 158993885648780362250858375)
          ·
            refine ⟨238490828473170543376287563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158993885648780362250858375 238490828473170543376287563)
            ·
              refine ⟨357736242709755815064431345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238490828473170543376287563 357736242709755815064431345)
              ·
                refine ⟨268302182032316861298323509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 357736242709755815064431345 268302182032316861298323509)
                ·
                  refine ⟨25153329565529705746717829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 268302182032316861298323509 25153329565529705746717829)
                  ·
                    refine ⟨4716249293536819827509593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25153329565529705746717829 4716249293536819827509593)
                    ·
                      refine ⟨3537186970152614870632195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4716249293536819827509593 3537186970152614870632195)
                      ·
                        rfl

theorem cell23_6888647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 4, 2].length) (baseStart_6888647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888647 prefixEnd_6888647 := by exact prefixLift 6888647
  have htrace : WordTrace (prefixWord ++ tailWord_6888647) baseStart_6888647 baseEnd_6888647 := by
    simpa [prefixWord, tailWord_6888647, baseEnd_6888647] using wordTrace_append hprefix tailTrace_6888647
  have hstable : (prefixWord ++ tailWord_6888647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888647).length < 2 ^ (prefixWord ++ tailWord_6888647).sum := by decide
  have hdescent : baseEnd_6888647 < baseStart_6888647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888697 : List Nat := [1, 2, 1, 3, 1, 1, 5, 1, 2, 3, 3]
def baseStart_6888697 : Nat := 118140960795 + 6888697 * 2 ^ 59
def prefixEnd_6888697 : Nat := 4983230072969 + 3 ^ 40 * 6888697 * 2
def baseEnd_6888697 : Nat := 3537212644185339675006965

theorem tailTrace_6888697 : CollatzResearch.WordTrace tailWord_6888697 prefixEnd_6888697 3537212644185339675006965 := by
  unfold tailWord_6888697
  simp only [CollatzResearch.WordTrace]
  refine ⟨251251420724434739627096345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167500947149623159751397563 251251420724434739627096345)
  ·
    refine ⟨188438565543326054720322259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251251420724434739627096345 188438565543326054720322259)
    ·
      refine ⟨282657848314989082080483389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188438565543326054720322259 282657848314989082080483389)
      ·
        refine ⟨105996693118120905780181271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282657848314989082080483389 105996693118120905780181271)
        ·
          refine ⟨158995039677181358670271907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105996693118120905780181271 158995039677181358670271907)
          ·
            refine ⟨238492559515772038005407861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158995039677181358670271907 238492559515772038005407861)
            ·
              refine ⟨22358677454603628563006987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 238492559515772038005407861 22358677454603628563006987)
              ·
                refine ⟨33538016181905442844510481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22358677454603628563006987 33538016181905442844510481)
                ·
                  refine ⟨25153512136429082133382861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33538016181905442844510481 25153512136429082133382861)
                  ·
                    refine ⟨9432567051160905800018573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25153512136429082133382861 9432567051160905800018573)
                    ·
                      refine ⟨3537212644185339675006965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9432567051160905800018573 3537212644185339675006965)
                      ·
                        rfl

theorem cell23_6888697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_6888697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888697 prefixEnd_6888697 := by exact prefixLift 6888697
  have htrace : WordTrace (prefixWord ++ tailWord_6888697) baseStart_6888697 baseEnd_6888697 := by
    simpa [prefixWord, tailWord_6888697, baseEnd_6888697] using wordTrace_append hprefix tailTrace_6888697
  have hstable : (prefixWord ++ tailWord_6888697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888697).length < 2 ^ (prefixWord ++ tailWord_6888697).sum := by decide
  have hdescent : baseEnd_6888697 < baseStart_6888697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888737 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 4, 1, 4]
def baseStart_6888737 : Nat := 118140960795 + 6888737 * 2 ^ 59
def prefixEnd_6888737 : Nat := 4983230072969 + 3 ^ 40 * 6888737 * 2
def baseEnd_6888737 : Nat := 3537233183411519518506781

theorem tailTrace_6888737 : CollatzResearch.WordTrace tailWord_6888737 prefixEnd_6888737 3537233183411519518506781 := by
  unfold tailWord_6888737
  simp only [CollatzResearch.WordTrace]
  refine ⟨251252879644289826458552465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167501919762859884305701643 251252879644289826458552465)
  ·
    refine ⟨188439659733217369843914349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251252879644289826458552465 188439659733217369843914349)
    ·
      refine ⟨70664872399956513691467881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188439659733217369843914349 70664872399956513691467881)
      ·
        refine ⟨52998654299967385268600911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70664872399956513691467881 52998654299967385268600911)
        ·
          refine ⟨79497981449951077902901367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52998654299967385268600911 79497981449951077902901367)
          ·
            refine ⟨119246972174926616854352051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79497981449951077902901367 119246972174926616854352051)
            ·
              refine ⟨178870458262389925281528077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119246972174926616854352051 178870458262389925281528077)
              ·
                refine ⟨67076421848396221980573029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178870458262389925281528077 67076421848396221980573029)
                ·
                  refine ⟨12576829096574291621357443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67076421848396221980573029 12576829096574291621357443)
                  ·
                    refine ⟨18865243644861437432036165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12576829096574291621357443 18865243644861437432036165)
                    ·
                      refine ⟨3537233183411519518506781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18865243644861437432036165 3537233183411519518506781)
                      ·
                        rfl

theorem cell23_6888737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_6888737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888737 prefixEnd_6888737 := by exact prefixLift 6888737
  have htrace : WordTrace (prefixWord ++ tailWord_6888737) baseStart_6888737 baseEnd_6888737 := by
    simpa [prefixWord, tailWord_6888737, baseEnd_6888737] using wordTrace_append hprefix tailTrace_6888737
  have hstable : (prefixWord ++ tailWord_6888737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888737).length < 2 ^ (prefixWord ++ tailWord_6888737).sum := by decide
  have hdescent : baseEnd_6888737 < baseStart_6888737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888764 : List Nat := [2, 2, 2, 2, 1, 3, 2, 2, 3, 4]
def baseStart_6888764 : Nat := 118140960795 + 6888764 * 2 ^ 59
def prefixEnd_6888764 : Nat := 4983230072969 + 3 ^ 40 * 6888764 * 2
def baseEnd_6888764 : Nat := 1179082349129730304289719

theorem tailTrace_6888764 : CollatzResearch.WordTrace tailWord_6888764 prefixEnd_6888764 1179082349129730304289719 := by
  unfold tailWord_6888764
  simp only [CollatzResearch.WordTrace]
  refine ⟨125626932207596005034892673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167502576276794673379856897 125626932207596005034892673)
  ·
    refine ⟨94220199155697003776169505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125626932207596005034892673 94220199155697003776169505)
    ·
      refine ⟨70665149366772752832127129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94220199155697003776169505 70665149366772752832127129)
      ·
        refine ⟨52998862025079564624095347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70665149366772752832127129 52998862025079564624095347)
        ·
          refine ⟨79498293037619346936143021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52998862025079564624095347 79498293037619346936143021)
          ·
            refine ⟨29811859889107255101053633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79498293037619346936143021 29811859889107255101053633)
            ·
              refine ⟨22358894916830441325790225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29811859889107255101053633 22358894916830441325790225)
              ·
                refine ⟨16769171187622830994342669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22358894916830441325790225 16769171187622830994342669)
                ·
                  refine ⟨6288439195358561622878501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16769171187622830994342669 6288439195358561622878501)
                  ·
                    refine ⟨1179082349129730304289719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6288439195358561622878501 1179082349129730304289719)
                    ·
                      rfl

theorem cell23_6888764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_6888764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888764 prefixEnd_6888764 := by exact prefixLift 6888764
  have htrace : WordTrace (prefixWord ++ tailWord_6888764) baseStart_6888764 baseEnd_6888764 := by
    simpa [prefixWord, tailWord_6888764, baseEnd_6888764] using wordTrace_append hprefix tailTrace_6888764
  have hstable : (prefixWord ++ tailWord_6888764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888764).length < 2 ^ (prefixWord ++ tailWord_6888764).sum := by decide
  have hdescent : baseEnd_6888764 < baseStart_6888764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888837 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 3, 6]
def baseStart_6888837 : Nat := 118140960795 + 6888837 * 2 ^ 59
def prefixEnd_6888837 : Nat := 4983230072969 + 3 ^ 40 * 6888837 * 2
def baseEnd_6888837 : Nat := 1179094843825656375752107

theorem tailTrace_6888837 : CollatzResearch.WordTrace tailWord_6888837 prefixEnd_6888837 1179094843825656375752107 := by
  unfold tailWord_6888837
  simp only [CollatzResearch.WordTrace]
  refine ⟨251256526943927543537192765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167504351295951695691461843 251256526943927543537192765)
  ·
    refine ⟨94221197603972828826447287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251256526943927543537192765 94221197603972828826447287)
    ·
      refine ⟨141331796405959243239670931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94221197603972828826447287 141331796405959243239670931)
      ·
        refine ⟨211997694608938864859506397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141331796405959243239670931 211997694608938864859506397)
        ·
          refine ⟨79499135478352074322314899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211997694608938864859506397 79499135478352074322314899)
          ·
            refine ⟨119248703217528111483472349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79499135478352074322314899 119248703217528111483472349)
            ·
              refine ⟨44718263706573041806302131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119248703217528111483472349 44718263706573041806302131)
              ·
                refine ⟨67077395559859562709453197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44718263706573041806302131 67077395559859562709453197)
                ·
                  refine ⟨25154023334947336016044949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67077395559859562709453197 25154023334947336016044949)
                  ·
                    refine ⟨1179094843825656375752107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25154023334947336016044949 1179094843825656375752107)
                    ·
                      rfl

theorem cell23_6888837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 6].length) (baseStart_6888837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888837 prefixEnd_6888837 := by exact prefixLift 6888837
  have htrace : WordTrace (prefixWord ++ tailWord_6888837) baseStart_6888837 baseEnd_6888837 := by
    simpa [prefixWord, tailWord_6888837, baseEnd_6888837] using wordTrace_append hprefix tailTrace_6888837
  have hstable : (prefixWord ++ tailWord_6888837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888837).length < 2 ^ (prefixWord ++ tailWord_6888837).sum := by decide
  have hdescent : baseEnd_6888837 < baseStart_6888837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888864 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 3]
def baseStart_6888864 : Nat := 118140960795 + 6888864 * 2 ^ 59
def prefixEnd_6888864 : Nat := 4983230072969 + 3 ^ 40 * 6888864 * 2
def baseEnd_6888864 : Nat := 3537298395454640521618697

theorem tailTrace_6888864 : CollatzResearch.WordTrace tailWord_6888864 prefixEnd_6888864 3537298395454640521618697 := by
  unfold tailWord_6888864
  simp only [CollatzResearch.WordTrace]
  refine ⟨125628755857414863574212823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167505007809886484765617097 125628755857414863574212823)
  ·
    refine ⟨188443133786122295361319235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125628755857414863574212823 188443133786122295361319235)
    ·
      refine ⟨282664700679183443041978853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188443133786122295361319235 282664700679183443041978853)
      ·
        refine ⟨52999631377346895570371035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 282664700679183443041978853 52999631377346895570371035)
        ·
          refine ⟨79499447066020343355556553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52999631377346895570371035 79499447066020343355556553)
          ·
            refine ⟨59624585299515257516667415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79499447066020343355556553 59624585299515257516667415)
            ·
              refine ⟨89436877949272886275001123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59624585299515257516667415 89436877949272886275001123)
              ·
                refine ⟨134155316923909329412501685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89436877949272886275001123 134155316923909329412501685)
                ·
                  refine ⟨12577060961616499632422033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134155316923909329412501685 12577060961616499632422033)
                  ·
                    refine ⟨9432795721212374724316525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12577060961616499632422033 9432795721212374724316525)
                    ·
                      refine ⟨3537298395454640521618697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9432795721212374724316525 3537298395454640521618697)
                      ·
                        rfl

theorem cell23_6888864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_6888864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888864 prefixEnd_6888864 := by exact prefixLift 6888864
  have htrace : WordTrace (prefixWord ++ tailWord_6888864) baseStart_6888864 baseEnd_6888864 := by
    simpa [prefixWord, tailWord_6888864, baseEnd_6888864] using wordTrace_append hprefix tailTrace_6888864
  have hstable : (prefixWord ++ tailWord_6888864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888864).length < 2 ^ (prefixWord ++ tailWord_6888864).sum := by decide
  have hdescent : baseEnd_6888864 < baseStart_6888864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888871 : List Nat := [1, 1, 6, 1, 1, 1, 1, 5, 2, 4]
def baseStart_6888871 : Nat := 118140960795 + 6888871 * 2 ^ 59
def prefixEnd_6888871 : Nat := 4983230072969 + 3 ^ 40 * 6888871 * 2
def baseEnd_6888871 : Nat := 1179100663273073998077055

theorem tailTrace_6888871 : CollatzResearch.WordTrace tailWord_6888871 prefixEnd_6888871 1179100663273073998077055 := by
  unfold tailWord_6888871
  simp only [CollatzResearch.WordTrace]
  refine ⟨251257767025804367343930467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167505178017202911562620311 251257767025804367343930467)
  ·
    refine ⟨376886650538706551015895701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251257767025804367343930467 376886650538706551015895701)
    ·
      refine ⟨17666561744001869578870111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 376886650538706551015895701 17666561744001869578870111)
      ·
        refine ⟨26499842616002804368305167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17666561744001869578870111 26499842616002804368305167)
        ·
          refine ⟨39749763924004206552457751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26499842616002804368305167 39749763924004206552457751)
          ·
            refine ⟨59624645886006309828686627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39749763924004206552457751 59624645886006309828686627)
            ·
              refine ⟨89436968829009464743029941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59624645886006309828686627 89436968829009464743029941)
              ·
                refine ⟨8384715827719637319659057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89436968829009464743029941 8384715827719637319659057)
                ·
                  refine ⟨6288536870789727989744293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8384715827719637319659057 6288536870789727989744293)
                  ·
                    refine ⟨1179100663273073998077055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6288536870789727989744293 1179100663273073998077055)
                    ·
                      rfl

theorem cell23_6888871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_6888871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888871 prefixEnd_6888871 := by exact prefixLift 6888871
  have htrace : WordTrace (prefixWord ++ tailWord_6888871) baseStart_6888871 baseEnd_6888871 := by
    simpa [prefixWord, tailWord_6888871, baseEnd_6888871] using wordTrace_append hprefix tailTrace_6888871
  have hstable : (prefixWord ++ tailWord_6888871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888871).length < 2 ^ (prefixWord ++ tailWord_6888871).sum := by decide
  have hdescent : baseEnd_6888871 < baseStart_6888871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888881 : List Nat := [1, 2, 2, 4, 1, 1, 2, 4, 1, 2, 3]
def baseStart_6888881 : Nat := 118140960795 + 6888881 * 2 ^ 59
def prefixEnd_6888881 : Nat := 4983230072969 + 3 ^ 40 * 6888881 * 2
def baseEnd_6888881 : Nat := 3537307124625766955106119

theorem tailTrace_6888881 : CollatzResearch.WordTrace tailWord_6888881 prefixEnd_6888881 3537307124625766955106119 := by
  unfold tailWord_6888881
  simp only [CollatzResearch.WordTrace]
  refine ⟨251258131755768139051794497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167505421170512092701196331 251258131755768139051794497)
  ·
    refine ⟨188443598816826104288845873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251258131755768139051794497 188443598816826104288845873)
    ·
      refine ⟨141332699112619578216634405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188443598816826104288845873 141332699112619578216634405)
      ·
        refine ⟨26499881083616170915618951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141332699112619578216634405 26499881083616170915618951)
        ·
          refine ⟨39749821625424256373428427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26499881083616170915618951 39749821625424256373428427)
          ·
            refine ⟨59624732438136384560142641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39749821625424256373428427 59624732438136384560142641)
            ·
              refine ⟨44718549328602288420106981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59624732438136384560142641 44718549328602288420106981)
              ·
                refine ⟨8384727999112929078770059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44718549328602288420106981 8384727999112929078770059)
                ·
                  refine ⟨12577091998669393618155089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8384727999112929078770059 12577091998669393618155089)
                  ·
                    refine ⟨9432818999002045213616317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12577091998669393618155089 9432818999002045213616317)
                    ·
                      refine ⟨3537307124625766955106119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9432818999002045213616317 3537307124625766955106119)
                      ·
                        rfl

theorem cell23_6888881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_6888881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888881 prefixEnd_6888881 := by exact prefixLift 6888881
  have htrace : WordTrace (prefixWord ++ tailWord_6888881) baseStart_6888881 baseEnd_6888881 := by
    simpa [prefixWord, tailWord_6888881, baseEnd_6888881] using wordTrace_append hprefix tailTrace_6888881
  have hstable : (prefixWord ++ tailWord_6888881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888881).length < 2 ^ (prefixWord ++ tailWord_6888881).sum := by decide
  have hdescent : baseEnd_6888881 < baseStart_6888881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888954 : List Nat := [3, 1, 1, 1, 1, 2, 5, 1, 2, 1, 5]
def baseStart_6888954 : Nat := 118140960795 + 6888954 * 2 ^ 59
def prefixEnd_6888954 : Nat := 4983230072969 + 3 ^ 40 * 6888954 * 2
def baseEnd_6888954 : Nat := 3537344608713545169493283

theorem tailTrace_6888954 : CollatzResearch.WordTrace tailWord_6888954 prefixEnd_6888954 3537344608713545169493283 := by
  unfold tailWord_6888954
  simp only [CollatzResearch.WordTrace]
  refine ⟨62815198571125918129800479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167507196189669115012801277 62815198571125918129800479)
  ·
    refine ⟨94222797856688877194700719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62815198571125918129800479 94222797856688877194700719)
    ·
      refine ⟨141334196785033315792051079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94222797856688877194700719 141334196785033315792051079)
      ·
        refine ⟨212001295177549973688076619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141334196785033315792051079 212001295177549973688076619)
        ·
          refine ⟨318001942766324960532114929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212001295177549973688076619 318001942766324960532114929)
          ·
            refine ⟨238501457074743720399086197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318001942766324960532114929 238501457074743720399086197)
            ·
              refine ⟨22359511600757223787414331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 238501457074743720399086197 22359511600757223787414331)
              ·
                refine ⟨33539267401135835681121497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22359511600757223787414331 33539267401135835681121497)
                ·
                  refine ⟨25154450550851876760841123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33539267401135835681121497 25154450550851876760841123)
                  ·
                    refine ⟨37731675826277815141261685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25154450550851876760841123 37731675826277815141261685)
                    ·
                      refine ⟨3537344608713545169493283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37731675826277815141261685 3537344608713545169493283)
                      ·
                        rfl

theorem cell23_6888954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_6888954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888954 prefixEnd_6888954 := by exact prefixLift 6888954
  have htrace : WordTrace (prefixWord ++ tailWord_6888954) baseStart_6888954 baseEnd_6888954 := by
    simpa [prefixWord, tailWord_6888954, baseEnd_6888954] using wordTrace_append hprefix tailTrace_6888954
  have hstable : (prefixWord ++ tailWord_6888954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888954).length < 2 ^ (prefixWord ++ tailWord_6888954).sum := by decide
  have hdescent : baseEnd_6888954 < baseStart_6888954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6888968 : List Nat := [2, 1, 3, 2, 1, 1, 4, 1, 4, 2, 2]
def baseStart_6888968 : Nat := 118140960795 + 6888968 * 2 ^ 59
def prefixEnd_6888968 : Nat := 4983230072969 + 3 ^ 40 * 6888968 * 2
def baseEnd_6888968 : Nat := 3537351797442708114718219

theorem tailTrace_6888968 : CollatzResearch.WordTrace tailWord_6888968 prefixEnd_6888968 3537351797442708114718219 := by
  unfold tailWord_6888968
  simp only [CollatzResearch.WordTrace]
  refine ⟨125630652453226476455105779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167507536604301968606807705 125630652453226476455105779)
  ·
    refine ⟨188445978679839714682658669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125630652453226476455105779 188445978679839714682658669)
    ·
      refine ⟨70667242004939893005997001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188445978679839714682658669 70667242004939893005997001)
      ·
        refine ⟨53000431503704919754497751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70667242004939893005997001 53000431503704919754497751)
        ·
          refine ⟨79500647255557379631746627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53000431503704919754497751 79500647255557379631746627)
          ·
            refine ⟨119250970883336069447619941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79500647255557379631746627 119250970883336069447619941)
            ·
              refine ⟨22359557040625513021428739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119250970883336069447619941 22359557040625513021428739)
              ·
                refine ⟨33539335560938269532143109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22359557040625513021428739 33539335560938269532143109)
                ·
                  refine ⟨6288625417675925537276833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33539335560938269532143109 6288625417675925537276833)
                  ·
                    refine ⟨4716469063256944152957625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6288625417675925537276833 4716469063256944152957625)
                    ·
                      refine ⟨3537351797442708114718219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4716469063256944152957625 3537351797442708114718219)
                      ·
                        rfl

theorem cell23_6888968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_6888968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6888968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6888968 prefixEnd_6888968 := by exact prefixLift 6888968
  have htrace : WordTrace (prefixWord ++ tailWord_6888968) baseStart_6888968 baseEnd_6888968 := by
    simpa [prefixWord, tailWord_6888968, baseEnd_6888968] using wordTrace_append hprefix tailTrace_6888968
  have hstable : (prefixWord ++ tailWord_6888968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6888968).length < 2 ^ (prefixWord ++ tailWord_6888968).sum := by decide
  have hdescent : baseEnd_6888968 < baseStart_6888968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6888968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889024 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 4]
def baseStart_6889024 : Nat := 118140960795 + 6889024 * 2 ^ 59
def prefixEnd_6889024 : Nat := 4983230072969 + 3 ^ 40 * 6889024 * 2
def baseEnd_6889024 : Nat := 3537380552359359895617961

theorem tailTrace_6889024 : CollatzResearch.WordTrace tailWord_6889024 prefixEnd_6889024 3537380552359359895617961 := by
  unfold tailWord_6889024
  simp only [CollatzResearch.WordTrace]
  refine ⟨125631673697125037237125063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167508898262833382982833417 125631673697125037237125063)
  ·
    refine ⟨188447510545687555855687595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125631673697125037237125063 188447510545687555855687595)
    ·
      refine ⟨282671265818531333783531393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188447510545687555855687595 282671265818531333783531393)
      ·
        refine ⟨212003449363898500337648545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282671265818531333783531393 212003449363898500337648545)
        ·
          refine ⟨159002587022923875253236409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212003449363898500337648545 159002587022923875253236409)
          ·
            refine ⟨119251940267192906439927307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159002587022923875253236409 119251940267192906439927307)
            ·
              refine ⟨178877910400789359659890961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119251940267192906439927307 178877910400789359659890961)
              ·
                refine ⟨134158432800592019744918221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178877910400789359659890961 134158432800592019744918221)
                ·
                  refine ⟨50309412300222007404344333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134158432800592019744918221 50309412300222007404344333)
                  ·
                    refine ⟨18866029612583252776629125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50309412300222007404344333 18866029612583252776629125)
                    ·
                      refine ⟨3537380552359359895617961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18866029612583252776629125 3537380552359359895617961)
                      ·
                        rfl

theorem cell23_6889024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_6889024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889024 prefixEnd_6889024 := by exact prefixLift 6889024
  have htrace : WordTrace (prefixWord ++ tailWord_6889024) baseStart_6889024 baseEnd_6889024 := by
    simpa [prefixWord, tailWord_6889024, baseEnd_6889024] using wordTrace_append hprefix tailTrace_6889024
  have hstable : (prefixWord ++ tailWord_6889024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889024).length < 2 ^ (prefixWord ++ tailWord_6889024).sum := by decide
  have hdescent : baseEnd_6889024 < baseStart_6889024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889085 : List Nat := [1, 4, 1, 1, 4, 1, 2, 4, 1, 4]
def baseStart_6889085 : Nat := 118140960795 + 6889085 * 2 ^ 59
def prefixEnd_6889085 : Nat := 4983230072969 + 3 ^ 40 * 6889085 * 2
def baseEnd_6889085 : Nat := 1179137291559761385651727

theorem tailTrace_6889085 : CollatzResearch.WordTrace tailWord_6889085 prefixEnd_6889085 1179137291559761385651727 := by
  unfold tailWord_6889085
  simp only [CollatzResearch.WordTrace]
  refine ⟨251265572247029081892220709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167510381498019387928147139 251265572247029081892220709)
  ·
    refine ⟨47112294796317952854791383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251265572247029081892220709 47112294796317952854791383)
    ·
      refine ⟨70668442194476929282187075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47112294796317952854791383 70668442194476929282187075)
      ·
        refine ⟨106002663291715393923280613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70668442194476929282187075 106002663291715393923280613)
        ·
          refine ⟨19875499367196636360615115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106002663291715393923280613 19875499367196636360615115)
          ·
            refine ⟨29813249050794954540922673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19875499367196636360615115 29813249050794954540922673)
            ·
              refine ⟨22359936788096215905692005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29813249050794954540922673 22359936788096215905692005)
              ·
                refine ⟨4192488147768040482317251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22359936788096215905692005 4192488147768040482317251)
                ·
                  refine ⟨6288732221652060723475877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4192488147768040482317251 6288732221652060723475877)
                  ·
                    refine ⟨1179137291559761385651727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6288732221652060723475877 1179137291559761385651727)
                    ·
                      rfl

theorem cell23_6889085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_6889085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889085 prefixEnd_6889085 := by exact prefixLift 6889085
  have htrace : WordTrace (prefixWord ++ tailWord_6889085) baseStart_6889085 baseEnd_6889085 := by
    simpa [prefixWord, tailWord_6889085, baseEnd_6889085] using wordTrace_append hprefix tailTrace_6889085
  have hstable : (prefixWord ++ tailWord_6889085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889085).length < 2 ^ (prefixWord ++ tailWord_6889085).sum := by decide
  have hdescent : baseEnd_6889085 < baseStart_6889085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889104 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 7]
def baseStart_6889104 : Nat := 118140960795 + 6889104 * 2 ^ 59
def prefixEnd_6889104 : Nat := 4983230072969 + 3 ^ 40 * 6889104 * 2
def baseEnd_6889104 : Nat := 3537421630811719582617593

theorem tailTrace_6889104 : CollatzResearch.WordTrace tailWord_6889104 prefixEnd_6889104 3537421630811719582617593 := by
  unfold tailWord_6889104
  simp only [CollatzResearch.WordTrace]
  refine ⟨125633132616980124068581183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167510843489306832091441577 125633132616980124068581183)
  ·
    refine ⟨188449698925470186102871775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125633132616980124068581183 188449698925470186102871775)
    ·
      refine ⟨282674548388205279154307663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188449698925470186102871775 282674548388205279154307663)
      ·
        refine ⟨424011822582307918731461495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282674548388205279154307663 424011822582307918731461495)
        ·
          refine ⟨636017733873461878097192243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424011822582307918731461495 636017733873461878097192243)
          ·
            refine ⟨954026600810192817145788365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636017733873461878097192243 954026600810192817145788365)
            ·
              refine ⟨357759975303822306429670637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 954026600810192817145788365 357759975303822306429670637)
              ·
                refine ⟨134159990738933364911126489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 357759975303822306429670637 134159990738933364911126489)
                ·
                  refine ⟨100619993054200023683344867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134159990738933364911126489 100619993054200023683344867)
                  ·
                    refine ⟨150929989581300035525017301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 100619993054200023683344867 150929989581300035525017301)
                    ·
                      refine ⟨3537421630811719582617593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 150929989581300035525017301 3537421630811719582617593)
                      ·
                        rfl

theorem cell23_6889104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 7].length) (baseStart_6889104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889104 prefixEnd_6889104 := by exact prefixLift 6889104
  have htrace : WordTrace (prefixWord ++ tailWord_6889104) baseStart_6889104 baseEnd_6889104 := by
    simpa [prefixWord, tailWord_6889104, baseEnd_6889104] using wordTrace_append hprefix tailTrace_6889104
  have hstable : (prefixWord ++ tailWord_6889104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889104).length < 2 ^ (prefixWord ++ tailWord_6889104).sum := by decide
  have hdescent : baseEnd_6889104 < baseStart_6889104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889119 : List Nat := [1, 1, 2, 7, 1, 2, 1, 3, 1, 4]
def baseStart_6889119 : Nat := 118140960795 + 6889119 * 2 ^ 59
def prefixEnd_6889119 : Nat := 4983230072969 + 3 ^ 40 * 6889119 * 2
def baseEnd_6889119 : Nat := 1179143111007179007976675

theorem tailTrace_6889119 : CollatzResearch.WordTrace tailWord_6889119 prefixEnd_6889119 1179143111007179007976675 := by
  unfold tailWord_6889119
  simp only [CollatzResearch.WordTrace]
  refine ⟨251266812328905905698958411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167511208219270603799305607 251266812328905905698958411)
  ·
    refine ⟨376900218493358858548437617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251266812328905905698958411 376900218493358858548437617)
    ·
      refine ⟨282675163870019143911328213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376900218493358858548437617 282675163870019143911328213)
      ·
        refine ⟨6625199153203573685421755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 282675163870019143911328213 6625199153203573685421755)
        ·
          refine ⟨9937798729805360528132633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6625199153203573685421755 9937798729805360528132633)
          ·
            refine ⟨7453349047354020396099475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9937798729805360528132633 7453349047354020396099475)
            ·
              refine ⟨11180023571031030594149213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7453349047354020396099475 11180023571031030594149213)
              ·
                refine ⟨4192508839136636472805955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11180023571031030594149213 4192508839136636472805955)
                ·
                  refine ⟨6288763258704954709208933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4192508839136636472805955 6288763258704954709208933)
                  ·
                    refine ⟨1179143111007179007976675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6288763258704954709208933 1179143111007179007976675)
                    ·
                      rfl

theorem cell23_6889119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 3, 1, 4].length) (baseStart_6889119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889119 prefixEnd_6889119 := by exact prefixLift 6889119
  have htrace : WordTrace (prefixWord ++ tailWord_6889119) baseStart_6889119 baseEnd_6889119 := by
    simpa [prefixWord, tailWord_6889119, baseEnd_6889119] using wordTrace_append hprefix tailTrace_6889119
  have hstable : (prefixWord ++ tailWord_6889119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889119).length < 2 ^ (prefixWord ++ tailWord_6889119).sum := by decide
  have hdescent : baseEnd_6889119 < baseStart_6889119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889151 : List Nat := [1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 5]
def baseStart_6889151 : Nat := 118140960795 + 6889151 * 2 ^ 59
def prefixEnd_6889151 : Nat := 4983230072969 + 3 ^ 40 * 6889151 * 2
def baseEnd_6889151 : Nat := 3537445764402480898729877

theorem tailTrace_6889151 : CollatzResearch.WordTrace tailWord_6889151 prefixEnd_6889151 3537445764402480898729877 := by
  unfold tailWord_6889151
  simp only [CollatzResearch.WordTrace]
  refine ⟨251267979464789975164123307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167511986309859983442748871 251267979464789975164123307)
  ·
    refine ⟨376901969197184962746184961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251267979464789975164123307 376901969197184962746184961)
    ·
      refine ⟨282676476897888722059638721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376901969197184962746184961 282676476897888722059638721)
      ·
        refine ⟨212007357673416541544729041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282676476897888722059638721 212007357673416541544729041)
        ·
          refine ⟨159005518255062406158546781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212007357673416541544729041 159005518255062406158546781)
          ·
            refine ⟨59627069345648402309455043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159005518255062406158546781 59627069345648402309455043)
            ·
              refine ⟨89440604018472603464182565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59627069345648402309455043 89440604018472603464182565)
              ·
                refine ⟨16770113253463613149534231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89440604018472603464182565 16770113253463613149534231)
                ·
                  refine ⟨25155169880195419724301347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16770113253463613149534231 25155169880195419724301347)
                  ·
                    refine ⟨37732754820293129586452021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25155169880195419724301347 37732754820293129586452021)
                    ·
                      refine ⟨3537445764402480898729877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37732754820293129586452021 3537445764402480898729877)
                      ·
                        rfl

theorem cell23_6889151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_6889151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889151 prefixEnd_6889151 := by exact prefixLift 6889151
  have htrace : WordTrace (prefixWord ++ tailWord_6889151) baseStart_6889151 baseEnd_6889151 := by
    simpa [prefixWord, tailWord_6889151, baseEnd_6889151] using wordTrace_append hprefix tailTrace_6889151
  have hstable : (prefixWord ++ tailWord_6889151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889151).length < 2 ^ (prefixWord ++ tailWord_6889151).sum := by decide
  have hdescent : baseEnd_6889151 < baseStart_6889151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889162 : List Nat := [3, 1, 2, 1, 6, 1, 1, 2, 1, 5]
def baseStart_6889162 : Nat := 118140960795 + 6889162 * 2 ^ 59
def prefixEnd_6889162 : Nat := 4983230072969 + 3 ^ 40 * 6889162 * 2
def baseEnd_6889162 : Nat := 1179150470896560118564109

theorem tailTrace_6889162 : CollatzResearch.WordTrace tailWord_6889162 prefixEnd_6889162 1179150470896560118564109 := by
  unfold tailWord_6889162
  simp only [CollatzResearch.WordTrace]
  refine ⟨62817095166937531010693435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167512253778500082695182493 62817095166937531010693435)
  ·
    refine ⟨94225642750406296516040153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62817095166937531010693435 94225642750406296516040153)
    ·
      refine ⟨70669232062804722387030115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94225642750406296516040153 70669232062804722387030115)
      ·
        refine ⟨106003848094207083580545173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70669232062804722387030115 106003848094207083580545173)
        ·
          refine ⟨4968930379415957042838055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 106003848094207083580545173 4968930379415957042838055)
          ·
            refine ⟨7453395569123935564257083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4968930379415957042838055 7453395569123935564257083)
            ·
              refine ⟨11180093353685903346385625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7453395569123935564257083 11180093353685903346385625)
              ·
                refine ⟨8385070015264427509789219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11180093353685903346385625 8385070015264427509789219)
                ·
                  refine ⟨12577605022896641264683829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8385070015264427509789219 12577605022896641264683829)
                  ·
                    refine ⟨1179150470896560118564109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12577605022896641264683829 1179150470896560118564109)
                    ·
                      rfl

theorem cell23_6889162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_6889162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889162 prefixEnd_6889162 := by exact prefixLift 6889162
  have htrace : WordTrace (prefixWord ++ tailWord_6889162) baseStart_6889162 baseEnd_6889162 := by
    simpa [prefixWord, tailWord_6889162, baseEnd_6889162] using wordTrace_append hprefix tailTrace_6889162
  have hstable : (prefixWord ++ tailWord_6889162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889162).length < 2 ^ (prefixWord ++ tailWord_6889162).sum := by decide
  have hdescent : baseEnd_6889162 < baseStart_6889162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889168 : List Nat := [2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 3]
def baseStart_6889168 : Nat := 118140960795 + 6889168 * 2 ^ 59
def prefixEnd_6889168 : Nat := 4983230072969 + 3 ^ 40 * 6889168 * 2
def baseEnd_6889168 : Nat := 3537454493573607332217299

theorem tailTrace_6889168 : CollatzResearch.WordTrace tailWord_6889168 prefixEnd_6889168 3537454493573607332217299 := by
  unfold tailWord_6889168
  simp only [CollatzResearch.WordTrace]
  refine ⟨125634299752864193533746079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167512399670485591378328105 125634299752864193533746079)
  ·
    refine ⟨188451449629296290300619119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125634299752864193533746079 188451449629296290300619119)
    ·
      refine ⟨282677174443944435450928679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188451449629296290300619119 282677174443944435450928679)
      ·
        refine ⟨424015761665916653176393019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282677174443944435450928679 424015761665916653176393019)
        ·
          refine ⟨636023642498874979764589529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424015761665916653176393019 636023642498874979764589529)
          ·
            refine ⟨477017731874156234823442147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 636023642498874979764589529 477017731874156234823442147)
            ·
              refine ⟨715526597811234352235163221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477017731874156234823442147 715526597811234352235163221)
              ·
                refine ⟨8385077318100402565255819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 715526597811234352235163221 8385077318100402565255819)
                ·
                  refine ⟨12577615977150603847883729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8385077318100402565255819 12577615977150603847883729)
                  ·
                    refine ⟨9433211982862952885912797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12577615977150603847883729 9433211982862952885912797)
                    ·
                      refine ⟨3537454493573607332217299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9433211982862952885912797 3537454493573607332217299)
                      ·
                        rfl

theorem cell23_6889168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 3].length) (baseStart_6889168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889168 prefixEnd_6889168 := by exact prefixLift 6889168
  have htrace : WordTrace (prefixWord ++ tailWord_6889168) baseStart_6889168 baseEnd_6889168 := by
    simpa [prefixWord, tailWord_6889168, baseEnd_6889168] using wordTrace_append hprefix tailTrace_6889168
  have hstable : (prefixWord ++ tailWord_6889168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889168).length < 2 ^ (prefixWord ++ tailWord_6889168).sum := by decide
  have hdescent : baseEnd_6889168 < baseStart_6889168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889178 : List Nat := [3, 1, 1, 2, 2, 4, 1, 2, 1, 2, 4]
def baseStart_6889178 : Nat := 118140960795 + 6889178 * 2 ^ 59
def prefixEnd_6889178 : Nat := 4983230072969 + 3 ^ 40 * 6889178 * 2
def baseEnd_6889178 : Nat := 3537459628380152293092253

theorem tailTrace_6889178 : CollatzResearch.WordTrace tailWord_6889178 prefixEnd_6889178 3537459628380152293092253 := by
  unfold tailWord_6889178
  simp only [CollatzResearch.WordTrace]
  refine ⟨62817241058923039693839047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167512642823794772516904125 62817241058923039693839047)
  ·
    refine ⟨94225861588384559540758571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62817241058923039693839047 94225861588384559540758571)
    ·
      refine ⟨141338792382576839311137857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94225861588384559540758571 141338792382576839311137857)
      ·
        refine ⟨106004094286932629483353393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141338792382576839311137857 106004094286932629483353393)
        ·
          refine ⟨79503070715199472112515045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106004094286932629483353393 79503070715199472112515045)
          ·
            refine ⟨14906825759099901021096571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79503070715199472112515045 14906825759099901021096571)
            ·
              refine ⟨22360238638649851531644857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14906825759099901021096571 22360238638649851531644857)
              ·
                refine ⟨16770178978987388648733643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22360238638649851531644857 16770178978987388648733643)
                ·
                  refine ⟨25155268468481082973100465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16770178978987388648733643 25155268468481082973100465)
                  ·
                    refine ⟨18866451351360812229825349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25155268468481082973100465 18866451351360812229825349)
                    ·
                      refine ⟨3537459628380152293092253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18866451351360812229825349 3537459628380152293092253)
                      ·
                        rfl

theorem cell23_6889178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_6889178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889178 prefixEnd_6889178 := by exact prefixLift 6889178
  have htrace : WordTrace (prefixWord ++ tailWord_6889178) baseStart_6889178 baseEnd_6889178 := by
    simpa [prefixWord, tailWord_6889178, baseEnd_6889178] using wordTrace_append hprefix tailTrace_6889178
  have hstable : (prefixWord ++ tailWord_6889178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889178).length < 2 ^ (prefixWord ++ tailWord_6889178).sum := by decide
  have hdescent : baseEnd_6889178 < baseStart_6889178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889185 : List Nat := [1, 2, 3, 1, 5, 2, 1, 1, 1, 1, 5]
def baseStart_6889185 : Nat := 118140960795 + 6889185 * 2 ^ 59
def prefixEnd_6889185 : Nat := 4983230072969 + 3 ^ 40 * 6889185 * 2
def baseEnd_6889185 : Nat := 3537463222744733765704721

theorem tailTrace_6889185 : CollatzResearch.WordTrace tailWord_6889185 prefixEnd_6889185 3537463222744733765704721 := by
  unfold tailWord_6889185
  simp only [CollatzResearch.WordTrace]
  refine ⟨251269219546666798970861009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167512813031111199313907339 251269219546666798970861009)
  ·
    refine ⟨188451914660000099228145757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251269219546666798970861009 188451914660000099228145757)
    ·
      refine ⟨70669467997500037210554659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188451914660000099228145757 70669467997500037210554659)
      ·
        refine ⟨106004201996250055815831989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70669467997500037210554659 106004201996250055815831989)
        ·
          refine ⟨9937893937148442732734249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106004201996250055815831989 9937893937148442732734249)
          ·
            refine ⟨7453420452861332049550687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9937893937148442732734249 7453420452861332049550687)
            ·
              refine ⟨11180130679291998074326031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7453420452861332049550687 11180130679291998074326031)
              ·
                refine ⟨16770196018937997111489047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11180130679291998074326031 16770196018937997111489047)
                ·
                  refine ⟨25155294028406995667233571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16770196018937997111489047 25155294028406995667233571)
                  ·
                    refine ⟨37732941042610493500850357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25155294028406995667233571 37732941042610493500850357)
                    ·
                      refine ⟨3537463222744733765704721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37732941042610493500850357 3537463222744733765704721)
                      ·
                        rfl

theorem cell23_6889185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_6889185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889185 prefixEnd_6889185 := by exact prefixLift 6889185
  have htrace : WordTrace (prefixWord ++ tailWord_6889185) baseStart_6889185 baseEnd_6889185 := by
    simpa [prefixWord, tailWord_6889185, baseEnd_6889185] using wordTrace_append hprefix tailTrace_6889185
  have hstable : (prefixWord ++ tailWord_6889185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889185).length < 2 ^ (prefixWord ++ tailWord_6889185).sum := by decide
  have hdescent : baseEnd_6889185 < baseStart_6889185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889198 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 3, 3, 3]
def baseStart_6889198 : Nat := 118140960795 + 6889198 * 2 ^ 59
def prefixEnd_6889198 : Nat := 4983230072969 + 3 ^ 40 * 6889198 * 2
def baseEnd_6889198 : Nat := 3537469897993242214842161

theorem tailTrace_6889198 : CollatzResearch.WordTrace tailWord_6889198 prefixEnd_6889198 3537469897993242214842161 := by
  unfold tailWord_6889198
  simp only [CollatzResearch.WordTrace]
  refine ⟨31408711711952462773885531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167513129130413134794056165 31408711711952462773885531)
  ·
    refine ⟨47113067567928694160828297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31408711711952462773885531 47113067567928694160828297)
    ·
      refine ⟨35334800675946520620621223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47113067567928694160828297 35334800675946520620621223)
      ·
        refine ⟨53002201013919780930931835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35334800675946520620621223 53002201013919780930931835)
        ·
          refine ⟨79503301520879671396397753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53002201013919780930931835 79503301520879671396397753)
          ·
            refine ⟨59627476140659753547298315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79503301520879671396397753 59627476140659753547298315)
            ·
              refine ⟨89441214210989630320947473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59627476140659753547298315 89441214210989630320947473)
              ·
                refine ⟨67080910658242222740710605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89441214210989630320947473 67080910658242222740710605)
                ·
                  refine ⟨25155341496840833527766477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67080910658242222740710605 25155341496840833527766477)
                  ·
                    refine ⟨9433253061315312572912429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25155341496840833527766477 9433253061315312572912429)
                    ·
                      refine ⟨3537469897993242214842161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9433253061315312572912429 3537469897993242214842161)
                      ·
                        rfl

theorem cell23_6889198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_6889198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889198 prefixEnd_6889198 := by exact prefixLift 6889198
  have htrace : WordTrace (prefixWord ++ tailWord_6889198) baseStart_6889198 baseEnd_6889198 := by
    simpa [prefixWord, tailWord_6889198, baseEnd_6889198] using wordTrace_append hprefix tailTrace_6889198
  have hstable : (prefixWord ++ tailWord_6889198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889198).length < 2 ^ (prefixWord ++ tailWord_6889198).sum := by decide
  have hdescent : baseEnd_6889198 < baseStart_6889198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889201 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 2, 7]
def baseStart_6889201 : Nat := 118140960795 + 6889201 * 2 ^ 59
def prefixEnd_6889201 : Nat := 4983230072969 + 3 ^ 40 * 6889201 * 2
def baseEnd_6889201 : Nat := 1179157146145068567701549

theorem tailTrace_6889201 : CollatzResearch.WordTrace tailWord_6889201 prefixEnd_6889201 1179157146145068567701549 := by
  unfold tailWord_6889201
  simp only [CollatzResearch.WordTrace]
  refine ⟨251269803114608833703443457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167513202076405889135628971 251269803114608833703443457)
  ·
    refine ⟨188452352335956625277582593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251269803114608833703443457 188452352335956625277582593)
    ·
      refine ⟨141339264251967468958186945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188452352335956625277582593 141339264251967468958186945)
      ·
        refine ⟨106004448188975601718640209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141339264251967468958186945 106004448188975601718640209)
        ·
          refine ⟨79503336141731701288980157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106004448188975601718640209 79503336141731701288980157)
          ·
            refine ⟨29813751053149387983367559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79503336141731701288980157 29813751053149387983367559)
            ·
              refine ⟨44720626579724081975051339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29813751053149387983367559 44720626579724081975051339)
              ·
                refine ⟨67080939869586122962577009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44720626579724081975051339 67080939869586122962577009)
                ·
                  refine ⟨50310704902189592221932757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67080939869586122962577009 50310704902189592221932757)
                  ·
                    refine ⟨1179157146145068567701549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50310704902189592221932757 1179157146145068567701549)
                    ·
                      rfl

theorem cell23_6889201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 7].length) (baseStart_6889201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889201 prefixEnd_6889201 := by exact prefixLift 6889201
  have htrace : WordTrace (prefixWord ++ tailWord_6889201) baseStart_6889201 baseEnd_6889201 := by
    simpa [prefixWord, tailWord_6889201, baseEnd_6889201] using wordTrace_append hprefix tailTrace_6889201
  have hstable : (prefixWord ++ tailWord_6889201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889201).length < 2 ^ (prefixWord ++ tailWord_6889201).sum := by decide
  have hdescent : baseEnd_6889201 < baseStart_6889201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889215 : List Nat := [1, 1, 2, 2, 1, 3, 4, 3, 2, 1, 3]
def baseStart_6889215 : Nat := 118140960795 + 6889215 * 2 ^ 59
def prefixEnd_6889215 : Nat := 4983230072969 + 3 ^ 40 * 6889215 * 2
def baseEnd_6889215 : Nat := 3537478627164368648329583

theorem tailTrace_6889215 : CollatzResearch.WordTrace tailWord_6889215 prefixEnd_6889215 3537478627164368648329583 := by
  unfold tailWord_6889215
  simp only [CollatzResearch.WordTrace]
  refine ⟨251270313736558114094453099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167513542491038742729635399 251270313736558114094453099)
  ·
    refine ⟨376905470604837171141679649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251270313736558114094453099 376905470604837171141679649)
    ·
      refine ⟨282679102953627878356259737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376905470604837171141679649 282679102953627878356259737)
      ·
        refine ⟨212009327215220908767194803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282679102953627878356259737 212009327215220908767194803)
        ·
          refine ⟨318013990822831363150792205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212009327215220908767194803 318013990822831363150792205)
          ·
            refine ⟨119255246558561761181547077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 318013990822831363150792205 119255246558561761181547077)
            ·
              refine ⟨22360358729730330221540077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119255246558561761181547077 22360358729730330221540077)
              ·
                refine ⟨8385134523648873833077529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22360358729730330221540077 8385134523648873833077529)
                ·
                  refine ⟨6288850892736655374808147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8385134523648873833077529 6288850892736655374808147)
                  ·
                    refine ⟨9433276339104983062212221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6288850892736655374808147 9433276339104983062212221)
                    ·
                      refine ⟨3537478627164368648329583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9433276339104983062212221 3537478627164368648329583)
                      ·
                        rfl

theorem cell23_6889215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 2, 1, 3].length) (baseStart_6889215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889215 prefixEnd_6889215 := by exact prefixLift 6889215
  have htrace : WordTrace (prefixWord ++ tailWord_6889215) baseStart_6889215 baseEnd_6889215 := by
    simpa [prefixWord, tailWord_6889215, baseEnd_6889215] using wordTrace_append hprefix tailTrace_6889215
  have hstable : (prefixWord ++ tailWord_6889215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889215).length < 2 ^ (prefixWord ++ tailWord_6889215).sum := by decide
  have hdescent : baseEnd_6889215 < baseStart_6889215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889218 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 2, 7]
def baseStart_6889218 : Nat := 118140960795 + 6889218 * 2 ^ 59
def prefixEnd_6889218 : Nat := 4983230072969 + 3 ^ 40 * 6889218 * 2
def baseEnd_6889218 : Nat := 1179160055868777378864023

theorem tailTrace_6889218 : CollatzResearch.WordTrace tailWord_6889218 prefixEnd_6889218 1179160055868777378864023 := by
  unfold tailWord_6889218
  simp only [CollatzResearch.WordTrace]
  refine ⟨62817605788886811401703077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167513615437031497071208205 62817605788886811401703077)
  ·
    refine ⟨11778301085416277137819327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62817605788886811401703077 11778301085416277137819327)
    ·
      refine ⟨17667451628124415706728991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11778301085416277137819327 17667451628124415706728991)
      ·
        refine ⟨26501177442186623560093487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17667451628124415706728991 26501177442186623560093487)
        ·
          refine ⟨39751766163279935340140231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26501177442186623560093487 39751766163279935340140231)
          ·
            refine ⟨59627649244919903010210347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39751766163279935340140231 59627649244919903010210347)
            ·
              refine ⟨89441473867379854515315521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59627649244919903010210347 89441473867379854515315521)
              ·
                refine ⟨67081105400534890886486641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89441473867379854515315521 67081105400534890886486641)
                ·
                  refine ⟨50310829050401168164864981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67081105400534890886486641 50310829050401168164864981)
                  ·
                    refine ⟨1179160055868777378864023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50310829050401168164864981 1179160055868777378864023)
                    ·
                      rfl

theorem cell23_6889218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_6889218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889218 prefixEnd_6889218 := by exact prefixLift 6889218
  have htrace : WordTrace (prefixWord ++ tailWord_6889218) baseStart_6889218 baseEnd_6889218 := by
    simpa [prefixWord, tailWord_6889218, baseEnd_6889218] using wordTrace_append hprefix tailTrace_6889218
  have hstable : (prefixWord ++ tailWord_6889218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889218).length < 2 ^ (prefixWord ++ tailWord_6889218).sum := by decide
  have hdescent : baseEnd_6889218 < baseStart_6889218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889225 : List Nat := [1, 2, 1, 1, 3, 2, 1, 6, 1, 3, 2]
def baseStart_6889225 : Nat := 118140960795 + 6889225 * 2 ^ 59
def prefixEnd_6889225 : Nat := 4983230072969 + 3 ^ 40 * 6889225 * 2
def baseEnd_6889225 : Nat := 3537483761970913609204537

theorem tailTrace_6889225 : CollatzResearch.WordTrace tailWord_6889225 prefixEnd_6889225 3537483761970913609204537 := by
  unfold tailWord_6889225
  simp only [CollatzResearch.WordTrace]
  refine ⟨251270678466521885802317129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167513785644347923868211419 251270678466521885802317129)
  ·
    refine ⟨188453008849891414351737847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251270678466521885802317129 188453008849891414351737847)
    ·
      refine ⟨282679513274837121527606771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188453008849891414351737847 282679513274837121527606771)
      ·
        refine ⟨424019269912255682291410157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282679513274837121527606771 424019269912255682291410157)
        ·
          refine ⟨159007226217095880859278809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 424019269912255682291410157 159007226217095880859278809)
          ·
            refine ⟨119255419662821910644459107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159007226217095880859278809 119255419662821910644459107)
            ·
              refine ⟨178883129494232865966688661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119255419662821910644459107 178883129494232865966688661)
              ·
                refine ⟨8385146695042165592188531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 178883129494232865966688661 8385146695042165592188531)
                ·
                  refine ⟨12577720042563248388282797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8385146695042165592188531 12577720042563248388282797)
                  ·
                    refine ⟨4716645015961218145606049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12577720042563248388282797 4716645015961218145606049)
                    ·
                      refine ⟨3537483761970913609204537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4716645015961218145606049 3537483761970913609204537)
                      ·
                        rfl

theorem cell23_6889225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 3, 2].length) (baseStart_6889225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889225 prefixEnd_6889225 := by exact prefixLift 6889225
  have htrace : WordTrace (prefixWord ++ tailWord_6889225) baseStart_6889225 baseEnd_6889225 := by
    simpa [prefixWord, tailWord_6889225, baseEnd_6889225] using wordTrace_append hprefix tailTrace_6889225
  have hstable : (prefixWord ++ tailWord_6889225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889225).length < 2 ^ (prefixWord ++ tailWord_6889225).sum := by decide
  have hdescent : baseEnd_6889225 < baseStart_6889225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889236 : List Nat := [2, 4, 4, 1, 1, 1, 1, 3, 1, 2, 3]
def baseStart_6889236 : Nat := 118140960795 + 6889236 * 2 ^ 59
def prefixEnd_6889236 : Nat := 4983230072969 + 3 ^ 40 * 6889236 * 2
def baseEnd_6889236 : Nat := 3537489410258113066166987

theorem tailTrace_6889236 : CollatzResearch.WordTrace tailWord_6889236 prefixEnd_6889236 3537489410258113066166987 := by
  unfold tailWord_6889236
  simp only [CollatzResearch.WordTrace]
  refine ⟨125635539834741017340483781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167514053112988023120645041 125635539834741017340483781)
  ·
    refine ⟨23556663719013940751340709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125635539834741017340483781 23556663719013940751340709)
    ·
      refine ⟨4416874447315113890876383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23556663719013940751340709 4416874447315113890876383)
      ·
        refine ⟨6625311670972670836314575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4416874447315113890876383 6625311670972670836314575)
        ·
          refine ⟨9937967506459006254471863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6625311670972670836314575 9937967506459006254471863)
          ·
            refine ⟨14906951259688509381707795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9937967506459006254471863 14906951259688509381707795)
            ·
              refine ⟨22360426889532764072561693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14906951259688509381707795 22360426889532764072561693)
              ·
                refine ⟨8385160083574786527210635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22360426889532764072561693 8385160083574786527210635)
                ·
                  refine ⟨12577740125362179790815953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8385160083574786527210635 12577740125362179790815953)
                  ·
                    refine ⟨9433305094021634843111965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12577740125362179790815953 9433305094021634843111965)
                    ·
                      refine ⟨3537489410258113066166987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9433305094021634843111965 3537489410258113066166987)
                      ·
                        rfl

theorem cell23_6889236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_6889236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889236 prefixEnd_6889236 := by exact prefixLift 6889236
  have htrace : WordTrace (prefixWord ++ tailWord_6889236) baseStart_6889236 baseEnd_6889236 := by
    simpa [prefixWord, tailWord_6889236, baseEnd_6889236] using wordTrace_append hprefix tailTrace_6889236
  have hstable : (prefixWord ++ tailWord_6889236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889236).length < 2 ^ (prefixWord ++ tailWord_6889236).sum := by decide
  have hdescent : baseEnd_6889236 < baseStart_6889236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889241 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 6, 1, 5]
def baseStart_6889241 : Nat := 118140960795 + 6889241 * 2 ^ 59
def prefixEnd_6889241 : Nat := 4983230072969 + 3 ^ 40 * 6889241 * 2
def baseEnd_6889241 : Nat := 3537491977661385546604463

theorem tailTrace_6889241 : CollatzResearch.WordTrace tailWord_6889241 prefixEnd_6889241 3537491977661385546604463 := by
  unfold tailWord_6889241
  simp only [CollatzResearch.WordTrace]
  refine ⟨251271262034463920534899577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167514174689642613689933051 251271262034463920534899577)
  ·
    refine ⟨188453446525847940401174683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251271262034463920534899577 188453446525847940401174683)
    ·
      refine ⟨282680169788771910601762025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188453446525847940401174683 282680169788771910601762025)
      ·
        refine ⟨212010127341578932951321519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282680169788771910601762025 212010127341578932951321519)
        ·
          refine ⟨318015191012368399426982279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212010127341578932951321519 318015191012368399426982279)
          ·
            refine ⟨477022786518552599140473419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318015191012368399426982279 477022786518552599140473419)
            ·
              refine ⟨715534179777828898710710129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477022786518552599140473419 715534179777828898710710129)
              ·
                refine ⟨536650634833371674033032597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 715534179777828898710710129 536650634833371674033032597)
                ·
                  refine ⟨25155498507814297220298403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 536650634833371674033032597 25155498507814297220298403)
                  ·
                    refine ⟨37733247761721445830447605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25155498507814297220298403 37733247761721445830447605)
                    ·
                      refine ⟨3537491977661385546604463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37733247761721445830447605 3537491977661385546604463)
                      ·
                        rfl

theorem cell23_6889241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_6889241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889241 prefixEnd_6889241 := by exact prefixLift 6889241
  have htrace : WordTrace (prefixWord ++ tailWord_6889241) baseStart_6889241 baseEnd_6889241 := by
    simpa [prefixWord, tailWord_6889241, baseEnd_6889241] using wordTrace_append hprefix tailTrace_6889241
  have hstable : (prefixWord ++ tailWord_6889241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889241).length < 2 ^ (prefixWord ++ tailWord_6889241).sum := by decide
  have hdescent : baseEnd_6889241 < baseStart_6889241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889242 : List Nat := [3, 1, 1, 3, 2, 3, 1, 3, 1, 3, 2]
def baseStart_6889242 : Nat := 118140960795 + 6889242 * 2 ^ 59
def prefixEnd_6889242 : Nat := 4983230072969 + 3 ^ 40 * 6889242 * 2
def baseEnd_6889242 : Nat := 3537492491142040042691959

theorem tailTrace_6889242 : CollatzResearch.WordTrace tailWord_6889242 prefixEnd_6889242 3537492491142040042691959 := by
  unfold tailWord_6889242
  simp only [CollatzResearch.WordTrace]
  refine ⟨62817824626865074426421495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167514199004973531803790653 62817824626865074426421495)
  ·
    refine ⟨94226736940297611639632243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62817824626865074426421495 94226736940297611639632243)
    ·
      refine ⟨141340105410446417459448365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94226736940297611639632243 141340105410446417459448365)
      ·
        refine ⟨53002539528917406547293137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141340105410446417459448365 53002539528917406547293137)
        ·
          refine ⟨39751904646688054910469853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53002539528917406547293137 39751904646688054910469853)
          ·
            refine ⟨14906964242508020591426195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39751904646688054910469853 14906964242508020591426195)
            ·
              refine ⟨22360446363762030887139293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14906964242508020591426195 22360446363762030887139293)
              ·
                refine ⟨8385167386410761582677235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22360446363762030887139293 8385167386410761582677235)
                ·
                  refine ⟨12577751079616142374015853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8385167386410761582677235 12577751079616142374015853)
                  ·
                    refine ⟨4716656654856053390255945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12577751079616142374015853 4716656654856053390255945)
                    ·
                      refine ⟨3537492491142040042691959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4716656654856053390255945 3537492491142040042691959)
                      ·
                        rfl

theorem cell23_6889242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_6889242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889242 prefixEnd_6889242 := by exact prefixLift 6889242
  have htrace : WordTrace (prefixWord ++ tailWord_6889242) baseStart_6889242 baseEnd_6889242 := by
    simpa [prefixWord, tailWord_6889242, baseEnd_6889242] using wordTrace_append hprefix tailTrace_6889242
  have hstable : (prefixWord ++ tailWord_6889242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889242).length < 2 ^ (prefixWord ++ tailWord_6889242).sum := by decide
  have hdescent : baseEnd_6889242 < baseStart_6889242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889272 : List Nat := [2, 1, 2, 1, 3, 5, 1, 1, 1, 4, 2]
def baseStart_6889272 : Nat := 118140960795 + 6889272 * 2 ^ 59
def prefixEnd_6889272 : Nat := 4983230072969 + 3 ^ 40 * 6889272 * 2
def baseEnd_6889272 : Nat := 3537507895561674925316821

theorem tailTrace_6889272 : CollatzResearch.WordTrace tailWord_6889272 prefixEnd_6889272 3537507895561674925316821 := by
  unfold tailWord_6889272
  simp only [CollatzResearch.WordTrace]
  refine ⟨125636196348675806414639035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167514928464901075219518713 125636196348675806414639035)
  ·
    refine ⟨188454294523013709621958553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125636196348675806414639035 188454294523013709621958553)
    ·
      refine ⟨141340720892260282216468915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188454294523013709621958553 141340720892260282216468915)
      ·
        refine ⟨212011081338390423324703373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141340720892260282216468915 212011081338390423324703373)
        ·
          refine ⟨79504155501896408746763765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212011081338390423324703373 79504155501896408746763765)
          ·
            refine ⟨7453514578302788320009103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79504155501896408746763765 7453514578302788320009103)
            ·
              refine ⟨11180271867454182480013655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7453514578302788320009103 11180271867454182480013655)
              ·
                refine ⟨16770407801181273720020483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11180271867454182480013655 16770407801181273720020483)
                ·
                  refine ⟨25155611701771910580030725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16770407801181273720020483 25155611701771910580030725)
                  ·
                    refine ⟨4716677194082233233755761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25155611701771910580030725 4716677194082233233755761)
                    ·
                      refine ⟨3537507895561674925316821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4716677194082233233755761 3537507895561674925316821)
                      ·
                        rfl

theorem cell23_6889272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 1, 4, 2].length) (baseStart_6889272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889272 prefixEnd_6889272 := by exact prefixLift 6889272
  have htrace : WordTrace (prefixWord ++ tailWord_6889272) baseStart_6889272 baseEnd_6889272 := by
    simpa [prefixWord, tailWord_6889272, baseEnd_6889272] using wordTrace_append hprefix tailTrace_6889272
  have hstable : (prefixWord ++ tailWord_6889272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889272).length < 2 ^ (prefixWord ++ tailWord_6889272).sum := by decide
  have hdescent : baseEnd_6889272 < baseStart_6889272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889312 : List Nat := [2, 1, 1, 3, 3, 3, 3, 2, 5]
def baseStart_6889312 : Nat := 118140960795 + 6889312 * 2 ^ 59
def prefixEnd_6889312 : Nat := 4983230072969 + 3 ^ 40 * 6889312 * 2
def baseEnd_6889312 : Nat := 393058714976428307646293

theorem tailTrace_6889312 : CollatzResearch.WordTrace tailWord_6889312 prefixEnd_6889312 393058714976428307646293 := by
  unfold tailWord_6889312
  simp only [CollatzResearch.WordTrace]
  refine ⟨125636925808603349830367095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167515901078137799773822793 125636925808603349830367095)
  ·
    refine ⟨188455388712905024745550643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125636925808603349830367095 188455388712905024745550643)
    ·
      refine ⟨282683083069357537118325965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188455388712905024745550643 282683083069357537118325965)
      ·
        refine ⟨106006156151009076419372237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282683083069357537118325965 106006156151009076419372237)
        ·
          refine ⟨39752308556628403657264589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106006156151009076419372237 39752308556628403657264589)
          ·
            refine ⟨14907115708735651371474221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39752308556628403657264589 14907115708735651371474221)
            ·
              refine ⟨5590168390775869264302833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14907115708735651371474221 5590168390775869264302833)
              ·
                refine ⟨4192626293081901948227125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5590168390775869264302833 4192626293081901948227125)
                ·
                  refine ⟨393058714976428307646293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4192626293081901948227125 393058714976428307646293)
                  ·
                    rfl

theorem cell23_6889312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 2, 5].length) (baseStart_6889312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889312 prefixEnd_6889312 := by exact prefixLift 6889312
  have htrace : WordTrace (prefixWord ++ tailWord_6889312) baseStart_6889312 baseEnd_6889312 := by
    simpa [prefixWord, tailWord_6889312, baseEnd_6889312] using wordTrace_append hprefix tailTrace_6889312
  have hstable : (prefixWord ++ tailWord_6889312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889312).length < 2 ^ (prefixWord ++ tailWord_6889312).sum := by decide
  have hdescent : baseEnd_6889312 < baseStart_6889312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889328 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 4]
def baseStart_6889328 : Nat := 118140960795 + 6889328 * 2 ^ 59
def prefixEnd_6889328 : Nat := 4983230072969 + 3 ^ 40 * 6889328 * 2
def baseEnd_6889328 : Nat := 3537536650478326706216563

theorem tailTrace_6889328 : CollatzResearch.WordTrace tailWord_6889328 prefixEnd_6889328 3537536650478326706216563 := by
  unfold tailWord_6889328
  simp only [CollatzResearch.WordTrace]
  refine ⟨125637217592574367196658319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167516290123432489595544425 125637217592574367196658319)
  ·
    refine ⟨188455826388861550794987479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125637217592574367196658319 188455826388861550794987479)
    ·
      refine ⟨282683739583292326192481219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188455826388861550794987479 282683739583292326192481219)
      ·
        refine ⟨424025609374938489288721829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282683739583292326192481219 424025609374938489288721829)
        ·
          refine ⟨79504801757800966741635343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 424025609374938489288721829 79504801757800966741635343)
          ·
            refine ⟨119257202636701450112453015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79504801757800966741635343 119257202636701450112453015)
            ·
              refine ⟨178885803955052175168679523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119257202636701450112453015 178885803955052175168679523)
              ·
                refine ⟨268328705932578262753019285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178885803955052175168679523 268328705932578262753019285)
                ·
                  refine ⟨12577908090589606066547779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 268328705932578262753019285 12577908090589606066547779)
                  ·
                    refine ⟨18866862135884409099821669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12577908090589606066547779 18866862135884409099821669)
                    ·
                      refine ⟨3537536650478326706216563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18866862135884409099821669 3537536650478326706216563)
                      ·
                        rfl

theorem cell23_6889328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 4].length) (baseStart_6889328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889328 prefixEnd_6889328 := by exact prefixLift 6889328
  have htrace : WordTrace (prefixWord ++ tailWord_6889328) baseStart_6889328 baseEnd_6889328 := by
    simpa [prefixWord, tailWord_6889328, baseEnd_6889328] using wordTrace_append hprefix tailTrace_6889328
  have hstable : (prefixWord ++ tailWord_6889328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889328).length < 2 ^ (prefixWord ++ tailWord_6889328).sum := by decide
  have hdescent : baseEnd_6889328 < baseStart_6889328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889342 : List Nat := [4, 2, 3, 1, 1, 1, 1, 3, 2, 5]
def baseStart_6889342 : Nat := 118140960795 + 6889342 * 2 ^ 59
def prefixEnd_6889342 : Nat := 4983230072969 + 3 ^ 40 * 6889342 * 2
def baseEnd_6889342 : Nat := 1179181279735829883813833

theorem tailTrace_6889342 : CollatzResearch.WordTrace tailWord_6889342 prefixEnd_6889342 1179181279735829883813833 := by
  unfold tailWord_6889342
  simp only [CollatzResearch.WordTrace]
  refine ⟨31409368225887251848040785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167516630538065343189550853 31409368225887251848040785)
  ·
    refine ⟨23557026169415438886030589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31409368225887251848040785 23557026169415438886030589)
    ·
      refine ⟨8833884813530789582261471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23557026169415438886030589 8833884813530789582261471)
      ·
        refine ⟨13250827220296184373392207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8833884813530789582261471 13250827220296184373392207)
        ·
          refine ⟨19876240830444276560088311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13250827220296184373392207 19876240830444276560088311)
          ·
            refine ⟨29814361245666414840132467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19876240830444276560088311 29814361245666414840132467)
            ·
              refine ⟨44721541868499622260198701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29814361245666414840132467 44721541868499622260198701)
              ·
                refine ⟨16770578200687358347574513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44721541868499622260198701 16770578200687358347574513)
                ·
                  refine ⟨12577933650515518760680885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16770578200687358347574513 12577933650515518760680885)
                  ·
                    refine ⟨1179181279735829883813833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12577933650515518760680885 1179181279735829883813833)
                    ·
                      rfl

theorem cell23_6889342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_6889342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889342 prefixEnd_6889342 := by exact prefixLift 6889342
  have htrace : WordTrace (prefixWord ++ tailWord_6889342) baseStart_6889342 baseEnd_6889342 := by
    simpa [prefixWord, tailWord_6889342, baseEnd_6889342] using wordTrace_append hprefix tailTrace_6889342
  have hstable : (prefixWord ++ tailWord_6889342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889342).length < 2 ^ (prefixWord ++ tailWord_6889342).sum := by decide
  have hdescent : baseEnd_6889342 < baseStart_6889342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889362 : List Nat := [3, 2, 3, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_6889362 : Nat := 118140960795 + 6889362 * 2 ^ 59
def prefixEnd_6889362 : Nat := 4983230072969 + 3 ^ 40 * 6889362 * 2
def baseEnd_6889362 : Nat := 3537554108820579573191407

theorem tailTrace_6889362 : CollatzResearch.WordTrace tailWord_6889362 prefixEnd_6889362 3537554108820579573191407 := by
  unfold tailWord_6889362
  simp only [CollatzResearch.WordTrace]
  refine ⟨62818918816756389550013585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167517116844683705466702893 62818918816756389550013585)
  ·
    refine ⟨47114189112567292162510189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62818918816756389550013585 47114189112567292162510189)
    ·
      refine ⟨17667820917212734560941321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47114189112567292162510189 17667820917212734560941321)
      ·
        refine ⟨13250865687909550920705991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17667820917212734560941321 13250865687909550920705991)
        ·
          refine ⟨19876298531864326381058987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13250865687909550920705991 19876298531864326381058987)
          ·
            refine ⟨29814447797796489571588481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19876298531864326381058987 29814447797796489571588481)
            ·
              refine ⟨22360835848347367178691361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29814447797796489571588481 22360835848347367178691361)
              ·
                refine ⟨16770626886260525384018521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22360835848347367178691361 16770626886260525384018521)
                ·
                  refine ⟨12577970164695394038013891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16770626886260525384018521 12577970164695394038013891)
                  ·
                    refine ⟨18866955247043091057020837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12577970164695394038013891 18866955247043091057020837)
                    ·
                      refine ⟨3537554108820579573191407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18866955247043091057020837 3537554108820579573191407)
                      ·
                        rfl

theorem cell23_6889362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_6889362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889362 prefixEnd_6889362 := by exact prefixLift 6889362
  have htrace : WordTrace (prefixWord ++ tailWord_6889362) baseStart_6889362 baseEnd_6889362 := by
    simpa [prefixWord, tailWord_6889362, baseEnd_6889362] using wordTrace_append hprefix tailTrace_6889362
  have hstable : (prefixWord ++ tailWord_6889362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889362).length < 2 ^ (prefixWord ++ tailWord_6889362).sum := by decide
  have hdescent : baseEnd_6889362 < baseStart_6889362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889365 : List Nat := [1, 3, 2, 1, 1, 3, 1, 4, 2, 2, 3]
def baseStart_6889365 : Nat := 118140960795 + 6889365 * 2 ^ 59
def prefixEnd_6889365 : Nat := 4983230072969 + 3 ^ 40 * 6889365 * 2
def baseEnd_6889365 : Nat := 3537555649262543061453893

theorem tailTrace_6889365 : CollatzResearch.WordTrace tailWord_6889365 prefixEnd_6889365 3537555649262543061453893 := by
  unfold tailWord_6889365
  simp only [CollatzResearch.WordTrace]
  refine ⟨251275784686014689712413549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167517189790676459808275699 251275784686014689712413549)
  ·
    refine ⟨94228419257255508642155081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251275784686014689712413549 94228419257255508642155081)
    ·
      refine ⟨70671314442941631481616311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94228419257255508642155081 70671314442941631481616311)
      ·
        refine ⟨106006971664412447222424467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70671314442941631481616311 106006971664412447222424467)
        ·
          refine ⟨159010457496618670833636701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106006971664412447222424467 159010457496618670833636701)
          ·
            refine ⟨59628921561232001562613763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159010457496618670833636701 59628921561232001562613763)
            ·
              refine ⟨89443382341848002343920645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59628921561232001562613763 89443382341848002343920645)
              ·
                refine ⟨16770634189096500439485121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89443382341848002343920645 16770634189096500439485121)
                ·
                  refine ⟨12577975641822375329613841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16770634189096500439485121 12577975641822375329613841)
                  ·
                    refine ⟨9433481731366781497210381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12577975641822375329613841 9433481731366781497210381)
                    ·
                      refine ⟨3537555649262543061453893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9433481731366781497210381 3537555649262543061453893)
                      ·
                        rfl

theorem cell23_6889365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_6889365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889365 prefixEnd_6889365 := by exact prefixLift 6889365
  have htrace : WordTrace (prefixWord ++ tailWord_6889365) baseStart_6889365 baseEnd_6889365 := by
    simpa [prefixWord, tailWord_6889365, baseEnd_6889365] using wordTrace_append hprefix tailTrace_6889365
  have hstable : (prefixWord ++ tailWord_6889365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889365).length < 2 ^ (prefixWord ++ tailWord_6889365).sum := by decide
  have hdescent : baseEnd_6889365 < baseStart_6889365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889396 : List Nat := [2, 5, 2, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_6889396 : Nat := 118140960795 + 6889396 * 2 ^ 59
def prefixEnd_6889396 : Nat := 4983230072969 + 3 ^ 40 * 6889396 * 2
def baseEnd_6889396 : Nat := 3537571567162832440166251

theorem tailTrace_6889396 : CollatzResearch.WordTrace tailWord_6889396 prefixEnd_6889396 3537571567162832440166251 := by
  unfold tailWord_6889396
  simp only [CollatzResearch.WordTrace]
  refine ⟨125638457674451191003396021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167517943565934921337861361 125638457674451191003396021)
  ·
    refine ⟨11778605406979799156568377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125638457674451191003396021 11778605406979799156568377)
    ·
      refine ⟨8833954055234849367426283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11778605406979799156568377 8833954055234849367426283)
      ·
        refine ⟨13250931082852274051139425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8833954055234849367426283 13250931082852274051139425)
        ·
          refine ⟨9938198312139205538354569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13250931082852274051139425 9938198312139205538354569)
          ·
            refine ⟨7453648734104404153765927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9938198312139205538354569 7453648734104404153765927)
            ·
              refine ⟨11180473101156606230648891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7453648734104404153765927 11180473101156606230648891)
              ·
                refine ⟨16770709651734909345973337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11180473101156606230648891 16770709651734909345973337)
                ·
                  refine ⟨12578032238801182009480003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16770709651734909345973337 12578032238801182009480003)
                  ·
                    refine ⟨18867048358201773014220005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12578032238801182009480003 18867048358201773014220005)
                    ·
                      refine ⟨3537571567162832440166251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18867048358201773014220005 3537571567162832440166251)
                      ·
                        rfl

theorem cell23_6889396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_6889396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889396 prefixEnd_6889396 := by exact prefixLift 6889396
  have htrace : WordTrace (prefixWord ++ tailWord_6889396) baseStart_6889396 baseEnd_6889396 := by
    simpa [prefixWord, tailWord_6889396, baseEnd_6889396] using wordTrace_append hprefix tailTrace_6889396
  have hstable : (prefixWord ++ tailWord_6889396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889396).length < 2 ^ (prefixWord ++ tailWord_6889396).sum := by decide
  have hdescent : baseEnd_6889396 < baseStart_6889396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889422 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2]
def baseStart_6889422 : Nat := 118140960795 + 6889422 * 2 ^ 59
def prefixEnd_6889422 : Nat := 4983230072969 + 3 ^ 40 * 6889422 * 2
def baseEnd_6889422 : Nat := 3537584917659849338441131

theorem tailTrace_6889422 : CollatzResearch.WordTrace tailWord_6889422 prefixEnd_6889422 3537584917659849338441131 := by
  unfold tailWord_6889422
  simp only [CollatzResearch.WordTrace]
  refine ⟨31409732955851023555904815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167518575764538792298159013 31409732955851023555904815)
  ·
    refine ⟨47114599433776535333857223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31409732955851023555904815 47114599433776535333857223)
    ·
      refine ⟨70671899150664803000785835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47114599433776535333857223 70671899150664803000785835)
      ·
        refine ⟨106007848725997204501178753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70671899150664803000785835 106007848725997204501178753)
        ·
          refine ⟨79505886544497903375884065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106007848725997204501178753 79505886544497903375884065)
          ·
            refine ⟨59629414908373427531913049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79505886544497903375884065 59629414908373427531913049)
            ·
              refine ⟨44722061181280070648934787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59629414908373427531913049 44722061181280070648934787)
              ·
                refine ⟨67083091771920105973402181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44722061181280070648934787 67083091771920105973402181)
                ·
                  refine ⟨12578079707235019870012909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67083091771920105973402181 12578079707235019870012909)
                  ·
                    refine ⟨4716779890213132451254841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12578079707235019870012909 4716779890213132451254841)
                    ·
                      refine ⟨3537584917659849338441131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4716779890213132451254841 3537584917659849338441131)
                      ·
                        rfl

theorem cell23_6889422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2].length) (baseStart_6889422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889422 prefixEnd_6889422 := by exact prefixLift 6889422
  have htrace : WordTrace (prefixWord ++ tailWord_6889422) baseStart_6889422 baseEnd_6889422 := by
    simpa [prefixWord, tailWord_6889422, baseEnd_6889422] using wordTrace_append hprefix tailTrace_6889422
  have hstable : (prefixWord ++ tailWord_6889422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889422).length < 2 ^ (prefixWord ++ tailWord_6889422).sum := by decide
  have hdescent : baseEnd_6889422 < baseStart_6889422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889429 : List Nat := [1, 3, 2, 3, 2, 2, 2, 1, 3, 1, 3]
def baseStart_6889429 : Nat := 118140960795 + 6889429 * 2 ^ 59
def prefixEnd_6889429 : Nat := 4983230072969 + 3 ^ 40 * 6889429 * 2
def baseEnd_6889429 : Nat := 3537588512024430811053599

theorem tailTrace_6889429 : CollatzResearch.WordTrace tailWord_6889429 prefixEnd_6889429 3537588512024430811053599 := by
  unfold tailWord_6889429
  simp only [CollatzResearch.WordTrace]
  refine ⟨251278118957782828642743341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167518745971855219095162227 251278118957782828642743341)
  ·
    refine ⟨94229294609168560741028753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251278118957782828642743341 94229294609168560741028753)
    ·
      refine ⟨70671970956876420555771565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94229294609168560741028753 70671970956876420555771565)
      ·
        refine ⟨26501989108828657708414337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70671970956876420555771565 26501989108828657708414337)
        ·
          refine ⟨19876491831621493281310753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26501989108828657708414337 19876491831621493281310753)
          ·
            refine ⟨14907368873716119960983065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19876491831621493281310753 14907368873716119960983065)
            ·
              refine ⟨11180526655287089970737299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14907368873716119960983065 11180526655287089970737299)
              ·
                refine ⟨16770789982930634956105949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11180526655287089970737299 16770789982930634956105949)
                ·
                  refine ⟨6289046243598988108539731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16770789982930634956105949 6289046243598988108539731)
                  ·
                    refine ⟨9433569365398482162809597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6289046243598988108539731 9433569365398482162809597)
                    ·
                      refine ⟨3537588512024430811053599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9433569365398482162809597 3537588512024430811053599)
                      ·
                        rfl

theorem cell23_6889429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_6889429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889429 prefixEnd_6889429 := by exact prefixLift 6889429
  have htrace : WordTrace (prefixWord ++ tailWord_6889429) baseStart_6889429 baseEnd_6889429 := by
    simpa [prefixWord, tailWord_6889429, baseEnd_6889429] using wordTrace_append hprefix tailTrace_6889429
  have hstable : (prefixWord ++ tailWord_6889429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889429).length < 2 ^ (prefixWord ++ tailWord_6889429).sum := by decide
  have hdescent : baseEnd_6889429 < baseStart_6889429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889488 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 1, 9]
def baseStart_6889488 : Nat := 118140960795 + 6889488 * 2 ^ 59
def prefixEnd_6889488 : Nat := 4983230072969 + 3 ^ 40 * 6889488 * 2
def baseEnd_6889488 : Nat := 1179206269127682026738609

theorem tailTrace_6889488 : CollatzResearch.WordTrace tailWord_6889488 prefixEnd_6889488 1179206269127682026738609 := by
  unfold tailWord_6889488
  simp only [CollatzResearch.WordTrace]
  refine ⟨125640135432284540859570559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167520180576379387812760745 125640135432284540859570559)
  ·
    refine ⟨188460203148426811289355839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125640135432284540859570559 188460203148426811289355839)
    ·
      refine ⟨282690304722640216934033759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188460203148426811289355839 282690304722640216934033759)
      ·
        refine ⟨424035457083960325401050639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282690304722640216934033759 424035457083960325401050639)
        ·
          refine ⟨636053185625940488101575959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424035457083960325401050639 636053185625940488101575959)
          ·
            refine ⟨954079778438910732152363939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636053185625940488101575959 954079778438910732152363939)
            ·
              refine ⟨1431119667658366098228545909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 954079778438910732152363939 1431119667658366098228545909)
              ·
                refine ⟨134167468842971821708926179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1431119667658366098228545909 134167468842971821708926179)
                ·
                  refine ⟨201251203264457732563389269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134167468842971821708926179 201251203264457732563389269)
                  ·
                    refine ⟨1179206269127682026738609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 201251203264457732563389269 1179206269127682026738609)
                    ·
                      rfl

theorem cell23_6889488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 9].length) (baseStart_6889488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889488 prefixEnd_6889488 := by exact prefixLift 6889488
  have htrace : WordTrace (prefixWord ++ tailWord_6889488) baseStart_6889488 baseEnd_6889488 := by
    simpa [prefixWord, tailWord_6889488, baseEnd_6889488] using wordTrace_append hprefix tailTrace_6889488
  have hstable : (prefixWord ++ tailWord_6889488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889488).length < 2 ^ (prefixWord ++ tailWord_6889488).sum := by decide
  have hdescent : baseEnd_6889488 < baseStart_6889488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889545 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 1, 6, 3]
def baseStart_6889545 : Nat := 118140960795 + 6889545 * 2 ^ 59
def prefixEnd_6889545 : Nat := 4983230072969 + 3 ^ 40 * 6889545 * 2
def baseEnd_6889545 : Nat := 3537648075780352357203065

theorem tailTrace_6889545 : CollatzResearch.WordTrace tailWord_6889545 prefixEnd_6889545 3537648075780352357203065 := by
  unfold tailWord_6889545
  simp only [CollatzResearch.WordTrace]
  refine ⟨251282349825362580453966089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167521566550241720302644059 251282349825362580453966089)
  ·
    refine ⟨188461762369021935340474567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251282349825362580453966089 188461762369021935340474567)
    ·
      refine ⟨282692643553532903010711851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188461762369021935340474567 282692643553532903010711851)
      ·
        refine ⟨424038965330299354516067777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282692643553532903010711851 424038965330299354516067777)
        ·
          refine ⟨318029223997724515887050833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424038965330299354516067777 318029223997724515887050833)
          ·
            refine ⟨238521917998293386915288125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318029223997724515887050833 238521917998293386915288125)
            ·
              refine ⟨89445719249360020093233047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238521917998293386915288125 89445719249360020093233047)
              ·
                refine ⟨134168578874040030139849571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89445719249360020093233047 134168578874040030139849571)
                ·
                  refine ⟨201252868311060045209774357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134168578874040030139849571 201252868311060045209774357)
                  ·
                    refine ⟨9433728202080939619208173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 201252868311060045209774357 9433728202080939619208173)
                    ·
                      refine ⟨3537648075780352357203065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9433728202080939619208173 3537648075780352357203065)
                      ·
                        rfl

theorem cell23_6889545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 6, 3].length) (baseStart_6889545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889545 prefixEnd_6889545 := by exact prefixLift 6889545
  have htrace : WordTrace (prefixWord ++ tailWord_6889545) baseStart_6889545 baseEnd_6889545 := by
    simpa [prefixWord, tailWord_6889545, baseEnd_6889545] using wordTrace_append hprefix tailTrace_6889545
  have hstable : (prefixWord ++ tailWord_6889545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889545).length < 2 ^ (prefixWord ++ tailWord_6889545).sum := by decide
  have hdescent : baseEnd_6889545 < baseStart_6889545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889593 : List Nat := [1, 2, 1, 3, 4, 3, 1, 2, 2, 2, 2]
def baseStart_6889593 : Nat := 118140960795 + 6889593 * 2 ^ 59
def prefixEnd_6889593 : Nat := 4983230072969 + 3 ^ 40 * 6889593 * 2
def baseEnd_6889593 : Nat := 3537672722851768169402845

theorem tailTrace_6889593 : CollatzResearch.WordTrace tailWord_6889593 prefixEnd_6889593 3537672722851768169402845 := by
  unfold tailWord_6889593
  simp only [CollatzResearch.WordTrace]
  refine ⟨251284100529188684651713433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167522733686125789767808955 251284100529188684651713433)
  ·
    refine ⟨188463075396891513488785075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251284100529188684651713433 188463075396891513488785075)
    ·
      refine ⟨282694613095337270233177613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188463075396891513488785075 282694613095337270233177613)
      ·
        refine ⟨106010479910751476337441605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282694613095337270233177613 106010479910751476337441605)
        ·
          refine ⟨19876964983265901813270301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106010479910751476337441605 19876964983265901813270301)
          ·
            refine ⟨7453861868724713179976363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19876964983265901813270301 7453861868724713179976363)
            ·
              refine ⟨11180792803087069769964545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7453861868724713179976363 11180792803087069769964545)
              ·
                refine ⟨8385594602315302327473409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11180792803087069769964545 8385594602315302327473409)
                ·
                  refine ⟨6289195951736476745605057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8385594602315302327473409 6289195951736476745605057)
                  ·
                    refine ⟨4716896963802357559203793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6289195951736476745605057 4716896963802357559203793)
                    ·
                      refine ⟨3537672722851768169402845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4716896963802357559203793 3537672722851768169402845)
                      ·
                        rfl

theorem cell23_6889593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 2, 2, 2].length) (baseStart_6889593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889593 prefixEnd_6889593 := by exact prefixLift 6889593
  have htrace : WordTrace (prefixWord ++ tailWord_6889593) baseStart_6889593 baseEnd_6889593 := by
    simpa [prefixWord, tailWord_6889593, baseEnd_6889593] using wordTrace_append hprefix tailTrace_6889593
  have hstable : (prefixWord ++ tailWord_6889593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889593).length < 2 ^ (prefixWord ++ tailWord_6889593).sum := by decide
  have hdescent : baseEnd_6889593 < baseStart_6889593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889632 : List Nat := [2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 4]
def baseStart_6889632 : Nat := 118140960795 + 6889632 * 2 ^ 59
def prefixEnd_6889632 : Nat := 4983230072969 + 3 ^ 40 * 6889632 * 2
def baseEnd_6889632 : Nat := 3537692748597293516815165

theorem tailTrace_6889632 : CollatzResearch.WordTrace tailWord_6889632 prefixEnd_6889632 3537692748597293516815165 := by
  unfold tailWord_6889632
  simp only [CollatzResearch.WordTrace]
  refine ⟨125642761488023697156191575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167523681984031596208255433 125642761488023697156191575)
  ·
    refine ⟨188464142232035545734287363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125642761488023697156191575 188464142232035545734287363)
    ·
      refine ⟨282696213348053318601431045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188464142232035545734287363 282696213348053318601431045)
      ·
        refine ⟨53005540002759997237768321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 282696213348053318601431045 53005540002759997237768321)
        ·
          refine ⟨39754155002069997928326241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53005540002759997237768321 39754155002069997928326241)
          ·
            refine ⟨29815616251552498446244681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39754155002069997928326241 29815616251552498446244681)
            ·
              refine ⟨22361712188664373834683511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29815616251552498446244681 22361712188664373834683511)
              ·
                refine ⟨33542568282996560752025267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22361712188664373834683511 33542568282996560752025267)
                ·
                  refine ⟨50313852424494841128037901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33542568282996560752025267 50313852424494841128037901)
                  ·
                    refine ⟨18867694659185565423014213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50313852424494841128037901 18867694659185565423014213)
                    ·
                      refine ⟨3537692748597293516815165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18867694659185565423014213 3537692748597293516815165)
                      ·
                        rfl

theorem cell23_6889632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_6889632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889632 prefixEnd_6889632 := by exact prefixLift 6889632
  have htrace : WordTrace (prefixWord ++ tailWord_6889632) baseStart_6889632 baseEnd_6889632 := by
    simpa [prefixWord, tailWord_6889632, baseEnd_6889632] using wordTrace_append hprefix tailTrace_6889632
  have hstable : (prefixWord ++ tailWord_6889632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889632).length < 2 ^ (prefixWord ++ tailWord_6889632).sum := by decide
  have hdescent : baseEnd_6889632 < baseStart_6889632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889635 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 5]
def baseStart_6889635 : Nat := 118140960795 + 6889635 * 2 ^ 59
def prefixEnd_6889635 : Nat := 4983230072969 + 3 ^ 40 * 6889635 * 2
def baseEnd_6889635 : Nat := 3537694289039257005077651

theorem tailTrace_6889635 : CollatzResearch.WordTrace tailWord_6889635 prefixEnd_6889635 3537694289039257005077651 := by
  unfold tailWord_6889635
  simp only [CollatzResearch.WordTrace]
  refine ⟨251285632395036525824742359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167523754930024350549828239 251285632395036525824742359)
  ·
    refine ⟨376928448592554788737113539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251285632395036525824742359 376928448592554788737113539)
    ·
      refine ⟨565392672888832183105670309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376928448592554788737113539 565392672888832183105670309)
      ·
        refine ⟨106011126166656034332313183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 565392672888832183105670309 106011126166656034332313183)
        ·
          refine ⟨159016689249984051498469775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106011126166656034332313183 159016689249984051498469775)
          ·
            refine ⟨238525033874976077247704663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159016689249984051498469775 238525033874976077247704663)
            ·
              refine ⟨357787550812464115871556995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238525033874976077247704663 357787550812464115871556995)
              ·
                refine ⟨536681326218696173807335493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357787550812464115871556995 536681326218696173807335493)
                ·
                  refine ⟨100627748666005532588875405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 536681326218696173807335493 100627748666005532588875405)
                  ·
                    refine ⟨37735405749752074720828277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100627748666005532588875405 37735405749752074720828277)
                    ·
                      refine ⟨3537694289039257005077651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37735405749752074720828277 3537694289039257005077651)
                      ·
                        rfl

theorem cell23_6889635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_6889635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889635 prefixEnd_6889635 := by exact prefixLift 6889635
  have htrace : WordTrace (prefixWord ++ tailWord_6889635) baseStart_6889635 baseEnd_6889635 := by
    simpa [prefixWord, tailWord_6889635, baseEnd_6889635] using wordTrace_append hprefix tailTrace_6889635
  have hstable : (prefixWord ++ tailWord_6889635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889635).length < 2 ^ (prefixWord ++ tailWord_6889635).sum := by decide
  have hdescent : baseEnd_6889635 < baseStart_6889635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889726 : List Nat := [4, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2]
def baseStart_6889726 : Nat := 118140960795 + 6889726 * 2 ^ 59
def prefixEnd_6889726 : Nat := 4983230072969 + 3 ^ 40 * 6889726 * 2
def baseEnd_6889726 : Nat := 3537741015778816149039733

theorem tailTrace_6889726 : CollatzResearch.WordTrace tailWord_6889726 prefixEnd_6889726 3537741015778816149039733 := by
  unfold tailWord_6889726
  simp only [CollatzResearch.WordTrace]
  refine ⟨31411118929713356045788129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167525967625137898910870021 31411118929713356045788129)
  ·
    refine ⟨23558339197285017034341097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31411118929713356045788129 23558339197285017034341097)
    ·
      refine ⟨17668754397963762775755823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23558339197285017034341097 17668754397963762775755823)
      ·
        refine ⟨26503131596945644163633735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17668754397963762775755823 26503131596945644163633735)
        ·
          refine ⟨39754697395418466245450603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26503131596945644163633735 39754697395418466245450603)
          ·
            refine ⟨59632046093127699368175905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39754697395418466245450603 59632046093127699368175905)
            ·
              refine ⟨44724034569845774526131929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59632046093127699368175905 44724034569845774526131929)
              ·
                refine ⟨33543025927384330894598947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44724034569845774526131929 33543025927384330894598947)
                ·
                  refine ⟨50314538891076496341898421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33543025927384330894598947 50314538891076496341898421)
                  ·
                    refine ⟨4716988021038421532052977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50314538891076496341898421 4716988021038421532052977)
                    ·
                      refine ⟨3537741015778816149039733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4716988021038421532052977 3537741015778816149039733)
                      ·
                        rfl

theorem cell23_6889726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_6889726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889726 prefixEnd_6889726 := by exact prefixLift 6889726
  have htrace : WordTrace (prefixWord ++ tailWord_6889726) baseStart_6889726 baseEnd_6889726 := by
    simpa [prefixWord, tailWord_6889726, baseEnd_6889726] using wordTrace_append hprefix tailTrace_6889726
  have hstable : (prefixWord ++ tailWord_6889726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889726).length < 2 ^ (prefixWord ++ tailWord_6889726).sum := by decide
  have hdescent : baseEnd_6889726 < baseStart_6889726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889739 : List Nat := [1, 1, 1, 1, 5, 2, 2, 4, 1, 1, 4]
def baseStart_6889739 : Nat := 118140960795 + 6889739 * 2 ^ 59
def prefixEnd_6889739 : Nat := 4983230072969 + 3 ^ 40 * 6889739 * 2
def baseEnd_6889739 : Nat := 3537747691027324598177173

theorem tailTrace_6889739 : CollatzResearch.WordTrace tailWord_6889739 prefixEnd_6889739 3537747691027324598177173 := by
  unfold tailWord_6889739
  simp only [CollatzResearch.WordTrace]
  refine ⟨251289425586659751586528271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167526283724439834391018847 251289425586659751586528271)
  ·
    refine ⟨376934138379989627379792407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251289425586659751586528271 376934138379989627379792407)
    ·
      refine ⟨565401207569984441069688611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376934138379989627379792407 565401207569984441069688611)
      ·
        refine ⟨848101811354976661604532917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565401207569984441069688611 848101811354976661604532917)
        ·
          refine ⟨79509544814529062025424961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 848101811354976661604532917 79509544814529062025424961)
          ·
            refine ⟨59632158610896796519068721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79509544814529062025424961 59632158610896796519068721)
            ·
              refine ⟨44724118958172597389301541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59632158610896796519068721 44724118958172597389301541)
              ·
                refine ⟨8385772304657362010494039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44724118958172597389301541 8385772304657362010494039)
                ·
                  refine ⟨12578658456986043015741059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8385772304657362010494039 12578658456986043015741059)
                  ·
                    refine ⟨18867987685479064523611589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12578658456986043015741059 18867987685479064523611589)
                    ·
                      refine ⟨3537747691027324598177173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18867987685479064523611589 3537747691027324598177173)
                      ·
                        rfl

theorem cell23_6889739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 1, 4].length) (baseStart_6889739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889739 prefixEnd_6889739 := by exact prefixLift 6889739
  have htrace : WordTrace (prefixWord ++ tailWord_6889739) baseStart_6889739 baseEnd_6889739 := by
    simpa [prefixWord, tailWord_6889739, baseEnd_6889739] using wordTrace_append hprefix tailTrace_6889739
  have hstable : (prefixWord ++ tailWord_6889739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889739).length < 2 ^ (prefixWord ++ tailWord_6889739).sum := by decide
  have hdescent : baseEnd_6889739 < baseStart_6889739 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889756 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 7, 2, 2]
def baseStart_6889756 : Nat := 118140960795 + 6889756 * 2 ^ 59
def prefixEnd_6889756 : Nat := 4983230072969 + 3 ^ 40 * 6889756 * 2
def baseEnd_6889756 : Nat := 3537756420198451031664595

theorem tailTrace_6889756 : CollatzResearch.WordTrace tailWord_6889756 prefixEnd_6889756 3537756420198451031664595 := by
  unfold tailWord_6889756
  simp only [CollatzResearch.WordTrace]
  refine ⟨125645022813799081744948561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167526697085065442326598081 125645022813799081744948561)
  ·
    refine ⟨94233767110349311308711421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125645022813799081744948561 94233767110349311308711421)
    ·
      refine ⟨35337662666380991740766783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94233767110349311308711421 35337662666380991740766783)
      ·
        refine ⟨53006493999571487611150175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35337662666380991740766783 53006493999571487611150175)
        ·
          refine ⟨79509740999357231416725263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53006493999571487611150175 79509740999357231416725263)
          ·
            refine ⟨119264611499035847125087895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79509740999357231416725263 119264611499035847125087895)
            ·
              refine ⟨178896917248553770687631843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119264611499035847125087895 178896917248553770687631843)
              ·
                refine ⟨268345375872830656031447765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178896917248553770687631843 268345375872830656031447765)
                ·
                  refine ⟨6289344747019468500737057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 268345375872830656031447765 6289344747019468500737057)
                  ·
                    refine ⟨4717008560264601375552793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6289344747019468500737057 4717008560264601375552793)
                    ·
                      refine ⟨3537756420198451031664595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4717008560264601375552793 3537756420198451031664595)
                      ·
                        rfl

theorem cell23_6889756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_6889756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889756 prefixEnd_6889756 := by exact prefixLift 6889756
  have htrace : WordTrace (prefixWord ++ tailWord_6889756) baseStart_6889756 baseEnd_6889756 := by
    simpa [prefixWord, tailWord_6889756, baseEnd_6889756] using wordTrace_append hprefix tailTrace_6889756
  have hstable : (prefixWord ++ tailWord_6889756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889756).length < 2 ^ (prefixWord ++ tailWord_6889756).sum := by decide
  have hdescent : baseEnd_6889756 < baseStart_6889756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889767 : List Nat := [1, 1, 8, 1, 1, 1, 2, 1, 3, 1, 3]
def baseStart_6889767 : Nat := 118140960795 + 6889767 * 2 ^ 59
def prefixEnd_6889767 : Nat := 4983230072969 + 3 ^ 40 * 6889767 * 2
def baseEnd_6889767 : Nat := 3537762068485650488627045

theorem tailTrace_6889767 : CollatzResearch.WordTrace tailWord_6889767 prefixEnd_6889767 3537762068485650488627045 := by
  unfold tailWord_6889767
  simp only [CollatzResearch.WordTrace]
  refine ⟨251290446830558312368547555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167526964553705541579031703 251290446830558312368547555)
  ·
    refine ⟨376935670245837468552821333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251290446830558312368547555 376935670245837468552821333)
    ·
      refine ⟨4417214885693407834603375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 376935670245837468552821333 4417214885693407834603375)
      ·
        refine ⟨6625822328540111751905063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4417214885693407834603375 6625822328540111751905063)
        ·
          refine ⟨9938733492810167627857595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6625822328540111751905063 9938733492810167627857595)
          ·
            refine ⟨14908100239215251441786393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9938733492810167627857595 14908100239215251441786393)
            ·
              refine ⟨11181075179411438581339795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14908100239215251441786393 11181075179411438581339795)
              ·
                refine ⟨16771612769117157872009693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11181075179411438581339795 16771612769117157872009693)
                ·
                  refine ⟨6289354788418934202003635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16771612769117157872009693 6289354788418934202003635)
                  ·
                    refine ⟨9434032182628401303005453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6289354788418934202003635 9434032182628401303005453)
                    ·
                      refine ⟨3537762068485650488627045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9434032182628401303005453 3537762068485650488627045)
                      ·
                        rfl

theorem cell23_6889767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_6889767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889767 prefixEnd_6889767 := by exact prefixLift 6889767
  have htrace : WordTrace (prefixWord ++ tailWord_6889767) baseStart_6889767 baseEnd_6889767 := by
    simpa [prefixWord, tailWord_6889767, baseEnd_6889767] using wordTrace_append hprefix tailTrace_6889767
  have hstable : (prefixWord ++ tailWord_6889767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889767).length < 2 ^ (prefixWord ++ tailWord_6889767).sum := by decide
  have hdescent : baseEnd_6889767 < baseStart_6889767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889786 : List Nat := [3, 1, 1, 1, 4, 4, 1, 1, 1, 2, 4]
def baseStart_6889786 : Nat := 118140960795 + 6889786 * 2 ^ 59
def prefixEnd_6889786 : Nat := 4983230072969 + 3 ^ 40 * 6889786 * 2
def baseEnd_6889786 : Nat := 3537771824618085914289457

theorem tailTrace_6889786 : CollatzResearch.WordTrace tailWord_6889786 prefixEnd_6889786 3537771824618085914289457 := by
  unfold tailWord_6889786
  simp only [CollatzResearch.WordTrace]
  refine ⟨62822784954372369653372303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167527426544992985742326141 62822784954372369653372303)
  ·
    refine ⟨94234177431558554480058455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62822784954372369653372303 94234177431558554480058455)
    ·
      refine ⟨141351266147337831720087683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94234177431558554480058455 141351266147337831720087683)
      ·
        refine ⟨212026899221006747580131525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141351266147337831720087683 212026899221006747580131525)
        ·
          refine ⟨39755043603938765171274661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212026899221006747580131525 39755043603938765171274661)
          ·
            refine ⟨7454070675738518469613999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39755043603938765171274661 7454070675738518469613999)
            ·
              refine ⟨11181106013607777704420999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7454070675738518469613999 11181106013607777704420999)
              ·
                refine ⟨16771659020411666556631499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11181106013607777704420999 16771659020411666556631499)
                ·
                  refine ⟨25157488530617499834947249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16771659020411666556631499 25157488530617499834947249)
                  ·
                    refine ⟨18868116397963124876210437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25157488530617499834947249 18868116397963124876210437)
                    ·
                      refine ⟨3537771824618085914289457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18868116397963124876210437 3537771824618085914289457)
                      ·
                        rfl

theorem cell23_6889786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 1, 2, 4].length) (baseStart_6889786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889786 prefixEnd_6889786 := by exact prefixLift 6889786
  have htrace : WordTrace (prefixWord ++ tailWord_6889786) baseStart_6889786 baseEnd_6889786 := by
    simpa [prefixWord, tailWord_6889786, baseEnd_6889786] using wordTrace_append hprefix tailTrace_6889786
  have hstable : (prefixWord ++ tailWord_6889786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889786).length < 2 ^ (prefixWord ++ tailWord_6889786).sum := by decide
  have hdescent : baseEnd_6889786 < baseStart_6889786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889796 : List Nat := [2, 3, 4, 1, 2, 1, 1, 9]
def baseStart_6889796 : Nat := 118140960795 + 6889796 * 2 ^ 59
def prefixEnd_6889796 : Nat := 4983230072969 + 3 ^ 40 * 6889796 * 2
def baseEnd_6889796 : Nat := 131028776274986328709793

theorem tailTrace_6889796 : CollatzResearch.WordTrace tailWord_6889796 prefixEnd_6889796 131028776274986328709793 := by
  unfold tailWord_6889796
  simp only [CollatzResearch.WordTrace]
  refine ⟨125645752273726625160676621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167527669698302166880902161 125645752273726625160676621)
  ·
    refine ⟨47117157102647484435253733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125645752273726625160676621 47117157102647484435253733)
    ·
      refine ⟨8834466956746403331610075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47117157102647484435253733 8834466956746403331610075)
      ·
        refine ⟨13251700435119604997415113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8834466956746403331610075 13251700435119604997415113)
        ·
          refine ⟨9938775326339703748061335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13251700435119604997415113 9938775326339703748061335)
          ·
            refine ⟨14908162989509555622092003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9938775326339703748061335 14908162989509555622092003)
            ·
              refine ⟨22362244484264333433138005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14908162989509555622092003 22362244484264333433138005)
              ·
                refine ⟨131028776274986328709793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22362244484264333433138005 131028776274986328709793)
                ·
                  rfl

theorem cell23_6889796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 9].length) (baseStart_6889796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889796 prefixEnd_6889796 := by exact prefixLift 6889796
  have htrace : WordTrace (prefixWord ++ tailWord_6889796) baseStart_6889796 baseEnd_6889796 := by
    simpa [prefixWord, tailWord_6889796, baseEnd_6889796] using wordTrace_append hprefix tailTrace_6889796
  have hstable : (prefixWord ++ tailWord_6889796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889796).length < 2 ^ (prefixWord ++ tailWord_6889796).sum := by decide
  have hdescent : baseEnd_6889796 < baseStart_6889796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889840 : List Nat := [2, 1, 1, 1, 4, 5, 2, 1, 2, 1, 3]
def baseStart_6889840 : Nat := 118140960795 + 6889840 * 2 ^ 59
def prefixEnd_6889840 : Nat := 4983230072969 + 3 ^ 40 * 6889840 * 2
def baseEnd_6889840 : Nat := 3537799552573428703014209

theorem tailTrace_6889840 : CollatzResearch.WordTrace tailWord_6889840 prefixEnd_6889840 3537799552573428703014209 := by
  unfold tailWord_6889840
  simp only [CollatzResearch.WordTrace]
  refine ⟨125646554679646922917977487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167528739572862563890636649 125646554679646922917977487)
  ·
    refine ⟨188469832019470384376966231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125646554679646922917977487 188469832019470384376966231)
    ·
      refine ⟨282704748029205576565449347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188469832019470384376966231 282704748029205576565449347)
      ·
        refine ⟨424057122043808364848174021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282704748029205576565449347 424057122043808364848174021)
        ·
          refine ⟨79510710383214068409032629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 424057122043808364848174021 79510710383214068409032629)
          ·
            refine ⟨7454129098426318913346809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79510710383214068409032629 7454129098426318913346809)
            ·
              refine ⟨5590596823819739185010107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7454129098426318913346809 5590596823819739185010107)
              ·
                refine ⟨8385895235729608777515161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5590596823819739185010107 8385895235729608777515161)
                ·
                  refine ⟨6289421426797206583136371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8385895235729608777515161 6289421426797206583136371)
                  ·
                    refine ⟨9434132140195809874704557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6289421426797206583136371 9434132140195809874704557)
                    ·
                      refine ⟨3537799552573428703014209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9434132140195809874704557 3537799552573428703014209)
                      ·
                        rfl

theorem cell23_6889840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 2, 1, 3].length) (baseStart_6889840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889840 prefixEnd_6889840 := by exact prefixLift 6889840
  have htrace : WordTrace (prefixWord ++ tailWord_6889840) baseStart_6889840 baseEnd_6889840 := by
    simpa [prefixWord, tailWord_6889840, baseEnd_6889840] using wordTrace_append hprefix tailTrace_6889840
  have hstable : (prefixWord ++ tailWord_6889840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889840).length < 2 ^ (prefixWord ++ tailWord_6889840).sum := by decide
  have hdescent : baseEnd_6889840 < baseStart_6889840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889880 : List Nat := [2, 1, 2, 5, 1, 1, 1, 4, 2, 2, 2]
def baseStart_6889880 : Nat := 118140960795 + 6889880 * 2 ^ 59
def prefixEnd_6889880 : Nat := 4983230072969 + 3 ^ 40 * 6889880 * 2
def baseEnd_6889880 : Nat := 3537820091799608546514025

theorem tailTrace_6889880 : CollatzResearch.WordTrace tailWord_6889880 prefixEnd_6889880 3537820091799608546514025 := by
  unfold tailWord_6889880
  simp only [CollatzResearch.WordTrace]
  refine ⟨125647284139574466333705547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167529712186099288444940729 125647284139574466333705547)
  ·
    refine ⟨188470926209361699500558321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125647284139574466333705547 188470926209361699500558321)
    ·
      refine ⟨141353194657021274625418741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188470926209361699500558321 141353194657021274625418741)
      ·
        refine ⟨13251861999095744496133007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141353194657021274625418741 13251861999095744496133007)
        ·
          refine ⟨19877792998643616744199511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13251861999095744496133007 19877792998643616744199511)
          ·
            refine ⟨29816689497965425116299267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19877792998643616744199511 29816689497965425116299267)
            ·
              refine ⟨44725034246948137674448901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29816689497965425116299267 44725034246948137674448901)
              ·
                refine ⟨8385943921302775813959169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44725034246948137674448901 8385943921302775813959169)
                ·
                  refine ⟨6289457940977081860469377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8385943921302775813959169 6289457940977081860469377)
                  ·
                    refine ⟨4717093455732811395352033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6289457940977081860469377 4717093455732811395352033)
                    ·
                      refine ⟨3537820091799608546514025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4717093455732811395352033 3537820091799608546514025)
                      ·
                        rfl

theorem cell23_6889880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_6889880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889880 prefixEnd_6889880 := by exact prefixLift 6889880
  have htrace : WordTrace (prefixWord ++ tailWord_6889880) baseStart_6889880 baseEnd_6889880 := by
    simpa [prefixWord, tailWord_6889880, baseEnd_6889880] using wordTrace_append hprefix tailTrace_6889880
  have hstable : (prefixWord ++ tailWord_6889880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889880).length < 2 ^ (prefixWord ++ tailWord_6889880).sum := by decide
  have hdescent : baseEnd_6889880 < baseStart_6889880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889906 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2]
def baseStart_6889906 : Nat := 118140960795 + 6889906 * 2 ^ 59
def prefixEnd_6889906 : Nat := 4983230072969 + 3 ^ 40 * 6889906 * 2
def baseEnd_6889906 : Nat := 3537833442296625444788905

theorem tailTrace_6889906 : CollatzResearch.WordTrace tailWord_6889906 prefixEnd_6889906 3537833442296625444788905 := by
  unfold tailWord_6889906
  simp only [CollatzResearch.WordTrace]
  refine ⟨62823879144263684776964393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167530344384703159405238381 62823879144263684776964393)
  ·
    refine ⟨47117909358197763582723295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62823879144263684776964393 47117909358197763582723295)
    ·
      refine ⟨70676864037296645374084943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47117909358197763582723295 70676864037296645374084943)
      ·
        refine ⟨106015296055944968061127415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70676864037296645374084943 106015296055944968061127415)
        ·
          refine ⟨159022944083917452091691123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106015296055944968061127415 159022944083917452091691123)
          ·
            refine ⟨238534416125876178137536685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159022944083917452091691123 238534416125876178137536685)
            ·
              refine ⟨89450406047203566801576257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238534416125876178137536685 89450406047203566801576257)
              ·
                refine ⟨67087804535402675101182193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89450406047203566801576257 67087804535402675101182193)
                ·
                  refine ⟨50315853401552006325886645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67087804535402675101182193 50315853401552006325886645)
                  ·
                    refine ⟨4717111256395500593051873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50315853401552006325886645 4717111256395500593051873)
                    ·
                      refine ⟨3537833442296625444788905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4717111256395500593051873 3537833442296625444788905)
                      ·
                        rfl

theorem cell23_6889906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2].length) (baseStart_6889906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889906 prefixEnd_6889906 := by exact prefixLift 6889906
  have htrace : WordTrace (prefixWord ++ tailWord_6889906) baseStart_6889906 baseEnd_6889906 := by
    simpa [prefixWord, tailWord_6889906, baseEnd_6889906] using wordTrace_append hprefix tailTrace_6889906
  have hstable : (prefixWord ++ tailWord_6889906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889906).length < 2 ^ (prefixWord ++ tailWord_6889906).sum := by decide
  have hdescent : baseEnd_6889906 < baseStart_6889906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889916 : List Nat := [2, 2, 2, 4, 1, 2, 1, 1, 1, 7]
def baseStart_6889916 : Nat := 118140960795 + 6889916 * 2 ^ 59
def prefixEnd_6889916 : Nat := 4983230072969 + 3 ^ 40 * 6889916 * 2
def baseEnd_6889916 : Nat := 1179279525701056801887953

theorem tailTrace_6889916 : CollatzResearch.WordTrace tailWord_6889916 prefixEnd_6889916 1179279525701056801887953 := by
  unfold tailWord_6889916
  simp only [CollatzResearch.WordTrace]
  refine ⟨125647940653509255407860801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167530587538012340543814401 125647940653509255407860801)
  ·
    refine ⟨94235955490131941555895601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125647940653509255407860801 94235955490131941555895601)
    ·
      refine ⟨70676966617598956166921701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94235955490131941555895601 70676966617598956166921701)
      ·
        refine ⟨13251931240799804281297819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70676966617598956166921701 13251931240799804281297819)
        ·
          refine ⟨19877896861199706421946729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13251931240799804281297819 19877896861199706421946729)
          ·
            refine ⟨14908422645899779816460047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19877896861199706421946729 14908422645899779816460047)
            ·
              refine ⟨22362633968849669724690071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14908422645899779816460047 22362633968849669724690071)
              ·
                refine ⟨33543950953274504587035107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22362633968849669724690071 33543950953274504587035107)
                ·
                  refine ⟨50315926429911756880552661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33543950953274504587035107 50315926429911756880552661)
                  ·
                    refine ⟨1179279525701056801887953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50315926429911756880552661 1179279525701056801887953)
                    ·
                      rfl

theorem cell23_6889916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_6889916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889916 prefixEnd_6889916 := by exact prefixLift 6889916
  have htrace : WordTrace (prefixWord ++ tailWord_6889916) baseStart_6889916 baseEnd_6889916 := by
    simpa [prefixWord, tailWord_6889916, baseEnd_6889916] using wordTrace_append hprefix tailTrace_6889916
  have hstable : (prefixWord ++ tailWord_6889916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889916).length < 2 ^ (prefixWord ++ tailWord_6889916).sum := by decide
  have hdescent : baseEnd_6889916 < baseStart_6889916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6889997 : List Nat := [1, 7, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_6889997 : Nat := 118140960795 + 6889997 * 2 ^ 59
def prefixEnd_6889997 : Nat := 4983230072969 + 3 ^ 40 * 6889997 * 2
def baseEnd_6889997 : Nat := 1179293389678728196250329

theorem tailTrace_6889997 : CollatzResearch.WordTrace tailWord_6889997 prefixEnd_6889997 1179293389678728196250329 := by
  unfold tailWord_6889997
  simp only [CollatzResearch.WordTrace]
  refine ⟨251298835619725061649420245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167532557079816707766280163 251298835619725061649420245)
  ·
    refine ⟨5889816459837306132408287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 251298835619725061649420245 5889816459837306132408287)
    ·
      refine ⟨8834724689755959198612431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5889816459837306132408287 8834724689755959198612431)
      ·
        refine ⟨13252087034633938797918647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8834724689755959198612431 13252087034633938797918647)
        ·
          refine ⟨19878130551950908196877971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13252087034633938797918647 19878130551950908196877971)
          ·
            refine ⟨29817195827926362295316957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19878130551950908196877971 29817195827926362295316957)
            ·
              refine ⟨11181448435472385860743859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29817195827926362295316957 11181448435472385860743859)
              ·
                refine ⟨16772172653208578791115789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11181448435472385860743859 16772172653208578791115789)
                ·
                  refine ⟨6289564744953217046668421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16772172653208578791115789 6289564744953217046668421)
                  ·
                    refine ⟨1179293389678728196250329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6289564744953217046668421 1179293389678728196250329)
                    ·
                      rfl

theorem cell23_6889997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_6889997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6889997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6889997 prefixEnd_6889997 := by exact prefixLift 6889997
  have htrace : WordTrace (prefixWord ++ tailWord_6889997) baseStart_6889997 baseEnd_6889997 := by
    simpa [prefixWord, tailWord_6889997, baseEnd_6889997] using wordTrace_append hprefix tailTrace_6889997
  have hstable : (prefixWord ++ tailWord_6889997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6889997).length < 2 ^ (prefixWord ++ tailWord_6889997).sum := by decide
  have hdescent : baseEnd_6889997 < baseStart_6889997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6889997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
