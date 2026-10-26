import V185TrunkScan22Chunk347

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3104381 : List Nat := [1, 4, 1, 1, 4, 1, 2, 1, 2, 5]
def baseStart_3104381 : Nat := 118140960795 + 3104381 * 2 ^ 59
def prefixEnd_3104381 : Nat := 4983230072969 + 3 ^ 40 * 3104381 * 2
def baseEnd_3104381 : Nat := 1062693058456882552507145

theorem tailTrace_3104381 : CollatzResearch.WordTrace tailWord_3104381 prefixEnd_3104381 1062693058456882552507145 := by
  unfold tailWord_3104381
  simp only [CollatzResearch.WordTrace]
  refine ⟨113226076966365297909640997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75484051310910198606427331 113226076966365297909640997)
  ·
    refine ⟨21229889431193493358057687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113226076966365297909640997 21229889431193493358057687)
    ·
      refine ⟨31844834146790240037086531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21229889431193493358057687 31844834146790240037086531)
      ·
        refine ⟨47767251220185360055629797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31844834146790240037086531 47767251220185360055629797)
        ·
          refine ⟨8956359603784755010430587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47767251220185360055629797 8956359603784755010430587)
          ·
            refine ⟨13434539405677132515645881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8956359603784755010430587 13434539405677132515645881)
            ·
              refine ⟨10075904554257849386734411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13434539405677132515645881 10075904554257849386734411)
              ·
                refine ⟨15113856831386774080101617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10075904554257849386734411 15113856831386774080101617)
                ·
                  refine ⟨11335392623540080560076213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15113856831386774080101617 11335392623540080560076213)
                  ·
                    refine ⟨1062693058456882552507145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11335392623540080560076213 1062693058456882552507145)
                    ·
                      rfl

theorem cell22_3104381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_3104381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3104381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3104381 prefixEnd_3104381 := by exact prefixLift 3104381
  have htrace : WordTrace (prefixWord ++ tailWord_3104381) baseStart_3104381 baseEnd_3104381 := by
    simpa [prefixWord, tailWord_3104381, baseEnd_3104381] using wordTrace_append hprefix tailTrace_3104381
  have hstable : (prefixWord ++ tailWord_3104381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104381).length < 2 ^ (prefixWord ++ tailWord_3104381).sum := by decide
  have hdescent : baseEnd_3104381 < baseStart_3104381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104404 : List Nat := [2, 4, 2, 2, 2, 2, 1, 3, 1, 3]
def baseStart_3104404 : Nat := 118140960795 + 3104404 * 2 ^ 59
def prefixEnd_3104404 : Nat := 4983230072969 + 3 ^ 40 * 3104404 * 2
def baseEnd_3104404 : Nat := 1062700931826918159182075

theorem tailTrace_3104404 : CollatzResearch.WordTrace tailWord_3104404 prefixEnd_3104404 1062700931826918159182075 := by
  unfold tailWord_3104404
  simp only [CollatzResearch.WordTrace]
  refine ⟨56613457922640986418864133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75484610563521315225152177 56613457922640986418864133)
  ·
    refine ⟨10615023360495184953537025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56613457922640986418864133 10615023360495184953537025)
    ·
      refine ⟨7961267520371388715152769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10615023360495184953537025 7961267520371388715152769)
      ·
        refine ⟨5970950640278541536364577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7961267520371388715152769 5970950640278541536364577)
        ·
          refine ⟨4478212980208906152273433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5970950640278541536364577 4478212980208906152273433)
          ·
            refine ⟨3358659735156679614205075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4478212980208906152273433 3358659735156679614205075)
            ·
              refine ⟨5037989602735019421307613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3358659735156679614205075 5037989602735019421307613)
              ·
                refine ⟨1889246101025632282990355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5037989602735019421307613 1889246101025632282990355)
                ·
                  refine ⟨2833869151538448424485533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1889246101025632282990355 2833869151538448424485533)
                  ·
                    refine ⟨1062700931826918159182075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2833869151538448424485533 1062700931826918159182075)
                    ·
                      rfl

theorem cell22_3104404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_3104404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3104404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3104404 prefixEnd_3104404 := by exact prefixLift 3104404
  have htrace : WordTrace (prefixWord ++ tailWord_3104404) baseStart_3104404 baseEnd_3104404 := by
    simpa [prefixWord, tailWord_3104404, baseEnd_3104404] using wordTrace_append hprefix tailTrace_3104404
  have hstable : (prefixWord ++ tailWord_3104404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104404).length < 2 ^ (prefixWord ++ tailWord_3104404).sum := by decide
  have hdescent : baseEnd_3104404 < baseStart_3104404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104522 : List Nat := [3, 1, 2, 2, 1, 4, 2, 3, 1, 3]
def baseStart_3104522 : Nat := 118140960795 + 3104522 * 2 ^ 59
def prefixEnd_3104522 : Nat := 4983230072969 + 3 ^ 40 * 3104522 * 2
def baseEnd_3104522 : Nat := 1062741325638405184731713

theorem tailTrace_3104522 : CollatzResearch.WordTrace tailWord_3104522 prefixEnd_3104522 1062741325638405184731713 := by
  unfold tailWord_3104522
  simp only [CollatzResearch.WordTrace]
  refine ⟨28307804914713619747630955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75487479772569652660349213 28307804914713619747630955)
  ·
    refine ⟨42461707372070429621446433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28307804914713619747630955 42461707372070429621446433)
    ·
      refine ⟨31846280529052822216084825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42461707372070429621446433 31846280529052822216084825)
      ·
        refine ⟨23884710396789616662063619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31846280529052822216084825 23884710396789616662063619)
        ·
          refine ⟨35827065595184424993095429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23884710396789616662063619 35827065595184424993095429)
          ·
            refine ⟨6717574799097079686205393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35827065595184424993095429 6717574799097079686205393)
            ·
              refine ⟨5038181099322809764654045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6717574799097079686205393 5038181099322809764654045)
              ·
                refine ⟨1889317912246053661745267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5038181099322809764654045 1889317912246053661745267)
                ·
                  refine ⟨2833976868369080492617901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1889317912246053661745267 2833976868369080492617901)
                  ·
                    refine ⟨1062741325638405184731713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2833976868369080492617901 1062741325638405184731713)
                    ·
                      rfl

theorem cell22_3104522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_3104522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3104522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3104522 prefixEnd_3104522 := by exact prefixLift 3104522
  have htrace : WordTrace (prefixWord ++ tailWord_3104522) baseStart_3104522 baseEnd_3104522 := by
    simpa [prefixWord, tailWord_3104522, baseEnd_3104522] using wordTrace_append hprefix tailTrace_3104522
  have hstable : (prefixWord ++ tailWord_3104522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104522).length < 2 ^ (prefixWord ++ tailWord_3104522).sum := by decide
  have hdescent : baseEnd_3104522 < baseStart_3104522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104531 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 5, 4]
def baseStart_3104531 : Nat := 118140960795 + 3104531 * 2 ^ 59
def prefixEnd_3104531 : Nat := 4983230072969 + 3 ^ 40 * 3104531 * 2
def baseEnd_3104531 : Nat := 1062744406522332161256685

theorem tailTrace_3104531 : CollatzResearch.WordTrace tailWord_3104531 prefixEnd_3104531 1062744406522332161256685 := by
  unfold tailWord_3104531
  simp only [CollatzResearch.WordTrace]
  refine ⟨113231547915821873527601447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75487698610547915685067631 113231547915821873527601447)
  ·
    refine ⟨169847321873732810291402171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113231547915821873527601447 169847321873732810291402171)
    ·
      refine ⟨254770982810599215437103257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169847321873732810291402171 254770982810599215437103257)
      ·
        refine ⟨191078237107949411577827443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254770982810599215437103257 191078237107949411577827443)
        ·
          refine ⟨286617355661924117366741165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191078237107949411577827443 286617355661924117366741165)
          ·
            refine ⟨107481508373221544012527937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286617355661924117366741165 107481508373221544012527937)
            ·
              refine ⟨80611131279916158009395953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107481508373221544012527937 80611131279916158009395953)
              ·
                refine ⟨60458348459937118507046965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80611131279916158009395953 60458348459937118507046965)
                ·
                  refine ⟨5667970168119104860035653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60458348459937118507046965 5667970168119104860035653)
                  ·
                    refine ⟨1062744406522332161256685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5667970168119104860035653 1062744406522332161256685)
                    ·
                      rfl

theorem cell22_3104531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 4].length) (baseStart_3104531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3104531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3104531 prefixEnd_3104531 := by exact prefixLift 3104531
  have htrace : WordTrace (prefixWord ++ tailWord_3104531) baseStart_3104531 baseEnd_3104531 := by
    simpa [prefixWord, tailWord_3104531, baseEnd_3104531] using wordTrace_append hprefix tailTrace_3104531
  have hstable : (prefixWord ++ tailWord_3104531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104531).length < 2 ^ (prefixWord ++ tailWord_3104531).sum := by decide
  have hdescent : baseEnd_3104531 < baseStart_3104531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104535 : List Nat := [1, 1, 3, 4, 2, 3, 1, 2, 5]
def baseStart_3104535 : Nat := 118140960795 + 3104535 * 2 ^ 59
def prefixEnd_3104535 : Nat := 4983230072969 + 3 ^ 40 * 3104535 * 2
def baseEnd_3104535 : Nat := 354248591934692494718891

theorem tailTrace_3104535 : CollatzResearch.WordTrace tailWord_3104535 prefixEnd_3104535 354248591934692494718891 := by
  unfold tailWord_3104535
  simp only [CollatzResearch.WordTrace]
  refine ⟨113231693807807382210747059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75487795871871588140498039 113231693807807382210747059)
  ·
    refine ⟨169847540711711073316120589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113231693807807382210747059 169847540711711073316120589)
    ·
      refine ⟨63692827766891652493545221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169847540711711073316120589 63692827766891652493545221)
      ·
        refine ⟨11942405206292184842539729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63692827766891652493545221 11942405206292184842539729)
        ·
          refine ⟨8956803904719138631904797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11942405206292184842539729 8956803904719138631904797)
          ·
            refine ⟨3358801464269676986964299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8956803904719138631904797 3358801464269676986964299)
            ·
              refine ⟨5038202196404515480446449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3358801464269676986964299 5038202196404515480446449)
              ·
                refine ⟨3778651647303386610334837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5038202196404515480446449 3778651647303386610334837)
                ·
                  refine ⟨354248591934692494718891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3778651647303386610334837 354248591934692494718891)
                  ·
                    rfl

theorem cell22_3104535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 5].length) (baseStart_3104535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3104535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3104535 prefixEnd_3104535 := by exact prefixLift 3104535
  have htrace : WordTrace (prefixWord ++ tailWord_3104535) baseStart_3104535 baseEnd_3104535 := by
    simpa [prefixWord, tailWord_3104535, baseEnd_3104535] using wordTrace_append hprefix tailTrace_3104535
  have hstable : (prefixWord ++ tailWord_3104535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104535).length < 2 ^ (prefixWord ++ tailWord_3104535).sum := by decide
  have hdescent : baseEnd_3104535 < baseStart_3104535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104593 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 4, 4]
def baseStart_3104593 : Nat := 118140960795 + 3104593 * 2 ^ 59
def prefixEnd_3104593 : Nat := 4983230072969 + 3 ^ 40 * 3104593 * 2
def baseEnd_3104593 : Nat := 1062765630389384666206495

theorem tailTrace_3104593 : CollatzResearch.WordTrace tailWord_3104593 prefixEnd_3104593 1062765630389384666206495 := by
  unfold tailWord_3104593
  simp only [CollatzResearch.WordTrace]
  refine ⟨113233809241597258116358433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75489206161064838744238955 113233809241597258116358433)
  ·
    refine ⟨84925356931197943587268825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113233809241597258116358433 84925356931197943587268825)
    ·
      refine ⟨63694017698398457690451619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84925356931197943587268825 63694017698398457690451619)
      ·
        refine ⟨95541026547597686535677429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63694017698398457690451619 95541026547597686535677429)
        ·
          refine ⟨8956971238837283112719759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95541026547597686535677429 8956971238837283112719759)
          ·
            refine ⟨13435456858255924669079639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8956971238837283112719759 13435456858255924669079639)
            ·
              refine ⟨20153185287383887003619459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13435456858255924669079639 20153185287383887003619459)
              ·
                refine ⟨30229777931075830505429189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20153185287383887003619459 30229777931075830505429189)
                ·
                  refine ⟨5668083362076718219767973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30229777931075830505429189 5668083362076718219767973)
                  ·
                    refine ⟨1062765630389384666206495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5668083362076718219767973 1062765630389384666206495)
                    ·
                      rfl

theorem cell22_3104593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_3104593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3104593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3104593 prefixEnd_3104593 := by exact prefixLift 3104593
  have htrace : WordTrace (prefixWord ++ tailWord_3104593) baseStart_3104593 baseEnd_3104593 := by
    simpa [prefixWord, tailWord_3104593, baseEnd_3104593] using wordTrace_append hprefix tailTrace_3104593
  have hstable : (prefixWord ++ tailWord_3104593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104593).length < 2 ^ (prefixWord ++ tailWord_3104593).sum := by decide
  have hdescent : baseEnd_3104593 < baseStart_3104593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104597 : List Nat := [1, 3, 2, 2, 2, 3, 3, 2, 4]
def baseStart_3104597 : Nat := 118140960795 + 3104597 * 2 ^ 59
def prefixEnd_3104597 : Nat := 4983230072969 + 3 ^ 40 * 3104597 * 2
def baseEnd_3104597 : Nat := 354255666557043329702161

theorem tailTrace_3104597 : CollatzResearch.WordTrace tailWord_3104597 prefixEnd_3104597 354255666557043329702161 := by
  unfold tailWord_3104597
  simp only [CollatzResearch.WordTrace]
  refine ⟨113233955133582766799504045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75489303422388511199669363 113233955133582766799504045)
  ·
    refine ⟨42462733175093537549814017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113233955133582766799504045 42462733175093537549814017)
    ·
      refine ⟨31847049881320153162360513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42462733175093537549814017 31847049881320153162360513)
      ·
        refine ⟨23885287410990114871770385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31847049881320153162360513 23885287410990114871770385)
        ·
          refine ⟨17913965558242586153827789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23885287410990114871770385 17913965558242586153827789)
          ·
            refine ⟨6717737084340969807685421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17913965558242586153827789 6717737084340969807685421)
            ·
              refine ⟨2519151406627863677882033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6717737084340969807685421 2519151406627863677882033)
              ·
                refine ⟨1889363554970897758411525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2519151406627863677882033 1889363554970897758411525)
                ·
                  refine ⟨354255666557043329702161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1889363554970897758411525 354255666557043329702161)
                  ·
                    rfl

theorem cell22_3104597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 2, 4].length) (baseStart_3104597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3104597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3104597 prefixEnd_3104597 := by exact prefixLift 3104597
  have htrace : WordTrace (prefixWord ++ tailWord_3104597) baseStart_3104597 baseEnd_3104597 := by
    simpa [prefixWord, tailWord_3104597, baseEnd_3104597] using wordTrace_append hprefix tailTrace_3104597
  have hstable : (prefixWord ++ tailWord_3104597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104597).length < 2 ^ (prefixWord ++ tailWord_3104597).sum := by decide
  have hdescent : baseEnd_3104597 < baseStart_3104597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104608 : List Nat := [2, 1, 1, 3, 3, 3, 2, 7]
def baseStart_3104608 : Nat := 118140960795 + 3104608 * 2 ^ 59
def prefixEnd_3104608 : Nat := 4983230072969 + 3 ^ 40 * 3104608 * 2
def baseEnd_3104608 : Nat := 118085640577325514120161

theorem tailTrace_3104608 : CollatzResearch.WordTrace tailWord_3104608 prefixEnd_3104608 118085640577325514120161 := by
  unfold tailWord_3104608
  simp only [CollatzResearch.WordTrace]
  refine ⟨56617178168271457839077239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75489570891028610452102985 56617178168271457839077239)
  ·
    refine ⟨84925767252407186758615859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56617178168271457839077239 84925767252407186758615859)
    ·
      refine ⟨127388650878610780137923789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84925767252407186758615859 127388650878610780137923789)
      ·
        refine ⟨47770744079479042551721421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127388650878610780137923789 47770744079479042551721421)
        ·
          refine ⟨17914029029804640956895533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47770744079479042551721421 17914029029804640956895533)
          ·
            refine ⟨6717760886176740358835825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17914029029804640956895533 6717760886176740358835825)
            ·
              refine ⟨5038320664632555269126869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6717760886176740358835825 5038320664632555269126869)
              ·
                refine ⟨118085640577325514120161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5038320664632555269126869 118085640577325514120161)
                ·
                  rfl

theorem cell22_3104608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 7].length) (baseStart_3104608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3104608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3104608 prefixEnd_3104608 := by exact prefixLift 3104608
  have htrace : WordTrace (prefixWord ++ tailWord_3104608) baseStart_3104608 baseEnd_3104608 := by
    simpa [prefixWord, tailWord_3104608, baseEnd_3104608] using wordTrace_append hprefix tailTrace_3104608
  have hstable : (prefixWord ++ tailWord_3104608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104608).length < 2 ^ (prefixWord ++ tailWord_3104608).sum := by decide
  have hdescent : baseEnd_3104608 < baseStart_3104608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104612 : List Nat := [2, 3, 1, 1, 5, 1, 1, 3, 2, 3]
def baseStart_3104612 : Nat := 118140960795 + 3104612 * 2 ^ 59
def prefixEnd_3104612 : Nat := 4983230072969 + 3 ^ 40 * 3104612 * 2
def baseEnd_3104612 : Nat := 1062772134477674949981437

theorem tailTrace_3104612 : CollatzResearch.WordTrace tailWord_3104612 prefixEnd_3104612 1062772134477674949981437 := by
  unfold tailWord_3104612
  simp only [CollatzResearch.WordTrace]
  refine ⟨56617251114264212180650045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75489668152352282907533393 56617251114264212180650045)
  ·
    refine ⟨21231469167849079567743767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56617251114264212180650045 21231469167849079567743767)
    ·
      refine ⟨31847203751773619351615651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21231469167849079567743767 31847203751773619351615651)
      ·
        refine ⟨47770805627660429027423477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31847203751773619351615651 47770805627660429027423477)
        ·
          refine ⟨4478513027593165221320951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47770805627660429027423477 4478513027593165221320951)
          ·
            refine ⟨6717769541389747831981427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4478513027593165221320951 6717769541389747831981427)
            ·
              refine ⟨10076654312084621747972141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6717769541389747831981427 10076654312084621747972141)
              ·
                refine ⟨3778745367031733155489553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10076654312084621747972141 3778745367031733155489553)
                ·
                  refine ⟨2834059025273799866617165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3778745367031733155489553 2834059025273799866617165)
                  ·
                    refine ⟨1062772134477674949981437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2834059025273799866617165 1062772134477674949981437)
                    ·
                      rfl

theorem cell22_3104612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_3104612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3104612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3104612 prefixEnd_3104612 := by exact prefixLift 3104612
  have htrace : WordTrace (prefixWord ++ tailWord_3104612) baseStart_3104612 baseEnd_3104612 := by
    simpa [prefixWord, tailWord_3104612, baseEnd_3104612] using wordTrace_append hprefix tailTrace_3104612
  have hstable : (prefixWord ++ tailWord_3104612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104612).length < 2 ^ (prefixWord ++ tailWord_3104612).sum := by decide
  have hdescent : baseEnd_3104612 < baseStart_3104612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104715 : List Nat := [1, 1, 1, 1, 3, 4, 1, 6, 4]
def baseStart_3104715 : Nat := 118140960795 + 3104715 * 2 ^ 59
def prefixEnd_3104715 : Nat := 4983230072969 + 3 ^ 40 * 3104715 * 2
def baseEnd_3104715 : Nat := 354269131160872338218707

theorem tailTrace_3104715 : CollatzResearch.WordTrace tailWord_3104715 prefixEnd_3104715 354269131160872338218707 := by
  unfold tailWord_3104715
  simp only [CollatzResearch.WordTrace]
  refine ⟨113238258947155272952299599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75492172631436848634866399 113238258947155272952299599)
  ·
    refine ⟨169857388420732909428449399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113238258947155272952299599 169857388420732909428449399)
    ·
      refine ⟨254786082631099364142674099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169857388420732909428449399 254786082631099364142674099)
      ·
        refine ⟨382179123946649046214011149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254786082631099364142674099 382179123946649046214011149)
        ·
          refine ⟨143317171479993392330254181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 382179123946649046214011149 143317171479993392330254181)
          ·
            refine ⟨26871969652498761061922659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143317171479993392330254181 26871969652498761061922659)
            ·
              refine ⟨40307954478748141592883989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26871969652498761061922659 40307954478748141592883989)
              ·
                refine ⟨1889435366191319137166437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40307954478748141592883989 1889435366191319137166437)
                ·
                  refine ⟨354269131160872338218707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1889435366191319137166437 354269131160872338218707)
                  ·
                    rfl

theorem cell22_3104715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 6, 4].length) (baseStart_3104715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3104715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3104715 prefixEnd_3104715 := by exact prefixLift 3104715
  have htrace : WordTrace (prefixWord ++ tailWord_3104715) baseStart_3104715 baseEnd_3104715 := by
    simpa [prefixWord, tailWord_3104715, baseEnd_3104715] using wordTrace_append hprefix tailTrace_3104715
  have hstable : (prefixWord ++ tailWord_3104715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104715).length < 2 ^ (prefixWord ++ tailWord_3104715).sum := by decide
  have hdescent : baseEnd_3104715 < baseStart_3104715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104728 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 3, 6]
def baseStart_3104728 : Nat := 118140960795 + 3104728 * 2 ^ 59
def prefixEnd_3104728 : Nat := 4983230072969 + 3 ^ 40 * 3104728 * 2
def baseEnd_3104728 : Nat := 1062811843648289314081081

theorem tailTrace_3104728 : CollatzResearch.WordTrace tailWord_3104728 prefixEnd_3104728 1062811843648289314081081 := by
  unfold tailWord_3104728
  simp only [CollatzResearch.WordTrace]
  refine ⟨56619366548054088086261419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75492488730738784115015225 56619366548054088086261419)
  ·
    refine ⟨84929049822081132129392129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56619366548054088086261419 84929049822081132129392129)
    ·
      refine ⟨63696787366560849097044097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84929049822081132129392129 63696787366560849097044097)
      ·
        refine ⟨47772590524920636822783073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63696787366560849097044097 47772590524920636822783073)
        ·
          refine ⟨35829442893690477617087305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47772590524920636822783073 35829442893690477617087305)
          ·
            refine ⟨26872082170267858212815479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35829442893690477617087305 26872082170267858212815479)
            ·
              refine ⟨40308123255401787319223219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26872082170267858212815479 40308123255401787319223219)
              ·
                refine ⟨60462184883102680978834829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40308123255401787319223219 60462184883102680978834829)
                ·
                  refine ⟨22673319331163505367063061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60462184883102680978834829 22673319331163505367063061)
                  ·
                    refine ⟨1062811843648289314081081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22673319331163505367063061 1062811843648289314081081)
                    ·
                      rfl

theorem cell22_3104728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_3104728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3104728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3104728 prefixEnd_3104728 := by exact prefixLift 3104728
  have htrace : WordTrace (prefixWord ++ tailWord_3104728) baseStart_3104728 baseEnd_3104728 := by
    simpa [prefixWord, tailWord_3104728, baseEnd_3104728] using wordTrace_append hprefix tailTrace_3104728
  have hstable : (prefixWord ++ tailWord_3104728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104728).length < 2 ^ (prefixWord ++ tailWord_3104728).sum := by decide
  have hdescent : baseEnd_3104728 < baseStart_3104728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104766 : List Nat := [4, 2, 2, 2, 1, 2, 3, 2, 4]
def baseStart_3104766 : Nat := 118140960795 + 3104766 * 2 ^ 59
def prefixEnd_3104766 : Nat := 4983230072969 + 3 ^ 40 * 3104766 * 2
def baseEnd_3104766 : Nat := 354274950608289960543655

theorem tailTrace_3104766 : CollatzResearch.WordTrace tailWord_3104766 prefixEnd_3104766 354274950608289960543655 := by
  unfold tailWord_3104766
  simp only [CollatzResearch.WordTrace]
  refine ⟨14155014883746313582800769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75493412713313672441604101 14155014883746313582800769)
  ·
    refine ⟨10616261162809735187100577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14155014883746313582800769 10616261162809735187100577)
    ·
      refine ⟨7962195872107301390325433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10616261162809735187100577 7962195872107301390325433)
      ·
        refine ⟨5971646904080476042744075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7962195872107301390325433 5971646904080476042744075)
        ·
          refine ⟨8957470356120714064116113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5971646904080476042744075 8957470356120714064116113)
          ·
            refine ⟨6718102767090535548087085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8957470356120714064116113 6718102767090535548087085)
            ·
              refine ⟨2519288537658950830532657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6718102767090535548087085 2519288537658950830532657)
              ·
                refine ⟨1889466403244213122899493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2519288537658950830532657 1889466403244213122899493)
                ·
                  refine ⟨354274950608289960543655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1889466403244213122899493 354274950608289960543655)
                  ·
                    rfl

theorem cell22_3104766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_3104766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3104766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3104766 prefixEnd_3104766 := by exact prefixLift 3104766
  have htrace : WordTrace (prefixWord ++ tailWord_3104766) baseStart_3104766 baseEnd_3104766 := by
    simpa [prefixWord, tailWord_3104766, baseEnd_3104766] using wordTrace_append hprefix tailTrace_3104766
  have hstable : (prefixWord ++ tailWord_3104766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104766).length < 2 ^ (prefixWord ++ tailWord_3104766).sum := by decide
  have hdescent : baseEnd_3104766 < baseStart_3104766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104852 : List Nat := [2, 4, 1, 1, 1, 1, 1, 6, 1, 4]
def baseStart_3104852 : Nat := 118140960795 + 3104852 * 2 ^ 59
def prefixEnd_3104852 : Nat := 4983230072969 + 3 ^ 40 * 3104852 * 2
def baseEnd_3104852 : Nat := 1062854291382394323980701

theorem tailTrace_3104852 : CollatzResearch.WordTrace tailWord_3104852 prefixEnd_3104852 1062854291382394323980701 := by
  unfold tailWord_3104852
  simp only [CollatzResearch.WordTrace]
  refine ⟨56621627873829472675018405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75495503831772630233357873 56621627873829472675018405)
  ·
    refine ⟨10616555226343026126565951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56621627873829472675018405 10616555226343026126565951)
    ·
      refine ⟨15924832839514539189848927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10616555226343026126565951 15924832839514539189848927)
      ·
        refine ⟨23887249259271808784773391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15924832839514539189848927 23887249259271808784773391)
        ·
          refine ⟨35830873888907713177160087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23887249259271808784773391 35830873888907713177160087)
          ·
            refine ⟨53746310833361569765740131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35830873888907713177160087 53746310833361569765740131)
            ·
              refine ⟨80619466250042354648610197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53746310833361569765740131 80619466250042354648610197)
              ·
                refine ⟨3779037480470735374153603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 80619466250042354648610197 3779037480470735374153603)
                ·
                  refine ⟨5668556220706103061230405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3779037480470735374153603 5668556220706103061230405)
                  ·
                    refine ⟨1062854291382394323980701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5668556220706103061230405 1062854291382394323980701)
                    ·
                      rfl

theorem cell22_3104852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_3104852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3104852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3104852 prefixEnd_3104852 := by exact prefixLift 3104852
  have htrace : WordTrace (prefixWord ++ tailWord_3104852) baseStart_3104852 baseEnd_3104852 := by
    simpa [prefixWord, tailWord_3104852, baseEnd_3104852] using wordTrace_append hprefix tailTrace_3104852
  have hstable : (prefixWord ++ tailWord_3104852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104852).length < 2 ^ (prefixWord ++ tailWord_3104852).sum := by decide
  have hdescent : baseEnd_3104852 < baseStart_3104852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104867 : List Nat := [1, 1, 1, 5, 1, 1, 3, 5, 4]
def baseStart_3104867 : Nat := 118140960795 + 3104867 * 2 ^ 59
def prefixEnd_3104867 : Nat := 4983230072969 + 3 ^ 40 * 3104867 * 2
def baseEnd_3104867 : Nat := 354286475396313094951885

theorem tailTrace_3104867 : CollatzResearch.WordTrace tailWord_3104867 prefixEnd_3104867 354286475396313094951885 := by
  unfold tailWord_3104867
  simp only [CollatzResearch.WordTrace]
  refine ⟨113243802842604602911832855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75495868561736401941221903 113243802842604602911832855)
  ·
    refine ⟨169865704263906904367749283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113243802842604602911832855 169865704263906904367749283)
    ·
      refine ⟨254798556395860356551623925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169865704263906904367749283 254798556395860356551623925)
      ·
        refine ⟨23887364662111908426714743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 254798556395860356551623925 23887364662111908426714743)
        ·
          refine ⟨35831046993167862640072115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23887364662111908426714743 35831046993167862640072115)
          ·
            refine ⟨53746570489751793960108173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35831046993167862640072115 53746570489751793960108173)
            ·
              refine ⟨20154963933656922735040565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53746570489751793960108173 20154963933656922735040565)
              ·
                refine ⟨1889527868780336506410053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20154963933656922735040565 1889527868780336506410053)
                ·
                  refine ⟨354286475396313094951885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1889527868780336506410053 354286475396313094951885)
                  ·
                    rfl

theorem cell22_3104867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 5, 4].length) (baseStart_3104867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3104867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3104867 prefixEnd_3104867 := by exact prefixLift 3104867
  have htrace : WordTrace (prefixWord ++ tailWord_3104867) baseStart_3104867 baseEnd_3104867 := by
    simpa [prefixWord, tailWord_3104867, baseEnd_3104867] using wordTrace_append hprefix tailTrace_3104867
  have hstable : (prefixWord ++ tailWord_3104867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104867).length < 2 ^ (prefixWord ++ tailWord_3104867).sum := by decide
  have hdescent : baseEnd_3104867 < baseStart_3104867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104869 : List Nat := [1, 3, 1, 3, 2, 2, 4, 1, 1, 4]
def baseStart_3104869 : Nat := 118140960795 + 3104869 * 2 ^ 59
def prefixEnd_3104869 : Nat := 4983230072969 + 3 ^ 40 * 3104869 * 2
def baseEnd_3104869 : Nat := 1062860110829811946305649

theorem tailTrace_3104869 : CollatzResearch.WordTrace tailWord_3104869 prefixEnd_3104869 1062860110829811946305649 := by
  unfold tailWord_3104869
  simp only [CollatzResearch.WordTrace]
  refine ⟨113243875788597357253405661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75495917192398238168937107 113243875788597357253405661)
  ·
    refine ⟨42466453420724008970027123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113243875788597357253405661 42466453420724008970027123)
    ·
      refine ⟨63699680131086013455040685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42466453420724008970027123 63699680131086013455040685)
      ·
        refine ⟨23887380049157255045640257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63699680131086013455040685 23887380049157255045640257)
        ·
          refine ⟨17915535036867941284230193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23887380049157255045640257 17915535036867941284230193)
          ·
            refine ⟨13436651277650955963172645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17915535036867941284230193 13436651277650955963172645)
            ·
              refine ⟨2519372114559554243094871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13436651277650955963172645 2519372114559554243094871)
              ·
                refine ⟨3779058171839331364642307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2519372114559554243094871 3779058171839331364642307)
                ·
                  refine ⟨5668587257758997046963461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3779058171839331364642307 5668587257758997046963461)
                  ·
                    refine ⟨1062860110829811946305649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5668587257758997046963461 1062860110829811946305649)
                    ·
                      rfl

theorem cell22_3104869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 1, 4].length) (baseStart_3104869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3104869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3104869 prefixEnd_3104869 := by exact prefixLift 3104869
  have htrace : WordTrace (prefixWord ++ tailWord_3104869) baseStart_3104869 baseEnd_3104869 := by
    simpa [prefixWord, tailWord_3104869, baseEnd_3104869] using wordTrace_append hprefix tailTrace_3104869
  have hstable : (prefixWord ++ tailWord_3104869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104869).length < 2 ^ (prefixWord ++ tailWord_3104869).sum := by decide
  have hdescent : baseEnd_3104869 < baseStart_3104869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104955 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 1, 7]
def baseStart_3104955 : Nat := 118140960795 + 3104955 * 2 ^ 59
def prefixEnd_3104955 : Nat := 4983230072969 + 3 ^ 40 * 3104955 * 2
def baseEnd_3104955 : Nat := 1062889550387336388655385

theorem tailTrace_3104955 : CollatzResearch.WordTrace tailWord_3104955 prefixEnd_3104955 1062889550387336388655385 := by
  unfold tailWord_3104955
  simp only [CollatzResearch.WordTrace]
  refine ⟨113247012466285793941036319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75498008310857195960690879 113247012466285793941036319)
  ·
    refine ⟨169870518699428690911554479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113247012466285793941036319 169870518699428690911554479)
    ·
      refine ⟨254805778049143036367331719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169870518699428690911554479 254805778049143036367331719)
      ·
        refine ⟨382208667073714554550997579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254805778049143036367331719 382208667073714554550997579)
        ·
          refine ⟨573313000610571831826496369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382208667073714554550997579 573313000610571831826496369)
          ·
            refine ⟨429984750457928873869872277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 573313000610571831826496369 429984750457928873869872277)
            ·
              refine ⟨20155535177715415962650263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 429984750457928873869872277 20155535177715415962650263)
              ·
                refine ⟨30233302766573123943975395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20155535177715415962650263 30233302766573123943975395)
                ·
                  refine ⟨45349954149859685915963093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30233302766573123943975395 45349954149859685915963093)
                  ·
                    refine ⟨1062889550387336388655385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45349954149859685915963093 1062889550387336388655385)
                    ·
                      rfl

theorem cell22_3104955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 7].length) (baseStart_3104955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3104955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3104955 prefixEnd_3104955 := by exact prefixLift 3104955
  have htrace : WordTrace (prefixWord ++ tailWord_3104955) baseStart_3104955 baseEnd_3104955 := by
    simpa [prefixWord, tailWord_3104955, baseEnd_3104955] using wordTrace_append hprefix tailTrace_3104955
  have hstable : (prefixWord ++ tailWord_3104955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104955).length < 2 ^ (prefixWord ++ tailWord_3104955).sum := by decide
  have hdescent : baseEnd_3104955 < baseStart_3104955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105002 : List Nat := [3, 1, 3, 1, 1, 2, 2, 3, 6]
def baseStart_3105002 : Nat := 118140960795 + 3105002 * 2 ^ 59
def prefixEnd_3105002 : Nat := 4983230072969 + 3 ^ 40 * 3105002 * 2
def baseEnd_3105002 : Nat := 354301879815947977576747

theorem tailTrace_3105002 : CollatzResearch.WordTrace tailWord_3105002 prefixEnd_3105002 354301879815947977576747 := by
  unfold tailWord_3105002
  simp only [CollatzResearch.WordTrace]
  refine ⟨28312181674278880241999315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75499151131410347311998173 28312181674278880241999315)
  ·
    refine ⟨42468272511418320362998973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28312181674278880241999315 42468272511418320362998973)
    ·
      refine ⟨15925602191781870136124615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42468272511418320362998973 15925602191781870136124615)
      ·
        refine ⟨23888403287672805204186923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15925602191781870136124615 23888403287672805204186923)
        ·
          refine ⟨35832604931509207806280385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23888403287672805204186923 35832604931509207806280385)
          ·
            refine ⟨26874453698631905854710289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35832604931509207806280385 26874453698631905854710289)
            ·
              refine ⟨20155840273973929391032717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26874453698631905854710289 20155840273973929391032717)
              ·
                refine ⟨7558440102740223521637269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20155840273973929391032717 7558440102740223521637269)
                ·
                  refine ⟨354301879815947977576747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7558440102740223521637269 354301879815947977576747)
                  ·
                    rfl

theorem cell22_3105002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 6].length) (baseStart_3105002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105002 prefixEnd_3105002 := by exact prefixLift 3105002
  have htrace : WordTrace (prefixWord ++ tailWord_3105002) baseStart_3105002 baseEnd_3105002 := by
    simpa [prefixWord, tailWord_3105002, baseEnd_3105002] using wordTrace_append hprefix tailTrace_3105002
  have hstable : (prefixWord ++ tailWord_3105002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105002).length < 2 ^ (prefixWord ++ tailWord_3105002).sum := by decide
  have hdescent : baseEnd_3105002 < baseStart_3105002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105047 : List Nat := [1, 1, 3, 4, 1, 3, 9]
def baseStart_3105047 : Nat := 118140960795 + 3105047 * 2 ^ 59
def prefixEnd_3105047 : Nat := 4983230072969 + 3 ^ 40 * 3105047 * 2
def baseEnd_3105047 : Nat := 39367446069165882050189

theorem tailTrace_3105047 : CollatzResearch.WordTrace tailWord_3105047 prefixEnd_3105047 39367446069165882050189 := by
  unfold tailWord_3105047
  simp only [CollatzResearch.WordTrace]
  refine ⟨113250367981952493653385395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75500245321301662435590263 113250367981952493653385395)
  ·
    refine ⟨169875551972928740480078093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113250367981952493653385395 169875551972928740480078093)
    ·
      refine ⟨63703331989848277680029285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169875551972928740480078093 63703331989848277680029285)
      ·
        refine ⟨11944374748096552065005491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63703331989848277680029285 11944374748096552065005491)
        ·
          refine ⟨17916562122144828097508237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11944374748096552065005491 17916562122144828097508237)
          ·
            refine ⟨6718710795804310536565589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17916562122144828097508237 6718710795804310536565589)
            ·
              refine ⟨39367446069165882050189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6718710795804310536565589 39367446069165882050189)
              ·
                rfl

theorem cell22_3105047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 9].length) (baseStart_3105047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105047 prefixEnd_3105047 := by exact prefixLift 3105047
  have htrace : WordTrace (prefixWord ++ tailWord_3105047) baseStart_3105047 baseEnd_3105047 := by
    simpa [prefixWord, tailWord_3105047, baseEnd_3105047] using wordTrace_append hprefix tailTrace_3105047
  have hstable : (prefixWord ++ tailWord_3105047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105047).length < 2 ^ (prefixWord ++ tailWord_3105047).sum := by decide
  have hdescent : baseEnd_3105047 < baseStart_3105047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105081 : List Nat := [1, 2, 1, 6, 1, 3, 2, 6]
def baseStart_3105081 : Nat := 118140960795 + 3105081 * 2 ^ 59
def prefixEnd_3105081 : Nat := 4983230072969 + 3 ^ 40 * 3105081 * 2
def baseEnd_3105081 : Nat := 118103631418034895556111

theorem tailTrace_3105081 : CollatzResearch.WordTrace tailWord_3105081 prefixEnd_3105081 118103631418034895556111 := by
  unfold tailWord_3105081
  simp only [CollatzResearch.WordTrace]
  refine ⟨113251608063829317460123097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75501072042552878306748731 113251608063829317460123097)
  ·
    refine ⟨84938706047871988095092323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113251608063829317460123097 84938706047871988095092323)
    ·
      refine ⟨127408059071807982142638485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84938706047871988095092323 127408059071807982142638485)
      ·
        refine ⟨5972252768990999162936179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 127408059071807982142638485 5972252768990999162936179)
        ·
          refine ⟨8958379153486498744404269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5972252768990999162936179 8958379153486498744404269)
          ·
            refine ⟨3359392182557437029151601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8958379153486498744404269 3359392182557437029151601)
            ·
              refine ⟨2519544136918077771863701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3359392182557437029151601 2519544136918077771863701)
              ·
                refine ⟨118103631418034895556111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2519544136918077771863701 118103631418034895556111)
                ·
                  rfl

theorem cell22_3105081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 6].length) (baseStart_3105081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105081 prefixEnd_3105081 := by exact prefixLift 3105081
  have htrace : WordTrace (prefixWord ++ tailWord_3105081) baseStart_3105081 baseEnd_3105081 := by
    simpa [prefixWord, tailWord_3105081, baseEnd_3105081] using wordTrace_append hprefix tailTrace_3105081
  have hstable : (prefixWord ++ tailWord_3105081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105081).length < 2 ^ (prefixWord ++ tailWord_3105081).sum := by decide
  have hdescent : baseEnd_3105081 < baseStart_3105081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105107 : List Nat := [1, 1, 1, 2, 1, 1, 4, 4, 2, 5]
def baseStart_3105107 : Nat := 118140960795 + 3105107 * 2 ^ 59
def prefixEnd_3105107 : Nat := 4983230072969 + 3 ^ 40 * 3105107 * 2
def baseEnd_3105107 : Nat := 1062941583093658658854919

theorem tailTrace_3105107 : CollatzResearch.WordTrace tailWord_3105107 prefixEnd_3105107 1062941583093658658854919 := by
  unfold tailWord_3105107
  simp only [CollatzResearch.WordTrace]
  refine ⟨113252556361735123900569575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75501704241156749267046383 113252556361735123900569575)
  ·
    refine ⟨169878834542602685850854363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113252556361735123900569575 169878834542602685850854363)
    ·
      refine ⟨254818251813904028776281545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169878834542602685850854363 254818251813904028776281545)
      ·
        refine ⟨191113688860428021582211159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254818251813904028776281545 191113688860428021582211159)
        ·
          refine ⟨286670533290642032373316739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191113688860428021582211159 286670533290642032373316739)
          ·
            refine ⟨430005799935963048559975109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286670533290642032373316739 430005799935963048559975109)
            ·
              refine ⟨80626087487993071604995333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 430005799935963048559975109 80626087487993071604995333)
              ·
                refine ⟨15117391403998700925936625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80626087487993071604995333 15117391403998700925936625)
                ·
                  refine ⟨11338043552999025694452469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15117391403998700925936625 11338043552999025694452469)
                  ·
                    refine ⟨1062941583093658658854919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11338043552999025694452469 1062941583093658658854919)
                    ·
                      rfl

theorem cell22_3105107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 5].length) (baseStart_3105107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105107 prefixEnd_3105107 := by exact prefixLift 3105107
  have htrace : WordTrace (prefixWord ++ tailWord_3105107) baseStart_3105107 baseEnd_3105107 := by
    simpa [prefixWord, tailWord_3105107, baseEnd_3105107] using wordTrace_append hprefix tailTrace_3105107
  have hstable : (prefixWord ++ tailWord_3105107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105107).length < 2 ^ (prefixWord ++ tailWord_3105107).sum := by decide
  have hdescent : baseEnd_3105107 < baseStart_3105107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105137 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 8]
def baseStart_3105137 : Nat := 118140960795 + 3105137 * 2 ^ 59
def prefixEnd_3105137 : Nat := 4983230072969 + 3 ^ 40 * 3105137 * 2
def baseEnd_3105137 : Nat := 354317284235582860201609

theorem tailTrace_3105137 : CollatzResearch.WordTrace tailWord_3105137 prefixEnd_3105137 354317284235582860201609 := by
  unfold tailWord_3105137
  simp only [CollatzResearch.WordTrace]
  refine ⟨113253650551626439024161665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75502433701084292682774443 113253650551626439024161665)
  ·
    refine ⟨84940237913719829268121249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113253650551626439024161665 84940237913719829268121249)
    ·
      refine ⟨63705178435289871951090937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84940237913719829268121249 63705178435289871951090937)
      ·
        refine ⟨47778883826467403963318203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63705178435289871951090937 47778883826467403963318203)
        ·
          refine ⟨71668325739701105944977305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47778883826467403963318203 71668325739701105944977305)
          ·
            refine ⟨53751244304775829458732979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71668325739701105944977305 53751244304775829458732979)
            ·
              refine ⟨80626866457163744188099469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53751244304775829458732979 80626866457163744188099469)
              ·
                refine ⟨30235074921436404070537301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80626866457163744188099469 30235074921436404070537301)
                ·
                  refine ⟨354317284235582860201609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30235074921436404070537301 354317284235582860201609)
                  ·
                    rfl

theorem cell22_3105137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 8].length) (baseStart_3105137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105137 prefixEnd_3105137 := by exact prefixLift 3105137
  have htrace : WordTrace (prefixWord ++ tailWord_3105137) baseStart_3105137 baseEnd_3105137 := by
    simpa [prefixWord, tailWord_3105137, baseEnd_3105137] using wordTrace_append hprefix tailTrace_3105137
  have hstable : (prefixWord ++ tailWord_3105137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105137).length < 2 ^ (prefixWord ++ tailWord_3105137).sum := by decide
  have hdescent : baseEnd_3105137 < baseStart_3105137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105186 : List Nat := [3, 3, 1, 2, 1, 1, 4, 1, 1, 5]
def baseStart_3105186 : Nat := 118140960795 + 3105186 * 2 ^ 59
def prefixEnd_3105186 : Nat := 4983230072969 + 3 ^ 40 * 3105186 * 2
def baseEnd_3105186 : Nat := 1062968626408128786129677

theorem tailTrace_3105186 : CollatzResearch.WordTrace tailWord_3105186 prefixEnd_3105186 1062968626408128786129677 := by
  unfold tailWord_3105186
  simp only [CollatzResearch.WordTrace]
  refine ⟨28313859432112230098173853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75503625152299280261796941 28313859432112230098173853)
  ·
    refine ⟨10617697287042086286815195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28313859432112230098173853 10617697287042086286815195)
    ·
      refine ⟨15926545930563129430222793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10617697287042086286815195 15926545930563129430222793)
      ·
        refine ⟨11944909447922347072667095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15926545930563129430222793 11944909447922347072667095)
        ·
          refine ⟨17917364171883520609000643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11944909447922347072667095 17917364171883520609000643)
          ·
            refine ⟨26876046257825280913500965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17917364171883520609000643 26876046257825280913500965)
            ·
              refine ⟨5039258673342240171281431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26876046257825280913500965 5039258673342240171281431)
              ·
                refine ⟨7558888010013360256922147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5039258673342240171281431 7558888010013360256922147)
                ·
                  refine ⟨11338332015020040385383221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7558888010013360256922147 11338332015020040385383221)
                  ·
                    refine ⟨1062968626408128786129677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11338332015020040385383221 1062968626408128786129677)
                    ·
                      rfl

theorem cell22_3105186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_3105186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105186 prefixEnd_3105186 := by exact prefixLift 3105186
  have htrace : WordTrace (prefixWord ++ tailWord_3105186) baseStart_3105186 baseEnd_3105186 := by
    simpa [prefixWord, tailWord_3105186, baseEnd_3105186] using wordTrace_append hprefix tailTrace_3105186
  have hstable : (prefixWord ++ tailWord_3105186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105186).length < 2 ^ (prefixWord ++ tailWord_3105186).sum := by decide
  have hdescent : baseEnd_3105186 < baseStart_3105186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105201 : List Nat := [1, 2, 2, 4, 1, 2, 3, 1, 2, 4]
def baseStart_3105201 : Nat := 118140960795 + 3105201 * 2 ^ 59
def prefixEnd_3105201 : Nat := 4983230072969 + 3 ^ 40 * 3105201 * 2
def baseEnd_3105201 : Nat := 1062973761214673747004631

theorem tailTrace_3105201 : CollatzResearch.WordTrace tailWord_3105201 prefixEnd_3105201 1062973761214673747004631 := by
  unfold tailWord_3105201
  simp only [CollatzResearch.WordTrace]
  refine ⟨113255984823394577954491457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75503989882263051969660971 113255984823394577954491457)
  ·
    refine ⟨84941988617545933465868593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113255984823394577954491457 84941988617545933465868593)
    ·
      refine ⟨63706491463159450099401445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84941988617545933465868593 63706491463159450099401445)
      ·
        refine ⟨11944967149342396893637771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63706491463159450099401445 11944967149342396893637771)
        ·
          refine ⟨17917450724013595340456657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11944967149342396893637771 17917450724013595340456657)
          ·
            refine ⟨13438088043010196505342493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17917450724013595340456657 13438088043010196505342493)
            ·
              refine ⟨5039283016128823689503435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13438088043010196505342493 5039283016128823689503435)
              ·
                refine ⟨7558924524193235534255153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5039283016128823689503435 7558924524193235534255153)
                ·
                  refine ⟨5669193393144926650691365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7558924524193235534255153 5669193393144926650691365)
                  ·
                    refine ⟨1062973761214673747004631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5669193393144926650691365 1062973761214673747004631)
                    ·
                      rfl

theorem cell22_3105201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_3105201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105201 prefixEnd_3105201 := by exact prefixLift 3105201
  have htrace : WordTrace (prefixWord ++ tailWord_3105201) baseStart_3105201 baseEnd_3105201 := by
    simpa [prefixWord, tailWord_3105201, baseEnd_3105201] using wordTrace_append hprefix tailTrace_3105201
  have hstable : (prefixWord ++ tailWord_3105201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105201).length < 2 ^ (prefixWord ++ tailWord_3105201).sum := by decide
  have hdescent : baseEnd_3105201 < baseStart_3105201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105261 : List Nat := [1, 5, 1, 3, 1, 1, 1, 2, 7]
def baseStart_3105261 : Nat := 118140960795 + 3105261 * 2 ^ 59
def prefixEnd_3105261 : Nat := 4983230072969 + 3 ^ 40 * 3105261 * 2
def baseEnd_3105261 : Nat := 354331433480284530168149

theorem tailTrace_3105261 : CollatzResearch.WordTrace tailWord_3105261 prefixEnd_3105261 354331433480284530168149 := by
  unfold tailWord_3105261
  simp only [CollatzResearch.WordTrace]
  refine ⟨113258173203177208201675637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75505448802118138801117091 113258173203177208201675637)
  ·
    refine ⟨10617953737797863268907091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113258173203177208201675637 10617953737797863268907091)
    ·
      refine ⟨15926930606696794903360637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10617953737797863268907091 15926930606696794903360637)
      ·
        refine ⟨5972598977511298088760239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15926930606696794903360637 5972598977511298088760239)
        ·
          refine ⟨8958898466266947133140359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5972598977511298088760239 8958898466266947133140359)
          ·
            refine ⟨13438347699400420699710539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8958898466266947133140359 13438347699400420699710539)
            ·
              refine ⟨20157521549100631049565809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13438347699400420699710539 20157521549100631049565809)
              ·
                refine ⟨15118141161825473287174357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20157521549100631049565809 15118141161825473287174357)
                ·
                  refine ⟨354331433480284530168149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15118141161825473287174357 354331433480284530168149)
                  ·
                    rfl

theorem cell22_3105261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_3105261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105261 prefixEnd_3105261 := by exact prefixLift 3105261
  have htrace : WordTrace (prefixWord ++ tailWord_3105261) baseStart_3105261 baseEnd_3105261 := by
    simpa [prefixWord, tailWord_3105261, baseEnd_3105261] using wordTrace_append hprefix tailTrace_3105261
  have hstable : (prefixWord ++ tailWord_3105261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105261).length < 2 ^ (prefixWord ++ tailWord_3105261).sum := by decide
  have hdescent : baseEnd_3105261 < baseStart_3105261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105282 : List Nat := [3, 4, 1, 2, 2, 2, 1, 1, 3, 3]
def baseStart_3105282 : Nat := 118140960795 + 3105282 * 2 ^ 59
def prefixEnd_3105282 : Nat := 4983230072969 + 3 ^ 40 * 3105282 * 2
def baseEnd_3105282 : Nat := 1063001489170016535729383

theorem tailTrace_3105282 : CollatzResearch.WordTrace tailWord_3105282 prefixEnd_3105282 1063001489170016535729383 := by
  unfold tailWord_3105282
  simp only [CollatzResearch.WordTrace]
  refine ⟨28314734784025282197047525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75505959424067419192126733 28314734784025282197047525)
  ·
    refine ⟨5309012772004740411946411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28314734784025282197047525 5309012772004740411946411)
    ·
      refine ⟨7963519158007110617919617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5309012772004740411946411 7963519158007110617919617)
      ·
        refine ⟨5972639368505332963439713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7963519158007110617919617 5972639368505332963439713)
        ·
          refine ⟨4479479526378999722579785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5972639368505332963439713 4479479526378999722579785)
          ·
            refine ⟨3359609644784249791934839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4479479526378999722579785 3359609644784249791934839)
            ·
              refine ⟨5039414467176374687902259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3359609644784249791934839 5039414467176374687902259)
              ·
                refine ⟨7559121700764562031853389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5039414467176374687902259 7559121700764562031853389)
                ·
                  refine ⟨2834670637786710761945021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7559121700764562031853389 2834670637786710761945021)
                  ·
                    refine ⟨1063001489170016535729383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2834670637786710761945021 1063001489170016535729383)
                    ·
                      rfl

theorem cell22_3105282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_3105282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105282 prefixEnd_3105282 := by exact prefixLift 3105282
  have htrace : WordTrace (prefixWord ++ tailWord_3105282) baseStart_3105282 baseEnd_3105282 := by
    simpa [prefixWord, tailWord_3105282, baseEnd_3105282] using wordTrace_append hprefix tailTrace_3105282
  have hstable : (prefixWord ++ tailWord_3105282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105282).length < 2 ^ (prefixWord ++ tailWord_3105282).sum := by decide
  have hdescent : baseEnd_3105282 < baseStart_3105282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105289 : List Nat := [1, 2, 1, 1, 3, 1, 2, 5, 6]
def baseStart_3105289 : Nat := 118140960795 + 3105289 * 2 ^ 59
def prefixEnd_3105289 : Nat := 4983230072969 + 3 ^ 40 * 3105289 * 2
def baseEnd_3105289 : Nat := 354334628471023616934787

theorem tailTrace_3105289 : CollatzResearch.WordTrace tailWord_3105289 prefixEnd_3105289 354334628471023616934787 := by
  unfold tailWord_3105289
  simp only [CollatzResearch.WordTrace]
  refine ⟨113259194447075768983694921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75506129631383845989129947 113259194447075768983694921)
  ·
    refine ⟨84944395835306826737771191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113259194447075768983694921 84944395835306826737771191)
    ·
      refine ⟨127416593752960240106656787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84944395835306826737771191 127416593752960240106656787)
      ·
        refine ⟨191124890629440360159985181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127416593752960240106656787 191124890629440360159985181)
        ·
          refine ⟨71671833986040135059994443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191124890629440360159985181 71671833986040135059994443)
          ·
            refine ⟨107507750979060202589991665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71671833986040135059994443 107507750979060202589991665)
            ·
              refine ⟨80630813234295151942493749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107507750979060202589991665 80630813234295151942493749)
              ·
                refine ⟨7559138740715170494608789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80630813234295151942493749 7559138740715170494608789)
                ·
                  refine ⟨354334628471023616934787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7559138740715170494608789 354334628471023616934787)
                  ·
                    rfl

theorem cell22_3105289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 6].length) (baseStart_3105289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105289 prefixEnd_3105289 := by exact prefixLift 3105289
  have htrace : WordTrace (prefixWord ++ tailWord_3105289) baseStart_3105289 baseEnd_3105289 := by
    simpa [prefixWord, tailWord_3105289, baseEnd_3105289] using wordTrace_append hprefix tailTrace_3105289
  have hstable : (prefixWord ++ tailWord_3105289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105289).length < 2 ^ (prefixWord ++ tailWord_3105289).sum := by decide
  have hdescent : baseEnd_3105289 < baseStart_3105289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105308 : List Nat := [2, 2, 3, 1, 2, 2, 3, 2, 1, 4]
def baseStart_3105308 : Nat := 118140960795 + 3105308 * 2 ^ 59
def prefixEnd_3105308 : Nat := 4983230072969 + 3 ^ 40 * 3105308 * 2
def baseEnd_3105308 : Nat := 1063010389501361134579303

theorem tailTrace_3105308 : CollatzResearch.WordTrace tailWord_3105308 prefixEnd_3105308 1063010389501361134579303 := by
  unfold tailWord_3105308
  simp only [CollatzResearch.WordTrace]
  refine ⟨56629943717003467614318289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75506591622671290152424385 56629943717003467614318289)
  ·
    refine ⟨42472457787752600710738717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56629943717003467614318289 42472457787752600710738717)
    ·
      refine ⟨15927171670407225266527019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42472457787752600710738717 15927171670407225266527019)
      ·
        refine ⟨23890757505610837899790529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15927171670407225266527019 23890757505610837899790529)
        ·
          refine ⟨17918068129208128424842897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23890757505610837899790529 17918068129208128424842897)
          ·
            refine ⟨13438551096906096318632173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17918068129208128424842897 13438551096906096318632173)
            ·
              refine ⟨5039456661339786119487065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13438551096906096318632173 5039456661339786119487065)
              ·
                refine ⟨3779592496004839589615299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5039456661339786119487065 3779592496004839589615299)
                ·
                  refine ⟨5669388744007259384422949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3779592496004839589615299 5669388744007259384422949)
                  ·
                    refine ⟨1063010389501361134579303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5669388744007259384422949 1063010389501361134579303)
                    ·
                      rfl

theorem cell22_3105308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_3105308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105308 prefixEnd_3105308 := by exact prefixLift 3105308
  have htrace : WordTrace (prefixWord ++ tailWord_3105308) baseStart_3105308 baseEnd_3105308 := by
    simpa [prefixWord, tailWord_3105308, baseEnd_3105308] using wordTrace_append hprefix tailTrace_3105308
  have hstable : (prefixWord ++ tailWord_3105308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105308).length < 2 ^ (prefixWord ++ tailWord_3105308).sum := by decide
  have hdescent : baseEnd_3105308 < baseStart_3105308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105336 : List Nat := [2, 1, 2, 1, 4, 1, 1, 4, 2, 4]
def baseStart_3105336 : Nat := 118140960795 + 3105336 * 2 ^ 59
def prefixEnd_3105336 : Nat := 4983230072969 + 3 ^ 40 * 3105336 * 2
def baseEnd_3105336 : Nat := 1063019974473578394879217

theorem tailTrace_3105336 : CollatzResearch.WordTrace tailWord_3105336 prefixEnd_3105336 1063019974473578394879217 := by
  unfold tailWord_3105336
  simp only [CollatzResearch.WordTrace]
  refine ⟨56630454338952748005327931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75507272451936997340437241 56630454338952748005327931)
  ·
    refine ⟨84945681508429122007991897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56630454338952748005327931 84945681508429122007991897)
    ·
      refine ⟨63709261131321841505993923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84945681508429122007991897 63709261131321841505993923)
      ·
        refine ⟨95563891696982762258990885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63709261131321841505993923 95563891696982762258990885)
        ·
          refine ⟨17918229693184267923560791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95563891696982762258990885 17918229693184267923560791)
          ·
            refine ⟨26877344539776401885341187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17918229693184267923560791 26877344539776401885341187)
            ·
              refine ⟨40316016809664602828011781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26877344539776401885341187 40316016809664602828011781)
              ·
                refine ⟨7559253151812113030252209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40316016809664602828011781 7559253151812113030252209)
                ·
                  refine ⟨5669439863859084772689157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7559253151812113030252209 5669439863859084772689157)
                  ·
                    refine ⟨1063019974473578394879217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5669439863859084772689157 1063019974473578394879217)
                    ·
                      rfl

theorem cell22_3105336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_3105336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105336 prefixEnd_3105336 := by exact prefixLift 3105336
  have htrace : WordTrace (prefixWord ++ tailWord_3105336) baseStart_3105336 baseEnd_3105336 := by
    simpa [prefixWord, tailWord_3105336, baseEnd_3105336] using wordTrace_append hprefix tailTrace_3105336
  have hstable : (prefixWord ++ tailWord_3105336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105336).length < 2 ^ (prefixWord ++ tailWord_3105336).sum := by decide
  have hdescent : baseEnd_3105336 < baseStart_3105336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105338 : List Nat := [3, 1, 1, 1, 3, 3, 1, 4, 2, 3]
def baseStart_3105338 : Nat := 118140960795 + 3105338 * 2 ^ 59
def prefixEnd_3105338 : Nat := 4983230072969 + 3 ^ 40 * 3105338 * 2
def baseEnd_3105338 : Nat := 1063020659114451056329211

theorem tailTrace_3105338 : CollatzResearch.WordTrace tailWord_3105338 prefixEnd_3105338 1063020659114451056329211 := by
  unfold tailWord_3105338
  simp only [CollatzResearch.WordTrace]
  refine ⟨28315245405974562588057167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75507321082598833568152445 28315245405974562588057167)
  ·
    refine ⟨42472868108961843882085751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28315245405974562588057167 42472868108961843882085751)
    ·
      refine ⟨63709302163442765823128627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42472868108961843882085751 63709302163442765823128627)
      ·
        refine ⟨95563953245164148734692941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63709302163442765823128627 95563953245164148734692941)
        ·
          refine ⟨35836482466936555775509853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95563953245164148734692941 35836482466936555775509853)
          ·
            refine ⟨13438680925101208415816195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35836482466936555775509853 13438680925101208415816195)
            ·
              refine ⟨20158021387651812623724293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13438680925101208415816195 20158021387651812623724293)
              ·
                refine ⟨3779629010184714866948305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20158021387651812623724293 3779629010184714866948305)
                ·
                  refine ⟨2834721757638536150211229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3779629010184714866948305 2834721757638536150211229)
                  ·
                    refine ⟨1063020659114451056329211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2834721757638536150211229 1063020659114451056329211)
                    ·
                      rfl

theorem cell22_3105338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 2, 3].length) (baseStart_3105338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105338 prefixEnd_3105338 := by exact prefixLift 3105338
  have htrace : WordTrace (prefixWord ++ tailWord_3105338) baseStart_3105338 baseEnd_3105338 := by
    simpa [prefixWord, tailWord_3105338, baseEnd_3105338] using wordTrace_append hprefix tailTrace_3105338
  have hstable : (prefixWord ++ tailWord_3105338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105338).length < 2 ^ (prefixWord ++ tailWord_3105338).sum := by decide
  have hdescent : baseEnd_3105338 < baseStart_3105338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105340 : List Nat := [2, 2, 2, 2, 3, 1, 4, 2, 4]
def baseStart_3105340 : Nat := 118140960795 + 3105340 * 2 ^ 59
def prefixEnd_3105340 : Nat := 4983230072969 + 3 ^ 40 * 3105340 * 2
def baseEnd_3105340 : Nat := 354340447918441239259735

theorem tailTrace_3105340 : CollatzResearch.WordTrace tailWord_3105340 prefixEnd_3105340 354340447918441239259735 := by
  unfold tailWord_3105340
  simp only [CollatzResearch.WordTrace]
  refine ⟨56630527284945502346900737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75507369713260669795867649 56630527284945502346900737)
  ·
    refine ⟨42472895463709126760175553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56630527284945502346900737 42472895463709126760175553)
    ·
      refine ⟨31854671597781845070131665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42472895463709126760175553 31854671597781845070131665)
      ·
        refine ⟨23891003698336383802598749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31854671597781845070131665 23891003698336383802598749)
        ·
          refine ⟨8959126386876143925974531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23891003698336383802598749 8959126386876143925974531)
          ·
            refine ⟨13438689580314215888961797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8959126386876143925974531 13438689580314215888961797)
            ·
              refine ⟨2519754296308915479180337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13438689580314215888961797 2519754296308915479180337)
              ·
                refine ⟨1889815722231686609385253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2519754296308915479180337 1889815722231686609385253)
                ·
                  refine ⟨354340447918441239259735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1889815722231686609385253 354340447918441239259735)
                  ·
                    rfl

theorem cell22_3105340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 2, 4].length) (baseStart_3105340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105340 prefixEnd_3105340 := by exact prefixLift 3105340
  have htrace : WordTrace (prefixWord ++ tailWord_3105340) baseStart_3105340 baseEnd_3105340 := by
    simpa [prefixWord, tailWord_3105340, baseEnd_3105340] using wordTrace_append hprefix tailTrace_3105340
  have hstable : (prefixWord ++ tailWord_3105340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105340).length < 2 ^ (prefixWord ++ tailWord_3105340).sum := by decide
  have hdescent : baseEnd_3105340 < baseStart_3105340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105351 : List Nat := [1, 1, 4, 1, 4, 1, 3, 7]
def baseStart_3105351 : Nat := 118140960795 + 3105351 * 2 ^ 59
def prefixEnd_3105351 : Nat := 4983230072969 + 3 ^ 40 * 3105351 * 2
def baseEnd_3105351 : Nat := 118113901031124817306019

theorem tailTrace_3105351 : CollatzResearch.WordTrace tailWord_3105351 prefixEnd_3105351 118113901031124817306019 := by
  unfold tailWord_3105351
  simp only [CollatzResearch.WordTrace]
  refine ⟨113261455772851153572451907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75507637181900769048301271 113261455772851153572451907)
  ·
    refine ⟨169892183659276730358677861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113261455772851153572451907 169892183659276730358677861)
    ·
      refine ⟨31854784436114386942252099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169892183659276730358677861 31854784436114386942252099)
      ·
        refine ⟨47782176654171580413378149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31854784436114386942252099 47782176654171580413378149)
        ·
          refine ⟨8959158122657171327508403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47782176654171580413378149 8959158122657171327508403)
          ·
            refine ⟨13438737183985756991262605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8959158122657171327508403 13438737183985756991262605)
            ·
              refine ⟨5039526443994658871723477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13438737183985756991262605 5039526443994658871723477)
              ·
                refine ⟨118113901031124817306019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5039526443994658871723477 118113901031124817306019)
                ·
                  rfl

theorem cell22_3105351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 7].length) (baseStart_3105351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105351 prefixEnd_3105351 := by exact prefixLift 3105351
  have htrace : WordTrace (prefixWord ++ tailWord_3105351) baseStart_3105351 baseEnd_3105351 := by
    simpa [prefixWord, tailWord_3105351, baseEnd_3105351] using wordTrace_append hprefix tailTrace_3105351
  have hstable : (prefixWord ++ tailWord_3105351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105351).length < 2 ^ (prefixWord ++ tailWord_3105351).sum := by decide
  have hdescent : baseEnd_3105351 < baseStart_3105351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105411 : List Nat := [1, 1, 1, 3, 3, 1, 4, 1, 2, 5]
def baseStart_3105411 : Nat := 118140960795 + 3105411 * 2 ^ 59
def prefixEnd_3105411 : Nat := 4983230072969 + 3 ^ 40 * 3105411 * 2
def baseEnd_3105411 : Nat := 1063045648506303199253987

theorem tailTrace_3105411 : CollatzResearch.WordTrace tailWord_3105411 prefixEnd_3105411 1063045648506303199253987 := by
  unfold tailWord_3105411
  simp only [CollatzResearch.WordTrace]
  refine ⟨113263644152633783819636087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75509096101755855879757391 113263644152633783819636087)
  ·
    refine ⟨169895466228950675729454131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113263644152633783819636087 169895466228950675729454131)
    ·
      refine ⟨254843199343426013594181197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169895466228950675729454131 254843199343426013594181197)
      ·
        refine ⟨95566199753784755097817949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254843199343426013594181197 95566199753784755097817949)
        ·
          refine ⟨35837324907669283161681731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95566199753784755097817949 35837324907669283161681731)
          ·
            refine ⟨53755987361503924742522597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35837324907669283161681731 53755987361503924742522597)
            ·
              refine ⟨10079247630281985889222987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53755987361503924742522597 10079247630281985889222987)
              ·
                refine ⟨15118871445422978833834481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10079247630281985889222987 15118871445422978833834481)
                ·
                  refine ⟨11339153584067234125375861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15118871445422978833834481 11339153584067234125375861)
                  ·
                    refine ⟨1063045648506303199253987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11339153584067234125375861 1063045648506303199253987)
                    ·
                      rfl

theorem cell22_3105411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 5].length) (baseStart_3105411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105411 prefixEnd_3105411 := by exact prefixLift 3105411
  have htrace : WordTrace (prefixWord ++ tailWord_3105411) baseStart_3105411 baseEnd_3105411 := by
    simpa [prefixWord, tailWord_3105411, baseEnd_3105411] using wordTrace_append hprefix tailTrace_3105411
  have hstable : (prefixWord ++ tailWord_3105411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105411).length < 2 ^ (prefixWord ++ tailWord_3105411).sum := by decide
  have hdescent : baseEnd_3105411 < baseStart_3105411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105490 : List Nat := [3, 2, 2, 2, 3, 1, 1, 2, 1, 5]
def baseStart_3105490 : Nat := 118140960795 + 3105490 * 2 ^ 59
def prefixEnd_3105490 : Nat := 4983230072969 + 3 ^ 40 * 3105490 * 2
def baseEnd_3105490 : Nat := 1063072691820773326528745

theorem tailTrace_3105490 : CollatzResearch.WordTrace tailWord_3105490 prefixEnd_3105490 1063072691820773326528745 := by
  unfold tailWord_3105490
  simp only [CollatzResearch.WordTrace]
  refine ⟨28316631379836895077940481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75511017012898386874507949 28316631379836895077940481)
  ·
    refine ⟨21237473534877671308455361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28316631379836895077940481 21237473534877671308455361)
    ·
      refine ⟨15928105151158253481341521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21237473534877671308455361 15928105151158253481341521)
      ·
        refine ⟨11946078863368690111006141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15928105151158253481341521 11946078863368690111006141)
        ·
          refine ⟨4479779573763258791627303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11946078863368690111006141 4479779573763258791627303)
          ·
            refine ⟨6719669360644888187440955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4479779573763258791627303 6719669360644888187440955)
            ·
              refine ⟨10079504040967332281161433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6719669360644888187440955 10079504040967332281161433)
              ·
                refine ⟨7559628030725499210871075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10079504040967332281161433 7559628030725499210871075)
                ·
                  refine ⟨11339442046088248816306613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7559628030725499210871075 11339442046088248816306613)
                  ·
                    refine ⟨1063072691820773326528745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11339442046088248816306613 1063072691820773326528745)
                    ·
                      rfl

theorem cell22_3105490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_3105490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105490 prefixEnd_3105490 := by exact prefixLift 3105490
  have htrace : WordTrace (prefixWord ++ tailWord_3105490) baseStart_3105490 baseEnd_3105490 := by
    simpa [prefixWord, tailWord_3105490, baseEnd_3105490] using wordTrace_append hprefix tailTrace_3105490
  have hstable : (prefixWord ++ tailWord_3105490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105490).length < 2 ^ (prefixWord ++ tailWord_3105490).sum := by decide
  have hdescent : baseEnd_3105490 < baseStart_3105490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105507 : List Nat := [1, 1, 1, 7, 1, 2, 2, 2, 2, 3]
def baseStart_3105507 : Nat := 118140960795 + 3105507 * 2 ^ 59
def prefixEnd_3105507 : Nat := 4983230072969 + 3 ^ 40 * 3105507 * 2
def baseEnd_3105507 : Nat := 1063078511268190948853693

theorem tailTrace_3105507 : CollatzResearch.WordTrace tailWord_3105507 prefixEnd_3105507 1063078511268190948853693 := by
  unfold tailWord_3105507
  simp only [CollatzResearch.WordTrace]
  refine ⟨113267145560285992215130775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75511430373523994810087183 113267145560285992215130775)
  ·
    refine ⟨169900718340428988322696163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113267145560285992215130775 169900718340428988322696163)
    ·
      refine ⟨254851077510643482484044245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169900718340428988322696163 254851077510643482484044245)
      ·
        refine ⟨5973072129155706620719787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 254851077510643482484044245 5973072129155706620719787)
        ·
          refine ⟨8959608193733559931079681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5973072129155706620719787 8959608193733559931079681)
          ·
            refine ⟨6719706145300169948309761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8959608193733559931079681 6719706145300169948309761)
            ·
              refine ⟨5039779608975127461232321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6719706145300169948309761 5039779608975127461232321)
              ·
                refine ⟨3779834706731345595924241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5039779608975127461232321 3779834706731345595924241)
                ·
                  refine ⟨2834876030048509196943181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3779834706731345595924241 2834876030048509196943181)
                  ·
                    refine ⟨1063078511268190948853693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2834876030048509196943181 1063078511268190948853693)
                    ·
                      rfl

theorem cell22_3105507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 2, 3].length) (baseStart_3105507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105507 prefixEnd_3105507 := by exact prefixLift 3105507
  have htrace : WordTrace (prefixWord ++ tailWord_3105507) baseStart_3105507 baseEnd_3105507 := by
    simpa [prefixWord, tailWord_3105507, baseEnd_3105507] using wordTrace_append hprefix tailTrace_3105507
  have hstable : (prefixWord ++ tailWord_3105507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105507).length < 2 ^ (prefixWord ++ tailWord_3105507).sum := by decide
  have hdescent : baseEnd_3105507 < baseStart_3105507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105524 : List Nat := [2, 6, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_3105524 : Nat := 118140960795 + 3105524 * 2 ^ 59
def prefixEnd_3105524 : Nat := 4983230072969 + 3 ^ 40 * 3105524 * 2
def baseEnd_3105524 : Nat := 1063084330715608571178641

theorem tailTrace_3105524 : CollatzResearch.WordTrace tailWord_3105524 prefixEnd_3105524 1063084330715608571178641 := by
  unfold tailWord_3105524
  simp only [CollatzResearch.WordTrace]
  refine ⟨56633882800612202059249813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75511843734149602745666417 56633882800612202059249813)
  ·
    refine ⟨2654713256278696971527335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 56633882800612202059249813 2654713256278696971527335)
    ·
      refine ⟨3982069884418045457291003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2654713256278696971527335 3982069884418045457291003)
      ·
        refine ⟨5973104826627068185936505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3982069884418045457291003 5973104826627068185936505)
        ·
          refine ⟨4479828619970301139452379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5973104826627068185936505 4479828619970301139452379)
          ·
            refine ⟨6719742929955451709178569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4479828619970301139452379 6719742929955451709178569)
            ·
              refine ⟨5039807197466588781883927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6719742929955451709178569 5039807197466588781883927)
              ·
                refine ⟨7559710796199883172825891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5039807197466588781883927 7559710796199883172825891)
                ·
                  refine ⟨11339566194299824759238837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7559710796199883172825891 11339566194299824759238837)
                  ·
                    refine ⟨1063084330715608571178641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11339566194299824759238837 1063084330715608571178641)
                    ·
                      rfl

theorem cell22_3105524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_3105524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105524 prefixEnd_3105524 := by exact prefixLift 3105524
  have htrace : WordTrace (prefixWord ++ tailWord_3105524) baseStart_3105524 baseEnd_3105524 := by
    simpa [prefixWord, tailWord_3105524, baseEnd_3105524] using wordTrace_append hprefix tailTrace_3105524
  have hstable : (prefixWord ++ tailWord_3105524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105524).length < 2 ^ (prefixWord ++ tailWord_3105524).sum := by decide
  have hdescent : baseEnd_3105524 < baseStart_3105524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105608 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 3, 5]
def baseStart_3105608 : Nat := 118140960795 + 3105608 * 2 ^ 59
def prefixEnd_3105608 : Nat := 4983230072969 + 3 ^ 40 * 3105608 * 2
def baseEnd_3105608 : Nat := 1063113085632260352078383

theorem tailTrace_3105608 : CollatzResearch.WordTrace tailWord_3105608 prefixEnd_3105608 1063113085632260352078383 := by
  unfold tailWord_3105608
  simp only [CollatzResearch.WordTrace]
  refine ⟨56635414666460043232278739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75513886221946724309704985 56635414666460043232278739)
  ·
    refine ⟨84953121999690064848418109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56635414666460043232278739 84953121999690064848418109)
    ·
      refine ⟨31857420749883774318156791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84953121999690064848418109 31857420749883774318156791)
      ·
        refine ⟨47786131124825661477235187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31857420749883774318156791 47786131124825661477235187)
        ·
          refine ⟨71679196687238492215852781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47786131124825661477235187 71679196687238492215852781)
          ·
            refine ⟨26879698757714434580944793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71679196687238492215852781 26879698757714434580944793)
            ·
              refine ⟨20159774068285825935708595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26879698757714434580944793 20159774068285825935708595)
              ·
                refine ⟨30239661102428738903562893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20159774068285825935708595 30239661102428738903562893)
                ·
                  refine ⟨11339872913410777088836085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30239661102428738903562893 11339872913410777088836085)
                  ·
                    refine ⟨1063113085632260352078383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11339872913410777088836085 1063113085632260352078383)
                    ·
                      rfl

theorem cell22_3105608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_3105608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105608 prefixEnd_3105608 := by exact prefixLift 3105608
  have htrace : WordTrace (prefixWord ++ tailWord_3105608) baseStart_3105608 baseEnd_3105608 := by
    simpa [prefixWord, tailWord_3105608, baseEnd_3105608] using wordTrace_append hprefix tailTrace_3105608
  have hstable : (prefixWord ++ tailWord_3105608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105608).length < 2 ^ (prefixWord ++ tailWord_3105608).sum := by decide
  have hdescent : baseEnd_3105608 < baseStart_3105608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105610 : List Nat := [3, 1, 2, 1, 1, 1, 2, 7, 4]
def baseStart_3105610 : Nat := 118140960795 + 3105610 * 2 ^ 59
def prefixEnd_3105610 : Nat := 4983230072969 + 3 ^ 40 * 3105610 * 2
def baseEnd_3105610 : Nat := 354371256757711004509459

theorem tailTrace_3105610 : CollatzResearch.WordTrace tailWord_3105610 prefixEnd_3105610 354371256757711004509459 := by
  unfold tailWord_3105610
  simp only [CollatzResearch.WordTrace]
  refine ⟨28317725569728210201532571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75513934852608560537420189 28317725569728210201532571)
  ·
    refine ⟨42476588354592315302298857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28317725569728210201532571 42476588354592315302298857)
    ·
      refine ⟨31857441265944236476724143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42476588354592315302298857 31857441265944236476724143)
      ·
        refine ⟨47786161898916354715086215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31857441265944236476724143 47786161898916354715086215)
        ·
          refine ⟨71679242848374532072629323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47786161898916354715086215 71679242848374532072629323)
          ·
            refine ⟨107518864272561798108943985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71679242848374532072629323 107518864272561798108943985)
            ·
              refine ⟨80639148204421348581707989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107518864272561798108943985 80639148204421348581707989)
              ·
                refine ⟨1889980036041125357383781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 80639148204421348581707989 1889980036041125357383781)
                ·
                  refine ⟨354371256757711004509459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1889980036041125357383781 354371256757711004509459)
                  ·
                    rfl

theorem cell22_3105610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 7, 4].length) (baseStart_3105610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105610 prefixEnd_3105610 := by exact prefixLift 3105610
  have htrace : WordTrace (prefixWord ++ tailWord_3105610) baseStart_3105610 baseEnd_3105610 := by
    simpa [prefixWord, tailWord_3105610, baseEnd_3105610] using wordTrace_append hprefix tailTrace_3105610
  have hstable : (prefixWord ++ tailWord_3105610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105610).length < 2 ^ (prefixWord ++ tailWord_3105610).sum := by decide
  have hdescent : baseEnd_3105610 < baseStart_3105610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105625 : List Nat := [1, 2, 1, 2, 2, 4, 2, 1, 4, 3]
def baseStart_3105625 : Nat := 118140960795 + 3105625 * 2 ^ 59
def prefixEnd_3105625 : Nat := 4983230072969 + 3 ^ 40 * 3105625 * 2
def baseEnd_3105625 : Nat := 1063118905079677974403331

theorem tailTrace_3105625 : CollatzResearch.WordTrace tailWord_3105625 prefixEnd_3105625 1063118905079677974403331 := by
  unfold tailWord_3105625
  simp only [CollatzResearch.WordTrace]
  refine ⟨113271449373858498367926329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75514299582572332245284219 113271449373858498367926329)
  ·
    refine ⟨84953587030393873775944747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113271449373858498367926329 84953587030393873775944747)
    ·
      refine ⟨127430380545590810663917121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84953587030393873775944747 127430380545590810663917121)
      ·
        refine ⟨95572785409193107997937841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127430380545590810663917121 95572785409193107997937841)
        ·
          refine ⟨71679589056894830998453381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95572785409193107997937841 71679589056894830998453381)
          ·
            refine ⟨13439922948167780812210009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71679589056894830998453381 13439922948167780812210009)
            ·
              refine ⟨10079942211125835609157507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13439922948167780812210009 10079942211125835609157507)
              ·
                refine ⟨15119913316688753413736261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10079942211125835609157507 15119913316688753413736261)
                ·
                  refine ⟨2834983746879141265075549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15119913316688753413736261 2834983746879141265075549)
                  ·
                    refine ⟨1063118905079677974403331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2834983746879141265075549 1063118905079677974403331)
                    ·
                      rfl

theorem cell22_3105625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 4, 3].length) (baseStart_3105625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105625 prefixEnd_3105625 := by exact prefixLift 3105625
  have htrace : WordTrace (prefixWord ++ tailWord_3105625) baseStart_3105625 baseEnd_3105625 := by
    simpa [prefixWord, tailWord_3105625, baseEnd_3105625] using wordTrace_append hprefix tailTrace_3105625
  have hstable : (prefixWord ++ tailWord_3105625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105625).length < 2 ^ (prefixWord ++ tailWord_3105625).sum := by decide
  have hdescent : baseEnd_3105625 < baseStart_3105625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105646 : List Nat := [4, 1, 2, 3, 3, 1, 1, 2, 1, 4]
def baseStart_3105646 : Nat := 118140960795 + 3105646 * 2 ^ 59
def prefixEnd_3105646 : Nat := 4983230072969 + 3 ^ 40 * 3105646 * 2
def baseEnd_3105646 : Nat := 1063126093808840919628267

theorem tailTrace_3105646 : CollatzResearch.WordTrace tailWord_3105646 prefixEnd_3105646 1063126093808840919628267 := by
  unfold tailWord_3105646
  simp only [CollatzResearch.WordTrace]
  refine ⟨14159026913347802369305099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75514810204521612636293861 14159026913347802369305099)
  ·
    refine ⟨21238540370021703553957649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14159026913347802369305099 21238540370021703553957649)
    ·
      refine ⟨15928905277516277665468237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21238540370021703553957649 15928905277516277665468237)
      ·
        refine ⟨5973339479068604124550589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15928905277516277665468237 5973339479068604124550589)
        ·
          refine ⟨2240002304650726546706471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5973339479068604124550589 2240002304650726546706471)
          ·
            refine ⟨3360003456976089820059707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2240002304650726546706471 3360003456976089820059707)
            ·
              refine ⟨5040005185464134730089561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3360003456976089820059707 5040005185464134730089561)
              ·
                refine ⟨3780003889098101047567171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5040005185464134730089561 3780003889098101047567171)
                ·
                  refine ⟨5670005833647151571350757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3780003889098101047567171 5670005833647151571350757)
                  ·
                    refine ⟨1063126093808840919628267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5670005833647151571350757 1063126093808840919628267)
                    ·
                      rfl

theorem cell22_3105646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_3105646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105646 prefixEnd_3105646 := by exact prefixLift 3105646
  have htrace : WordTrace (prefixWord ++ tailWord_3105646) baseStart_3105646 baseEnd_3105646 := by
    simpa [prefixWord, tailWord_3105646, baseEnd_3105646] using wordTrace_append hprefix tailTrace_3105646
  have hstable : (prefixWord ++ tailWord_3105646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105646).length < 2 ^ (prefixWord ++ tailWord_3105646).sum := by decide
  have hdescent : baseEnd_3105646 < baseStart_3105646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105700 : List Nat := [2, 3, 1, 2, 1, 2, 1, 5, 5]
def baseStart_3105700 : Nat := 118140960795 + 3105700 * 2 ^ 59
def prefixEnd_3105700 : Nat := 4983230072969 + 3 ^ 40 * 3105700 * 2
def baseEnd_3105700 : Nat := 354381526370800926259367

theorem tailTrace_3105700 : CollatzResearch.WordTrace tailWord_3105700 prefixEnd_3105700 354381526370800926259367 := by
  unfold tailWord_3105700
  simp only [CollatzResearch.WordTrace]
  refine ⟨56637092424293393088453277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75516123232391190784604369 56637092424293393088453277)
  ·
    refine ⟨21238909659110022408169979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56637092424293393088453277 21238909659110022408169979)
    ·
      refine ⟨31858364488665033612254969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21238909659110022408169979 31858364488665033612254969)
      ·
        refine ⟨23893773366498775209191227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31858364488665033612254969 23893773366498775209191227)
        ·
          refine ⟨35840660049748162813786841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23893773366498775209191227 35840660049748162813786841)
          ·
            refine ⟨26880495037311122110340131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35840660049748162813786841 26880495037311122110340131)
            ·
              refine ⟨40320742555966683165510197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26880495037311122110340131 40320742555966683165510197)
              ·
                refine ⟨3780069614621876546766581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40320742555966683165510197 3780069614621876546766581)
                ·
                  refine ⟨354381526370800926259367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3780069614621876546766581 354381526370800926259367)
                  ·
                    rfl

theorem cell22_3105700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_3105700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105700 prefixEnd_3105700 := by exact prefixLift 3105700
  have htrace : WordTrace (prefixWord ++ tailWord_3105700) baseStart_3105700 baseEnd_3105700 := by
    simpa [prefixWord, tailWord_3105700, baseEnd_3105700] using wordTrace_append hprefix tailTrace_3105700
  have hstable : (prefixWord ++ tailWord_3105700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105700).length < 2 ^ (prefixWord ++ tailWord_3105700).sum := by decide
  have hdescent : baseEnd_3105700 < baseStart_3105700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105745 : List Nat := [1, 2, 2, 1, 2, 1, 6, 1, 6]
def baseStart_3105745 : Nat := 118140960795 + 3105745 * 2 ^ 59
def prefixEnd_3105745 : Nat := 4983230072969 + 3 ^ 40 * 3105745 * 2
def baseEnd_3105745 : Nat := 354386661177345887134321

theorem tailTrace_3105745 : CollatzResearch.WordTrace tailWord_3105745 prefixEnd_3105745 354386661177345887134321 := by
  unfold tailWord_3105745
  simp only [CollatzResearch.WordTrace]
  refine ⟨113275826133423758862294689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75517217422282505908196459 113275826133423758862294689)
  ·
    refine ⟨84956869600067819146721017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113275826133423758862294689 84956869600067819146721017)
    ·
      refine ⟨63717652200050864360040763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84956869600067819146721017 63717652200050864360040763)
      ·
        refine ⟨95576478300076296540061145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63717652200050864360040763 95576478300076296540061145)
        ·
          refine ⟨71682358725057222405045859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95576478300076296540061145 71682358725057222405045859)
          ·
            refine ⟨107523538087585833607568789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71682358725057222405045859 107523538087585833607568789)
            ·
              refine ⟨5040165847855585950354787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 107523538087585833607568789 5040165847855585950354787)
              ·
                refine ⟨7560248771783378925532181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5040165847855585950354787 7560248771783378925532181)
                ·
                  refine ⟨354386661177345887134321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7560248771783378925532181 354386661177345887134321)
                  ·
                    rfl

theorem cell22_3105745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 6].length) (baseStart_3105745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105745 prefixEnd_3105745 := by exact prefixLift 3105745
  have htrace : WordTrace (prefixWord ++ tailWord_3105745) baseStart_3105745 baseEnd_3105745 := by
    simpa [prefixWord, tailWord_3105745, baseEnd_3105745] using wordTrace_append hprefix tailTrace_3105745
  have hstable : (prefixWord ++ tailWord_3105745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105745).length < 2 ^ (prefixWord ++ tailWord_3105745).sum := by decide
  have hdescent : baseEnd_3105745 < baseStart_3105745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105775 : List Nat := [1, 1, 2, 1, 4, 3, 2, 1, 1, 6]
def baseStart_3105775 : Nat := 118140960795 + 3105775 * 2 ^ 59
def prefixEnd_3105775 : Nat := 4983230072969 + 3 ^ 40 * 3105775 * 2
def baseEnd_3105775 : Nat := 1063170253145127583152871

theorem tailTrace_3105775 : CollatzResearch.WordTrace tailWord_3105775 prefixEnd_3105775 1063170253145127583152871 := by
  unfold tailWord_3105775
  simp only [CollatzResearch.WordTrace]
  refine ⟨113276920323315073985886779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75517946882210049323924519 113276920323315073985886779)
  ·
    refine ⟨169915380484972610978830169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113276920323315073985886779 169915380484972610978830169)
    ·
      refine ⟨127436535363729458234122627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169915380484972610978830169 127436535363729458234122627)
      ·
        refine ⟨191154803045594187351183941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127436535363729458234122627 191154803045594187351183941)
        ·
          refine ⟨35841525571048910128346989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191154803045594187351183941 35841525571048910128346989)
          ·
            refine ⟨13440572089143341298130121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35841525571048910128346989 13440572089143341298130121)
            ·
              refine ⟨10080429066857505973597591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13440572089143341298130121 10080429066857505973597591)
              ·
                refine ⟨15120643600286258960396387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10080429066857505973597591 15120643600286258960396387)
                ·
                  refine ⟨22680965400429388440594581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15120643600286258960396387 22680965400429388440594581)
                  ·
                    refine ⟨1063170253145127583152871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22680965400429388440594581 1063170253145127583152871)
                    ·
                      rfl

theorem cell22_3105775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 6].length) (baseStart_3105775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105775 prefixEnd_3105775 := by exact prefixLift 3105775
  have htrace : WordTrace (prefixWord ++ tailWord_3105775) baseStart_3105775 baseEnd_3105775 := by
    simpa [prefixWord, tailWord_3105775, baseEnd_3105775] using wordTrace_append hprefix tailTrace_3105775
  have hstable : (prefixWord ++ tailWord_3105775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105775).length < 2 ^ (prefixWord ++ tailWord_3105775).sum := by decide
  have hdescent : baseEnd_3105775 < baseStart_3105775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105777 : List Nat := [1, 2, 2, 2, 4, 1, 1, 2, 4, 3]
def baseStart_3105777 : Nat := 118140960795 + 3105777 * 2 ^ 59
def prefixEnd_3105777 : Nat := 4983230072969 + 3 ^ 40 * 3105777 * 2
def baseEnd_3105777 : Nat := 1063170937786000244602865

theorem tailTrace_3105777 : CollatzResearch.WordTrace tailWord_3105777 prefixEnd_3105777 1063170937786000244602865 := by
  unfold tailWord_3105777
  simp only [CollatzResearch.WordTrace]
  refine ⟨113276993269307828327459585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75517995512871885551639723 113276993269307828327459585)
  ·
    refine ⟨84957744951980871245594689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113276993269307828327459585 84957744951980871245594689)
    ·
      refine ⟨63718308713985653434196017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84957744951980871245594689 63718308713985653434196017)
      ·
        refine ⟨47788731535489240075647013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63718308713985653434196017 47788731535489240075647013)
        ·
          refine ⟨8960387162904232514183815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47788731535489240075647013 8960387162904232514183815)
          ·
            refine ⟨13440580744356348771275723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8960387162904232514183815 13440580744356348771275723)
            ·
              refine ⟨20160871116534523156913585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13440580744356348771275723 20160871116534523156913585)
              ·
                refine ⟨15120653337400892367685189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20160871116534523156913585 15120653337400892367685189)
                ·
                  refine ⟨2835122500762667318940973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15120653337400892367685189 2835122500762667318940973)
                  ·
                    refine ⟨1063170937786000244602865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2835122500762667318940973 1063170937786000244602865)
                    ·
                      rfl

theorem cell22_3105777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 4, 3].length) (baseStart_3105777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105777 prefixEnd_3105777 := by exact prefixLift 3105777
  have htrace : WordTrace (prefixWord ++ tailWord_3105777) baseStart_3105777 baseEnd_3105777 := by
    simpa [prefixWord, tailWord_3105777, baseEnd_3105777] using wordTrace_append hprefix tailTrace_3105777
  have hstable : (prefixWord ++ tailWord_3105777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105777).length < 2 ^ (prefixWord ++ tailWord_3105777).sum := by decide
  have hdescent : baseEnd_3105777 < baseStart_3105777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105852 : List Nat := [2, 2, 2, 2, 2, 2, 1, 4, 5]
def baseStart_3105852 : Nat := 118140960795 + 3105852 * 2 ^ 59
def prefixEnd_3105852 : Nat := 4983230072969 + 3 ^ 40 * 3105852 * 2
def baseEnd_3105852 : Nat := 354398870606241682992545

theorem tailTrace_3105852 : CollatzResearch.WordTrace tailWord_3105852 prefixEnd_3105852 354398870606241682992545 := by
  unfold tailWord_3105852
  simp only [CollatzResearch.WordTrace]
  refine ⟨56639864372018058068219905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75519819162690744090959873 56639864372018058068219905)
  ·
    refine ⟨42479898279013543551164929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56639864372018058068219905 42479898279013543551164929)
    ·
      refine ⟨31859923709260157663373697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42479898279013543551164929 31859923709260157663373697)
      ·
        refine ⟨23894942781945118247530273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31859923709260157663373697 23894942781945118247530273)
        ·
          refine ⟨17921207086458838685647705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23894942781945118247530273 17921207086458838685647705)
          ·
            refine ⟨13440905314844129014235779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17921207086458838685647705 13440905314844129014235779)
            ·
              refine ⟨20161357972266193521353669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13440905314844129014235779 20161357972266193521353669)
              ·
                refine ⟨3780254619799911285253813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20161357972266193521353669 3780254619799911285253813)
                ·
                  refine ⟨354398870606241682992545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3780254619799911285253813 354398870606241682992545)
                  ·
                    rfl

theorem cell22_3105852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 5].length) (baseStart_3105852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105852 prefixEnd_3105852 := by exact prefixLift 3105852
  have htrace : WordTrace (prefixWord ++ tailWord_3105852) baseStart_3105852 baseEnd_3105852 := by
    simpa [prefixWord, tailWord_3105852, baseEnd_3105852] using wordTrace_append hprefix tailTrace_3105852
  have hstable : (prefixWord ++ tailWord_3105852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105852).length < 2 ^ (prefixWord ++ tailWord_3105852).sum := by decide
  have hdescent : baseEnd_3105852 < baseStart_3105852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105869 : List Nat := [1, 6, 1, 1, 1, 2, 2, 3, 5]
def baseStart_3105869 : Nat := 118140960795 + 3105869 * 2 ^ 59
def prefixEnd_3105869 : Nat := 4983230072969 + 3 ^ 40 * 3105869 * 2
def baseEnd_3105869 : Nat := 354400810422047557100861

theorem tailTrace_3105869 : CollatzResearch.WordTrace tailWord_3105869 prefixEnd_3105869 354400810422047557100861 := by
  unfold tailWord_3105869
  simp only [CollatzResearch.WordTrace]
  refine ⟨113280348784974528039808661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75520232523316352026539107 113280348784974528039808661)
  ·
    refine ⟨5310016349295681001866031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 113280348784974528039808661 5310016349295681001866031)
    ·
      refine ⟨7965024523943521502799047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5310016349295681001866031 7965024523943521502799047)
      ·
        refine ⟨11947536785915282254198571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7965024523943521502799047 11947536785915282254198571)
        ·
          refine ⟨17921305178872923381297857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11947536785915282254198571 17921305178872923381297857)
          ·
            refine ⟨13440978884154692535973393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17921305178872923381297857 13440978884154692535973393)
            ·
              refine ⟨10080734163116019401980045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13440978884154692535973393 10080734163116019401980045)
              ·
                refine ⟨3780275311168507275742517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10080734163116019401980045 3780275311168507275742517)
                ·
                  refine ⟨354400810422047557100861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3780275311168507275742517 354400810422047557100861)
                  ·
                    rfl

theorem cell22_3105869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_3105869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105869 prefixEnd_3105869 := by exact prefixLift 3105869
  have htrace : WordTrace (prefixWord ++ tailWord_3105869) baseStart_3105869 baseEnd_3105869 := by
    simpa [prefixWord, tailWord_3105869, baseEnd_3105869] using wordTrace_append hprefix tailTrace_3105869
  have hstable : (prefixWord ++ tailWord_3105869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105869).length < 2 ^ (prefixWord ++ tailWord_3105869).sum := by decide
  have hdescent : baseEnd_3105869 < baseStart_3105869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105929 : List Nat := [1, 2, 1, 1, 4, 5, 1, 1, 1, 5]
def baseStart_3105929 : Nat := 118140960795 + 3105929 * 2 ^ 59
def prefixEnd_3105929 : Nat := 4983230072969 + 3 ^ 40 * 3105929 * 2
def baseEnd_3105929 : Nat := 1063222970492322514802399

theorem tailTrace_3105929 : CollatzResearch.WordTrace tailWord_3105929 prefixEnd_3105929 1063222970492322514802399 := by
  unfold tailWord_3105929
  simp only [CollatzResearch.WordTrace]
  refine ⟨113282537164757158286992841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75521691443171438857995227 113282537164757158286992841)
  ·
    refine ⟨84961902873567868715244631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113282537164757158286992841 84961902873567868715244631)
    ·
      refine ⟨127442854310351803072866947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84961902873567868715244631 127442854310351803072866947)
      ·
        refine ⟨191164281465527704609300421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127442854310351803072866947 191164281465527704609300421)
        ·
          refine ⟨35843302774786444614243829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191164281465527704609300421 35843302774786444614243829)
          ·
            refine ⟨3360309635136229182585359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35843302774786444614243829 3360309635136229182585359)
            ·
              refine ⟨5040464452704343773878039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3360309635136229182585359 5040464452704343773878039)
              ·
                refine ⟨7560696679056515660817059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5040464452704343773878039 7560696679056515660817059)
                ·
                  refine ⟨11341045018584773491225589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7560696679056515660817059 11341045018584773491225589)
                  ·
                    refine ⟨1063222970492322514802399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11341045018584773491225589 1063222970492322514802399)
                    ·
                      rfl

theorem cell22_3105929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 5].length) (baseStart_3105929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105929 prefixEnd_3105929 := by exact prefixLift 3105929
  have htrace : WordTrace (prefixWord ++ tailWord_3105929) baseStart_3105929 baseEnd_3105929 := by
    simpa [prefixWord, tailWord_3105929, baseEnd_3105929] using wordTrace_append hprefix tailTrace_3105929
  have hstable : (prefixWord ++ tailWord_3105929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105929).length < 2 ^ (prefixWord ++ tailWord_3105929).sum := by decide
  have hdescent : baseEnd_3105929 < baseStart_3105929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3105959 : List Nat := [1, 1, 6, 2, 1, 3, 8]
def baseStart_3105959 : Nat := 118140960795 + 3105959 * 2 ^ 59
def prefixEnd_3105959 : Nat := 4983230072969 + 3 ^ 40 * 3105959 * 2
def baseEnd_3105959 : Nat := 39379008892793053205641

theorem tailTrace_3105959 : CollatzResearch.WordTrace tailWord_3105959 prefixEnd_3105959 39379008892793053205641 := by
  unfold tailWord_3105959
  simp only [CollatzResearch.WordTrace]
  refine ⟨113283631354648473410584931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75522420903098982273723287 113283631354648473410584931)
  ·
    refine ⟨169925447031972710115877397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113283631354648473410584931 169925447031972710115877397)
    ·
      refine ⟨7965255329623720786681753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 169925447031972710115877397 7965255329623720786681753)
      ·
        refine ⟨5973941497217790590011315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7965255329623720786681753 5973941497217790590011315)
        ·
          refine ⟨8960912245826685885016973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5973941497217790590011315 8960912245826685885016973)
          ·
            refine ⟨3360342092185007206881365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8960912245826685885016973 3360342092185007206881365)
            ·
              refine ⟨39379008892793053205641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3360342092185007206881365 39379008892793053205641)
              ·
                rfl

theorem cell22_3105959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 8].length) (baseStart_3105959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3105959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3105959 prefixEnd_3105959 := by exact prefixLift 3105959
  have htrace : WordTrace (prefixWord ++ tailWord_3105959) baseStart_3105959 baseEnd_3105959 := by
    simpa [prefixWord, tailWord_3105959, baseEnd_3105959] using wordTrace_append hprefix tailTrace_3105959
  have hstable : (prefixWord ++ tailWord_3105959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3105959).length < 2 ^ (prefixWord ++ tailWord_3105959).sum := by decide
  have hdescent : baseEnd_3105959 < baseStart_3105959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3105959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106021 : List Nat := [1, 3, 1, 4, 3, 1, 2, 2, 5]
def baseStart_3106021 : Nat := 118140960795 + 3106021 * 2 ^ 59
def prefixEnd_3106021 : Nat := 4983230072969 + 3 ^ 40 * 3106021 * 2
def baseEnd_3106021 : Nat := 354418154657488313834039

theorem tailTrace_3106021 : CollatzResearch.WordTrace tailWord_3106021 prefixEnd_3106021 354418154657488313834039 := by
  unfold tailWord_3106021
  simp only [CollatzResearch.WordTrace]
  refine ⟨113285892680423857999341917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75523928453615905332894611 113285892680423857999341917)
  ·
    refine ⟨42482209755158946749753219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113285892680423857999341917 42482209755158946749753219)
    ·
      refine ⟨63723314632738420124629829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42482209755158946749753219 63723314632738420124629829)
      ·
        refine ⟨11948121493638453773368093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63723314632738420124629829 11948121493638453773368093)
        ·
          refine ⟨4480545560114420165013035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11948121493638453773368093 4480545560114420165013035)
          ·
            refine ⟨6720818340171630247519553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4480545560114420165013035 6720818340171630247519553)
            ·
              refine ⟨5040613755128722685639665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6720818340171630247519553 5040613755128722685639665)
              ·
                refine ⟨3780460316346542014229749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5040613755128722685639665 3780460316346542014229749)
                ·
                  refine ⟨354418154657488313834039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3780460316346542014229749 354418154657488313834039)
                  ·
                    rfl

theorem cell22_3106021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 5].length) (baseStart_3106021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106021 prefixEnd_3106021 := by exact prefixLift 3106021
  have htrace : WordTrace (prefixWord ++ tailWord_3106021) baseStart_3106021 baseEnd_3106021 := by
    simpa [prefixWord, tailWord_3106021, baseEnd_3106021] using wordTrace_append hprefix tailTrace_3106021
  have hstable : (prefixWord ++ tailWord_3106021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106021).length < 2 ^ (prefixWord ++ tailWord_3106021).sum := by decide
  have hdescent : baseEnd_3106021 < baseStart_3106021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106049 : List Nat := [1, 2, 4, 1, 1, 4, 1, 2, 6]
def baseStart_3106049 : Nat := 118140960795 + 3106049 * 2 ^ 59
def prefixEnd_3106049 : Nat := 4983230072969 + 3 ^ 40 * 3106049 * 2
def baseEnd_3106049 : Nat := 354421349648227400600677

theorem tailTrace_3106049 : CollatzResearch.WordTrace tailWord_3106049 prefixEnd_3106049 354421349648227400600677 := by
  unfold tailWord_3106049
  simp only [CollatzResearch.WordTrace]
  refine ⟨113286913924322418781361201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75524609282881612520907467 113286913924322418781361201)
  ·
    refine ⟨84965185443241814086020901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113286913924322418781361201 84965185443241814086020901)
    ·
      refine ⟨15930972270607840141128919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84965185443241814086020901 15930972270607840141128919)
      ·
        refine ⟨23896458405911760211693379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15930972270607840141128919 23896458405911760211693379)
        ·
          refine ⟨35844687608867640317540069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23896458405911760211693379 35844687608867640317540069)
          ·
            refine ⟨6720878926662682559538763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35844687608867640317540069 6720878926662682559538763)
            ·
              refine ⟨10081318389994023839308145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6720878926662682559538763 10081318389994023839308145)
              ·
                refine ⟨7560988792495517879481109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10081318389994023839308145 7560988792495517879481109)
                ·
                  refine ⟨354421349648227400600677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7560988792495517879481109 354421349648227400600677)
                  ·
                    rfl

theorem cell22_3106049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 6].length) (baseStart_3106049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106049 prefixEnd_3106049 := by exact prefixLift 3106049
  have htrace : WordTrace (prefixWord ++ tailWord_3106049) baseStart_3106049 baseEnd_3106049 := by
    simpa [prefixWord, tailWord_3106049, baseEnd_3106049] using wordTrace_append hprefix tailTrace_3106049
  have hstable : (prefixWord ++ tailWord_3106049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106049).length < 2 ^ (prefixWord ++ tailWord_3106049).sum := by decide
  have hdescent : baseEnd_3106049 < baseStart_3106049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106107 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 5, 8]
def baseStart_3106107 : Nat := 118140960795 + 3106107 * 2 ^ 59
def prefixEnd_3106107 : Nat := 4983230072969 + 3 ^ 40 * 3106107 * 2
def baseEnd_3106107 : Nat := 1063283903529989383851853

theorem tailTrace_3106107 : CollatzResearch.WordTrace tailWord_3106107 prefixEnd_3106107 1063283903529989383851853 := by
  unfold tailWord_3106107
  simp only [CollatzResearch.WordTrace]
  refine ⟨113289029358112294686972575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75526019572074863124648383 113289029358112294686972575)
  ·
    refine ⟨169933544037168442030458863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113289029358112294686972575 169933544037168442030458863)
    ·
      refine ⟨254900316055752663045688295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169933544037168442030458863 254900316055752663045688295)
      ·
        refine ⟨382350474083628994568532443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254900316055752663045688295 382350474083628994568532443)
        ·
          refine ⟨573525711125443491852798665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382350474083628994568532443 573525711125443491852798665)
          ·
            refine ⟨430144283344082618889598999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 573525711125443491852798665 430144283344082618889598999)
            ·
              refine ⟨645216425016123928334398499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430144283344082618889598999 645216425016123928334398499)
              ·
                refine ⟨967824637524185892501597749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645216425016123928334398499 967824637524185892501597749)
                ·
                  refine ⟨90733559767892427422024789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 967824637524185892501597749 90733559767892427422024789)
                  ·
                    refine ⟨1063283903529989383851853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90733559767892427422024789 1063283903529989383851853)
                    ·
                      rfl

theorem cell22_3106107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 8].length) (baseStart_3106107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106107 prefixEnd_3106107 := by exact prefixLift 3106107
  have htrace : WordTrace (prefixWord ++ tailWord_3106107) baseStart_3106107 baseEnd_3106107 := by
    simpa [prefixWord, tailWord_3106107, baseEnd_3106107] using wordTrace_append hprefix tailTrace_3106107
  have hstable : (prefixWord ++ tailWord_3106107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106107).length < 2 ^ (prefixWord ++ tailWord_3106107).sum := by decide
  have hdescent : baseEnd_3106107 < baseStart_3106107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106111 : List Nat := [1, 1, 2, 2, 4, 4, 2, 6]
def baseStart_3106111 : Nat := 118140960795 + 3106111 * 2 ^ 59
def prefixEnd_3106111 : Nat := 4983230072969 + 3 ^ 40 * 3106111 * 2
def baseEnd_3106111 : Nat := 118142808090192745194649

theorem tailTrace_3106111 : CollatzResearch.WordTrace tailWord_3106111 prefixEnd_3106111 118142808090192745194649 := by
  unfold tailWord_3106111
  simp only [CollatzResearch.WordTrace]
  refine ⟨113289175250097803370118187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75526116833398535580078791 113289175250097803370118187)
  ·
    refine ⟨169933762875146705055177281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113289175250097803370118187 169933762875146705055177281)
    ·
      refine ⟨127450322156360028791382961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169933762875146705055177281 127450322156360028791382961)
      ·
        refine ⟨95587741617270021593537221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127450322156360028791382961 95587741617270021593537221)
        ·
          refine ⟨17922701553238129048788229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95587741617270021593537221 17922701553238129048788229)
          ·
            refine ⟨3360506541232149196647793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17922701553238129048788229 3360506541232149196647793)
            ·
              refine ⟨2520379905924111897485845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3360506541232149196647793 2520379905924111897485845)
              ·
                refine ⟨118142808090192745194649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2520379905924111897485845 118142808090192745194649)
                ·
                  rfl

theorem cell22_3106111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 6].length) (baseStart_3106111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106111 prefixEnd_3106111 := by exact prefixLift 3106111
  have htrace : WordTrace (prefixWord ++ tailWord_3106111) baseStart_3106111 baseEnd_3106111 := by
    simpa [prefixWord, tailWord_3106111, baseEnd_3106111] using wordTrace_append hprefix tailTrace_3106111
  have hstable : (prefixWord ++ tailWord_3106111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106111).length < 2 ^ (prefixWord ++ tailWord_3106111).sum := by decide
  have hdescent : baseEnd_3106111 < baseStart_3106111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106134 : List Nat := [5, 2, 3, 1, 2, 1, 1, 1, 6]
def baseStart_3106134 : Nat := 118140960795 + 3106134 * 2 ^ 59
def prefixEnd_3106134 : Nat := 4983230072969 + 3 ^ 40 * 3106134 * 2
def baseEnd_3106134 : Nat := 354431048727256771142257

theorem tailTrace_3106134 : CollatzResearch.WordTrace tailWord_3106134 prefixEnd_3106134 354431048727256771142257 := by
  unfold tailWord_3106134
  simp only [CollatzResearch.WordTrace]
  refine ⟨7080625883063404893637841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75526676086009652198803637 7080625883063404893637841)
  ·
    refine ⟨5310469412297553670228381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7080625883063404893637841 5310469412297553670228381)
    ·
      refine ⟨1991426029611582626335643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5310469412297553670228381 1991426029611582626335643)
      ·
        refine ⟨2987139044417373939503465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1991426029611582626335643 2987139044417373939503465)
        ·
          refine ⟨2240354283313030454627599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2987139044417373939503465 2240354283313030454627599)
          ·
            refine ⟨3360531424969545681941399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2240354283313030454627599 3360531424969545681941399)
            ·
              refine ⟨5040797137454318522912099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3360531424969545681941399 5040797137454318522912099)
              ·
                refine ⟨7561195706181477784368149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5040797137454318522912099 7561195706181477784368149)
                ·
                  refine ⟨354431048727256771142257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7561195706181477784368149 354431048727256771142257)
                  ·
                    rfl

theorem cell22_3106134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_3106134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106134 prefixEnd_3106134 := by exact prefixLift 3106134
  have htrace : WordTrace (prefixWord ++ tailWord_3106134) baseStart_3106134 baseEnd_3106134 := by
    simpa [prefixWord, tailWord_3106134, baseEnd_3106134] using wordTrace_append hprefix tailTrace_3106134
  have hstable : (prefixWord ++ tailWord_3106134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106134).length < 2 ^ (prefixWord ++ tailWord_3106134).sum := by decide
  have hdescent : baseEnd_3106134 < baseStart_3106134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106156 : List Nat := [2, 2, 1, 1, 5, 2, 1, 3, 5]
def baseStart_3106156 : Nat := 118140960795 + 3106156 * 2 ^ 59
def prefixEnd_3106156 : Nat := 4983230072969 + 3 ^ 40 * 3106156 * 2
def baseEnd_3106156 : Nat := 354433559077123196458901

theorem tailTrace_3106156 : CollatzResearch.WordTrace tailWord_3106156 prefixEnd_3106156 354433559077123196458901 := by
  unfold tailWord_3106156
  simp only [CollatzResearch.WordTrace]
  refine ⟨56645408267467388027753161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75527211023289850703670881 56645408267467388027753161)
  ·
    refine ⟨42484056200600541020814871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56645408267467388027753161 42484056200600541020814871)
    ·
      refine ⟨63726084300900811531222307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42484056200600541020814871 63726084300900811531222307)
      ·
        refine ⟨95589126451351217296833461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63726084300900811531222307 95589126451351217296833461)
        ·
          refine ⟨8961480604814176621578137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95589126451351217296833461 8961480604814176621578137)
          ·
            refine ⟨6721110453610632466183603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8961480604814176621578137 6721110453610632466183603)
            ·
              refine ⟨10081665680415948699275405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6721110453610632466183603 10081665680415948699275405)
              ·
                refine ⟨3780624630155980762228277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10081665680415948699275405 3780624630155980762228277)
                ·
                  refine ⟨354433559077123196458901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3780624630155980762228277 354433559077123196458901)
                  ·
                    rfl

theorem cell22_3106156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 5].length) (baseStart_3106156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106156 prefixEnd_3106156 := by exact prefixLift 3106156
  have htrace : WordTrace (prefixWord ++ tailWord_3106156) baseStart_3106156 baseEnd_3106156 := by
    simpa [prefixWord, tailWord_3106156, baseEnd_3106156] using wordTrace_append hprefix tailTrace_3106156
  have hstable : (prefixWord ++ tailWord_3106156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106156).length < 2 ^ (prefixWord ++ tailWord_3106156).sum := by decide
  have hdescent : baseEnd_3106156 < baseStart_3106156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106199 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 5, 5]
def baseStart_3106199 : Nat := 118140960795 + 3106199 * 2 ^ 59
def prefixEnd_3106199 : Nat := 4983230072969 + 3 ^ 40 * 3106199 * 2
def baseEnd_3106199 : Nat := 1063315397010131810551571

theorem tailTrace_3106199 : CollatzResearch.WordTrace tailWord_3106199 prefixEnd_3106199 1063315397010131810551571 := by
  unfold tailWord_3106199
  simp only [CollatzResearch.WordTrace]
  refine ⟨113292384873778994399321651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75528256582519329599547767 113292384873778994399321651)
  ·
    refine ⟨169938577310668491598982477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113292384873778994399321651 169938577310668491598982477)
    ·
      refine ⟨63726966491500684349618429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169938577310668491598982477 63726966491500684349618429)
      ·
        refine ⟨23897612434312756631106911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63726966491500684349618429 23897612434312756631106911)
        ·
          refine ⟨35846418651469134946660367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23897612434312756631106911 35846418651469134946660367)
          ·
            refine ⟨53769627977203702419990551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35846418651469134946660367 53769627977203702419990551)
            ·
              refine ⟨80654441965805553629985827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53769627977203702419990551 80654441965805553629985827)
              ·
                refine ⟨120981662948708330444978741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80654441965805553629985827 120981662948708330444978741)
                ·
                  refine ⟨11342030901441405979216757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120981662948708330444978741 11342030901441405979216757)
                  ·
                    refine ⟨1063315397010131810551571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11342030901441405979216757 1063315397010131810551571)
                    ·
                      rfl

theorem cell22_3106199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_3106199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106199 prefixEnd_3106199 := by exact prefixLift 3106199
  have htrace : WordTrace (prefixWord ++ tailWord_3106199) baseStart_3106199 baseEnd_3106199 := by
    simpa [prefixWord, tailWord_3106199, baseEnd_3106199] using wordTrace_append hprefix tailTrace_3106199
  have hstable : (prefixWord ++ tailWord_3106199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106199).length < 2 ^ (prefixWord ++ tailWord_3106199).sum := by decide
  have hdescent : baseEnd_3106199 < baseStart_3106199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106250 : List Nat := [3, 1, 2, 1, 2, 5, 1, 2, 2, 3]
def baseStart_3106250 : Nat := 118140960795 + 3106250 * 2 ^ 59
def prefixEnd_3106250 : Nat := 4983230072969 + 3 ^ 40 * 3106250 * 2
def baseEnd_3106250 : Nat := 1063332855352384677526415

theorem tailTrace_3106250 : CollatzResearch.WordTrace tailWord_3106250 prefixEnd_3106250 1063332855352384677526415 := by
  unfold tailWord_3106250
  simp only [CollatzResearch.WordTrace]
  refine ⟨28323561249148557527357051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75529496664396153406285469 28323561249148557527357051)
  ·
    refine ⟨42485341873722836291035577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28323561249148557527357051 42485341873722836291035577)
    ·
      refine ⟨31864006405292127218276683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42485341873722836291035577 31864006405292127218276683)
      ·
        refine ⟨47796009607938190827415025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31864006405292127218276683 47796009607938190827415025)
        ·
          refine ⟨35847007205953643120561269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47796009607938190827415025 35847007205953643120561269)
          ·
            refine ⟨3360656925558154042552619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35847007205953643120561269 3360656925558154042552619)
            ·
              refine ⟨5040985388337231063828929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3360656925558154042552619 5040985388337231063828929)
              ·
                refine ⟨3780739041252923297871697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5040985388337231063828929 3780739041252923297871697)
                ·
                  refine ⟨2835554280939692473403773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3780739041252923297871697 2835554280939692473403773)
                  ·
                    refine ⟨1063332855352384677526415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2835554280939692473403773 1063332855352384677526415)
                    ·
                      rfl

theorem cell22_3106250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_3106250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106250 prefixEnd_3106250 := by exact prefixLift 3106250
  have htrace : WordTrace (prefixWord ++ tailWord_3106250) baseStart_3106250 baseEnd_3106250 := by
    simpa [prefixWord, tailWord_3106250, baseEnd_3106250] using wordTrace_append hprefix tailTrace_3106250
  have hstable : (prefixWord ++ tailWord_3106250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106250).length < 2 ^ (prefixWord ++ tailWord_3106250).sum := by decide
  have hdescent : baseEnd_3106250 < baseStart_3106250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106321 : List Nat := [1, 2, 2, 1, 1, 2, 4, 2, 3, 4]
def baseStart_3106321 : Nat := 118140960795 + 3106321 * 2 ^ 59
def prefixEnd_3106321 : Nat := 4983230072969 + 3 ^ 40 * 3106321 * 2
def baseEnd_3106321 : Nat := 1063357160103364159001197

theorem tailTrace_3106321 : CollatzResearch.WordTrace tailWord_3106321 prefixEnd_3106321 1063357160103364159001197 := by
  unfold tailWord_3106321
  simp only [CollatzResearch.WordTrace]
  refine ⟨113296834579337009235262817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75531223052891339490175211 113296834579337009235262817)
  ·
    refine ⟨84972625934502756926447113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113296834579337009235262817 84972625934502756926447113)
    ·
      refine ⟨63729469450877067694835335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84972625934502756926447113 63729469450877067694835335)
      ·
        refine ⟨95594204176315601542253003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63729469450877067694835335 95594204176315601542253003)
        ·
          refine ⟨143391306264473402313379505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95594204176315601542253003 143391306264473402313379505)
          ·
            refine ⟨107543479698355051735034629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143391306264473402313379505 107543479698355051735034629)
            ·
              refine ⟨20164402443441572200318993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107543479698355051735034629 20164402443441572200318993)
              ·
                refine ⟨15123301832581179150239245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20164402443441572200318993 15123301832581179150239245)
                ·
                  refine ⟨5671238187217942181339717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15123301832581179150239245 5671238187217942181339717)
                  ·
                    refine ⟨1063357160103364159001197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5671238187217942181339717 1063357160103364159001197)
                    ·
                      rfl

theorem cell22_3106321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_3106321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106321 prefixEnd_3106321 := by exact prefixLift 3106321
  have htrace : WordTrace (prefixWord ++ tailWord_3106321) baseStart_3106321 baseEnd_3106321 := by
    simpa [prefixWord, tailWord_3106321, baseEnd_3106321] using wordTrace_append hprefix tailTrace_3106321
  have hstable : (prefixWord ++ tailWord_3106321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106321).length < 2 ^ (prefixWord ++ tailWord_3106321).sum := by decide
  have hdescent : baseEnd_3106321 < baseStart_3106321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106325 : List Nat := [1, 3, 2, 1, 3, 4, 2, 1, 5]
def baseStart_3106325 : Nat := 118140960795 + 3106325 * 2 ^ 59
def prefixEnd_3106325 : Nat := 4983230072969 + 3 ^ 40 * 3106325 * 2
def baseEnd_3106325 : Nat := 354452843128369827300395

theorem tailTrace_3106325 : CollatzResearch.WordTrace tailWord_3106325 prefixEnd_3106325 354452843128369827300395 := by
  unfold tailWord_3106325
  simp only [CollatzResearch.WordTrace]
  refine ⟨113296980471322517918408429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75531320314215011945605619 113296980471322517918408429)
  ·
    refine ⟨42486367676745944219403161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113296980471322517918408429 42486367676745944219403161)
    ·
      refine ⟨31864775757559458164552371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42486367676745944219403161 31864775757559458164552371)
      ·
        refine ⟨47797163636339187246828557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31864775757559458164552371 47797163636339187246828557)
        ·
          refine ⟨17923936363627195217560709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47797163636339187246828557 17923936363627195217560709)
          ·
            refine ⟨3360738068180099103292633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17923936363627195217560709 3360738068180099103292633)
            ·
              refine ⟨2520553551135074327469475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3360738068180099103292633 2520553551135074327469475)
              ·
                refine ⟨3780830326702611491204213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2520553551135074327469475 3780830326702611491204213)
                ·
                  refine ⟨354452843128369827300395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3780830326702611491204213 354452843128369827300395)
                  ·
                    rfl

theorem cell22_3106325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 5].length) (baseStart_3106325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106325 prefixEnd_3106325 := by exact prefixLift 3106325
  have htrace : WordTrace (prefixWord ++ tailWord_3106325) baseStart_3106325 baseEnd_3106325 := by
    simpa [prefixWord, tailWord_3106325, baseEnd_3106325] using wordTrace_append hprefix tailTrace_3106325
  have hstable : (prefixWord ++ tailWord_3106325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106325).length < 2 ^ (prefixWord ++ tailWord_3106325).sum := by decide
  have hdescent : baseEnd_3106325 < baseStart_3106325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106353 : List Nat := [1, 2, 2, 3, 1, 1, 1, 7, 4]
def baseStart_3106353 : Nat := 118140960795 + 3106353 * 2 ^ 59
def prefixEnd_3106353 : Nat := 4983230072969 + 3 ^ 40 * 3106353 * 2
def baseEnd_3106353 : Nat := 354456038119108914067033

theorem tailTrace_3106353 : CollatzResearch.WordTrace tailWord_3106353 prefixEnd_3106353 354456038119108914067033 := by
  unfold tailWord_3106353
  simp only [CollatzResearch.WordTrace]
  refine ⟨113298001715221078700427713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75532001143480719133618475 113298001715221078700427713)
  ·
    refine ⟨84973501286415809025320785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113298001715221078700427713 84973501286415809025320785)
    ·
      refine ⟨63730125964811856768990589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84973501286415809025320785 63730125964811856768990589)
      ·
        refine ⟨23898797236804446288371471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63730125964811856768990589 23898797236804446288371471)
        ·
          refine ⟨35848195855206669432557207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23898797236804446288371471 35848195855206669432557207)
          ·
            refine ⟨53772293782810004148835811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35848195855206669432557207 53772293782810004148835811)
            ·
              refine ⟨80658440674215006223253717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53772293782810004148835811 80658440674215006223253717)
              ·
                refine ⟨1890432203301914208357509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 80658440674215006223253717 1890432203301914208357509)
                ·
                  refine ⟨354456038119108914067033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1890432203301914208357509 354456038119108914067033)
                  ·
                    rfl

theorem cell22_3106353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 7, 4].length) (baseStart_3106353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106353 prefixEnd_3106353 := by exact prefixLift 3106353
  have htrace : WordTrace (prefixWord ++ tailWord_3106353) baseStart_3106353 baseEnd_3106353 := by
    simpa [prefixWord, tailWord_3106353, baseEnd_3106353] using wordTrace_append hprefix tailTrace_3106353
  have hstable : (prefixWord ++ tailWord_3106353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106353).length < 2 ^ (prefixWord ++ tailWord_3106353).sum := by decide
  have hdescent : baseEnd_3106353 < baseStart_3106353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106355 : List Nat := [1, 1, 1, 2, 4, 4, 3, 1, 1, 4]
def baseStart_3106355 : Nat := 118140960795 + 3106355 * 2 ^ 59
def prefixEnd_3106355 : Nat := 4983230072969 + 3 ^ 40 * 3106355 * 2
def baseEnd_3106355 : Nat := 1063368798998199403651093

theorem tailTrace_3106355 : CollatzResearch.WordTrace tailWord_3106355 prefixEnd_3106355 1063368798998199403651093 := by
  unfold tailWord_3106355
  simp only [CollatzResearch.WordTrace]
  refine ⟨113298074661213833042000519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75532049774142555361333679 113298074661213833042000519)
  ·
    refine ⟨169947111991820749563000779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113298074661213833042000519 169947111991820749563000779)
    ·
      refine ⟨254920667987731124344501169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169947111991820749563000779 254920667987731124344501169)
      ·
        refine ⟨191190500990798343258375877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254920667987731124344501169 191190500990798343258375877)
        ·
          refine ⟨35848218935774689360945477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191190500990798343258375877 35848218935774689360945477)
          ·
            refine ⟨6721541050457754255177277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35848218935774689360945477 6721541050457754255177277)
            ·
              refine ⟨2520577893921657845691479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6721541050457754255177277 2520577893921657845691479)
              ·
                refine ⟨3780866840882486768537219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2520577893921657845691479 3780866840882486768537219)
                ·
                  refine ⟨5671300261323730152805829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3780866840882486768537219 5671300261323730152805829)
                  ·
                    refine ⟨1063368798998199403651093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5671300261323730152805829 1063368798998199403651093)
                    ·
                      rfl

theorem cell22_3106355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 1, 4].length) (baseStart_3106355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106355 prefixEnd_3106355 := by exact prefixLift 3106355
  have htrace : WordTrace (prefixWord ++ tailWord_3106355) baseStart_3106355 baseEnd_3106355 := by
    simpa [prefixWord, tailWord_3106355, baseEnd_3106355] using wordTrace_append hprefix tailTrace_3106355
  have hstable : (prefixWord ++ tailWord_3106355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106355).length < 2 ^ (prefixWord ++ tailWord_3106355).sum := by decide
  have hdescent : baseEnd_3106355 < baseStart_3106355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106464 : List Nat := [2, 1, 1, 4, 3, 3, 1, 3, 1, 3]
def baseStart_3106464 : Nat := 118140960795 + 3106464 * 2 ^ 59
def prefixEnd_3106464 : Nat := 4983230072969 + 3 ^ 40 * 3106464 * 2
def baseEnd_3106464 : Nat := 1063406111925759452675759

theorem tailTrace_3106464 : CollatzResearch.WordTrace tailWord_3106464 prefixEnd_3106464 1063406111925759452675759 := by
  unfold tailWord_3106464
  simp only [CollatzResearch.WordTrace]
  refine ⟨56651025108909472328859223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75534700145212629771812297 56651025108909472328859223)
  ·
    refine ⟨84976537663364208493288835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56651025108909472328859223 84976537663364208493288835)
    ·
      refine ⟨127464806495046312739933253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84976537663364208493288835 127464806495046312739933253)
      ·
        refine ⟨23899651217821183638737485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127464806495046312739933253 23899651217821183638737485)
        ·
          refine ⟨8962369206682943864526557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23899651217821183638737485 8962369206682943864526557)
          ·
            refine ⟨3360888452506103949197459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8962369206682943864526557 3360888452506103949197459)
            ·
              refine ⟨5041332678759155923796189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3360888452506103949197459 5041332678759155923796189)
              ·
                refine ⟨1890499754534683471423571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5041332678759155923796189 1890499754534683471423571)
                ·
                  refine ⟨2835749631802025207135357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1890499754534683471423571 2835749631802025207135357)
                  ·
                    refine ⟨1063406111925759452675759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2835749631802025207135357 1063406111925759452675759)
                    ·
                      rfl

theorem cell22_3106464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 3, 1, 3].length) (baseStart_3106464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106464 prefixEnd_3106464 := by exact prefixLift 3106464
  have htrace : WordTrace (prefixWord ++ tailWord_3106464) baseStart_3106464 baseEnd_3106464 := by
    simpa [prefixWord, tailWord_3106464, baseEnd_3106464] using wordTrace_append hprefix tailTrace_3106464
  have hstable : (prefixWord ++ tailWord_3106464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106464).length < 2 ^ (prefixWord ++ tailWord_3106464).sum := by decide
  have hdescent : baseEnd_3106464 < baseStart_3106464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106503 : List Nat := [1, 1, 4, 1, 1, 1, 4, 3, 1, 5]
def baseStart_3106503 : Nat := 118140960795 + 3106503 * 2 ^ 59
def prefixEnd_3106503 : Nat := 4983230072969 + 3 ^ 40 * 3106503 * 2
def baseEnd_3106503 : Nat := 1063419462422776350950639

theorem tailTrace_3106503 : CollatzResearch.WordTrace tailWord_3106503 prefixEnd_3106503 1063419462422776350950639 := by
  unfold tailWord_3106503
  simp only [CollatzResearch.WordTrace]
  refine ⟨113303472664677654318388163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75535648443118436212258775 113303472664677654318388163)
  ·
    refine ⟨169955208997016481477582245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113303472664677654318388163 169955208997016481477582245)
    ·
      refine ⟨31866601686940590277046671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169955208997016481477582245 31866601686940590277046671)
      ·
        refine ⟨47799902530410885415570007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31866601686940590277046671 47799902530410885415570007)
        ·
          refine ⟨71699853795616328123355011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47799902530410885415570007 71699853795616328123355011)
          ·
            refine ⟨107549780693424492185032517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71699853795616328123355011 107549780693424492185032517)
            ·
              refine ⟨20165583880017092284693597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107549780693424492185032517 20165583880017092284693597)
              ·
                refine ⟨7562093955006409606760099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20165583880017092284693597 7562093955006409606760099)
                ·
                  refine ⟨11343140932509614410140149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7562093955006409606760099 11343140932509614410140149)
                  ·
                    refine ⟨1063419462422776350950639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11343140932509614410140149 1063419462422776350950639)
                    ·
                      rfl

theorem cell22_3106503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_3106503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106503 prefixEnd_3106503 := by exact prefixLift 3106503
  have htrace : WordTrace (prefixWord ++ tailWord_3106503) baseStart_3106503 baseEnd_3106503 := by
    simpa [prefixWord, tailWord_3106503, baseEnd_3106503] using wordTrace_append hprefix tailTrace_3106503
  have hstable : (prefixWord ++ tailWord_3106503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106503).length < 2 ^ (prefixWord ++ tailWord_3106503).sum := by decide
  have hdescent : baseEnd_3106503 < baseStart_3106503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106550 : List Nat := [5, 1, 1, 1, 1, 3, 3, 7]
def baseStart_3106550 : Nat := 118140960795 + 3106550 * 2 ^ 59
def prefixEnd_3106550 : Nat := 4983230072969 + 3 ^ 40 * 3106550 * 2
def baseEnd_3106550 : Nat := 118159505720364877225055

theorem tailTrace_3106550 : CollatzResearch.WordTrace tailWord_3106550 prefixEnd_3106550 118159505720364877225055 := by
  unfold tailWord_3106550
  simp only [CollatzResearch.WordTrace]
  refine ⟨7081574180969211334084319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75536791263671587563566069 7081574180969211334084319)
  ·
    refine ⟨10622361271453817001126479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7081574180969211334084319 10622361271453817001126479)
    ·
      refine ⟨15933541907180725501689719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10622361271453817001126479 15933541907180725501689719)
      ·
        refine ⟨23900312860771088252534579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15933541907180725501689719 23900312860771088252534579)
        ·
          refine ⟨35850469291156632378801869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23900312860771088252534579 35850469291156632378801869)
          ·
            refine ⟨13443925984183737142050701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35850469291156632378801869 13443925984183737142050701)
            ·
              refine ⟨5041472244068901428269013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13443925984183737142050701 5041472244068901428269013)
              ·
                refine ⟨118159505720364877225055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5041472244068901428269013 118159505720364877225055)
                ·
                  rfl

theorem cell22_3106550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_3106550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106550 prefixEnd_3106550 := by exact prefixLift 3106550
  have htrace : WordTrace (prefixWord ++ tailWord_3106550) baseStart_3106550 baseEnd_3106550 := by
    simpa [prefixWord, tailWord_3106550, baseEnd_3106550] using wordTrace_append hprefix tailTrace_3106550
  have hstable : (prefixWord ++ tailWord_3106550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106550).length < 2 ^ (prefixWord ++ tailWord_3106550).sum := by decide
  have hdescent : baseEnd_3106550 < baseStart_3106550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106567 : List Nat := [1, 1, 4, 4, 2, 1, 3, 6]
def baseStart_3106567 : Nat := 118140960795 + 3106567 * 2 ^ 59
def prefixEnd_3106567 : Nat := 4983230072969 + 3 ^ 40 * 3106567 * 2
def baseEnd_3106567 : Nat := 118160152325633501927827

theorem tailTrace_3106567 : CollatzResearch.WordTrace tailWord_3106567 prefixEnd_3106567 118160152325633501927827 := by
  unfold tailWord_3106567
  simp only [CollatzResearch.WordTrace]
  refine ⟨113305806936445793248717955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75537204624297195499145303 113305806936445793248717955)
  ·
    refine ⟨169958710404668689873076933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113305806936445793248717955 169958710404668689873076933)
    ·
      refine ⟨31867258200875379351201925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169958710404668689873076933 31867258200875379351201925)
      ·
        refine ⟨5975110912664133628350361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31867258200875379351201925 5975110912664133628350361)
        ·
          refine ⟨4481333184498100221262771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5975110912664133628350361 4481333184498100221262771)
          ·
            refine ⟨6721999776747150331894157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4481333184498100221262771 6721999776747150331894157)
            ·
              refine ⟨2520749916280181374460309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6721999776747150331894157 2520749916280181374460309)
              ·
                refine ⟨118160152325633501927827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2520749916280181374460309 118160152325633501927827)
                ·
                  rfl

theorem cell22_3106567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 6].length) (baseStart_3106567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106567 prefixEnd_3106567 := by exact prefixLift 3106567
  have htrace : WordTrace (prefixWord ++ tailWord_3106567) baseStart_3106567 baseEnd_3106567 := by
    simpa [prefixWord, tailWord_3106567, baseEnd_3106567] using wordTrace_append hprefix tailTrace_3106567
  have hstable : (prefixWord ++ tailWord_3106567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106567).length < 2 ^ (prefixWord ++ tailWord_3106567).sum := by decide
  have hdescent : baseEnd_3106567 < baseStart_3106567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106595 : List Nat := [1, 1, 1, 4, 2, 1, 5, 2, 5]
def baseStart_3106595 : Nat := 118140960795 + 3106595 * 2 ^ 59
def prefixEnd_3106595 : Nat := 4983230072969 + 3 ^ 40 * 3106595 * 2
def baseEnd_3106595 : Nat := 354483651967639592550119

theorem tailTrace_3106595 : CollatzResearch.WordTrace tailWord_3106595 prefixEnd_3106595 354483651967639592550119 := by
  unfold tailWord_3106595
  simp only [CollatzResearch.WordTrace]
  refine ⟨113306828180344354030737239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75537885453562902687158159 113306828180344354030737239)
  ·
    refine ⟨169960242270516531046105859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113306828180344354030737239 169960242270516531046105859)
    ·
      refine ⟨254940363405774796569158789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169960242270516531046105859 254940363405774796569158789)
      ·
        refine ⟨47801318138582774356717273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254940363405774796569158789 47801318138582774356717273)
        ·
          refine ⟨35850988603937080767537955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47801318138582774356717273 35850988603937080767537955)
          ·
            refine ⟨53776482905905621151306933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35850988603937080767537955 53776482905905621151306933)
            ·
              refine ⟨5041545272428651982935025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53776482905905621151306933 5041545272428651982935025)
              ·
                refine ⟨3781158954321488987201269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5041545272428651982935025 3781158954321488987201269)
                ·
                  refine ⟨354483651967639592550119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3781158954321488987201269 354483651967639592550119)
                  ·
                    rfl

theorem cell22_3106595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 5].length) (baseStart_3106595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106595 prefixEnd_3106595 := by exact prefixLift 3106595
  have htrace : WordTrace (prefixWord ++ tailWord_3106595) baseStart_3106595 baseEnd_3106595 := by
    simpa [prefixWord, tailWord_3106595, baseEnd_3106595] using wordTrace_append hprefix tailTrace_3106595
  have hstable : (prefixWord ++ tailWord_3106595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106595).length < 2 ^ (prefixWord ++ tailWord_3106595).sum := by decide
  have hdescent : baseEnd_3106595 < baseStart_3106595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106610 : List Nat := [3, 2, 1, 1, 3, 2, 2, 1, 2, 5]
def baseStart_3106610 : Nat := 118140960795 + 3106610 * 2 ^ 59
def prefixEnd_3106610 : Nat := 4983230072969 + 3 ^ 40 * 3106610 * 2
def baseEnd_3106610 : Nat := 1063456090709463738525311

theorem tailTrace_3106610 : CollatzResearch.WordTrace tailWord_3106610 prefixEnd_3106610 1063456090709463738525311 := by
  unfold tailWord_3106610
  simp only [CollatzResearch.WordTrace]
  refine ⟨28326843818822502898133321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75538250183526674395022189 28326843818822502898133321)
  ·
    refine ⟨21245132864116877173599991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28326843818822502898133321 21245132864116877173599991)
    ·
      refine ⟨31867699296175315760399987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21245132864116877173599991 31867699296175315760399987)
      ·
        refine ⟨47801548944262973640599981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31867699296175315760399987 47801548944262973640599981)
        ·
          refine ⟨17925580854098615115224993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47801548944262973640599981 17925580854098615115224993)
          ·
            refine ⟨13444185640573961336418745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17925580854098615115224993 13444185640573961336418745)
            ·
              refine ⟨10083139230430471002314059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13444185640573961336418745 10083139230430471002314059)
              ·
                refine ⟨15124708845645706503471089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10083139230430471002314059 15124708845645706503471089)
                ·
                  refine ⟨11343531634234279877603317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15124708845645706503471089 11343531634234279877603317)
                  ·
                    refine ⟨1063456090709463738525311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11343531634234279877603317 1063456090709463738525311)
                    ·
                      rfl

theorem cell22_3106610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_3106610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106610 prefixEnd_3106610 := by exact prefixLift 3106610
  have htrace : WordTrace (prefixWord ++ tailWord_3106610) baseStart_3106610 baseEnd_3106610 := by
    simpa [prefixWord, tailWord_3106610, baseEnd_3106610] using wordTrace_append hprefix tailTrace_3106610
  have hstable : (prefixWord ++ tailWord_3106610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106610).length < 2 ^ (prefixWord ++ tailWord_3106610).sum := by decide
  have hdescent : baseEnd_3106610 < baseStart_3106610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106642 : List Nat := [3, 2, 2, 1, 1, 3, 2, 3, 1, 4]
def baseStart_3106642 : Nat := 118140960795 + 3106642 * 2 ^ 59
def prefixEnd_3106642 : Nat := 4983230072969 + 3 ^ 40 * 3106642 * 2
def baseEnd_3106642 : Nat := 1063467044963426321725213

theorem tailTrace_3106642 : CollatzResearch.WordTrace tailWord_3106642 prefixEnd_3106642 1063467044963426321725213 := by
  unfold tailWord_3106642
  simp only [CollatzResearch.WordTrace]
  refine ⟨28327135602793520264424545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75539028274116054038465453 28327135602793520264424545)
  ·
    refine ⟨21245351702095140198318409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28327135602793520264424545 21245351702095140198318409)
    ·
      refine ⟨15934013776571355148738807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21245351702095140198318409 15934013776571355148738807)
      ·
        refine ⟨23901020664857032723108211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15934013776571355148738807 23901020664857032723108211)
        ·
          refine ⟨35851530997285549084662317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23901020664857032723108211 35851530997285549084662317)
          ·
            refine ⟨13444324123982080906748369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35851530997285549084662317 13444324123982080906748369)
            ·
              refine ⟨10083243092986560680061277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13444324123982080906748369 10083243092986560680061277)
              ·
                refine ⟨3781216159869960255022979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10083243092986560680061277 3781216159869960255022979)
                ·
                  refine ⟨5671824239804940382534469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3781216159869960255022979 5671824239804940382534469)
                  ·
                    refine ⟨1063467044963426321725213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5671824239804940382534469 1063467044963426321725213)
                    ·
                      rfl

theorem cell22_3106642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_3106642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106642 prefixEnd_3106642 := by exact prefixLift 3106642
  have htrace : WordTrace (prefixWord ++ tailWord_3106642) baseStart_3106642 baseEnd_3106642 := by
    simpa [prefixWord, tailWord_3106642, baseEnd_3106642] using wordTrace_append hprefix tailTrace_3106642
  have hstable : (prefixWord ++ tailWord_3106642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106642).length < 2 ^ (prefixWord ++ tailWord_3106642).sum := by decide
  have hdescent : baseEnd_3106642 < baseStart_3106642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106689 : List Nat := [1, 2, 4, 4, 1, 1, 1, 2, 1, 5]
def baseStart_3106689 : Nat := 118140960795 + 3106689 * 2 ^ 59
def prefixEnd_3106689 : Nat := 4983230072969 + 3 ^ 40 * 3106689 * 2
def baseEnd_3106689 : Nat := 1063483134023933865800069

theorem tailTrace_3106689 : CollatzResearch.WordTrace tailWord_3106689 prefixEnd_3106689 1063483134023933865800069 := by
  unfold tailWord_3106689
  simp only [CollatzResearch.WordTrace]
  refine ⟨113310256642003808084659121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75540171094669205389772747 113310256642003808084659121)
  ·
    refine ⟨84982692481502856063494341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113310256642003808084659121 84982692481502856063494341)
    ·
      refine ⟨15934254840281785511905189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84982692481502856063494341 15934254840281785511905189)
      ·
        refine ⟨2987672782552834783482223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15934254840281785511905189 2987672782552834783482223)
        ·
          refine ⟨4481509173829252175223335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2987672782552834783482223 4481509173829252175223335)
          ·
            refine ⟨6722263760743878262835003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4481509173829252175223335 6722263760743878262835003)
            ·
              refine ⟨10083395641115817394252505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6722263760743878262835003 10083395641115817394252505)
              ·
                refine ⟨7562546730836863045689379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10083395641115817394252505 7562546730836863045689379)
                ·
                  refine ⟨11343820096255294568534069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7562546730836863045689379 11343820096255294568534069)
                  ·
                    refine ⟨1063483134023933865800069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11343820096255294568534069 1063483134023933865800069)
                    ·
                      rfl

theorem cell22_3106689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_3106689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106689 prefixEnd_3106689 := by exact prefixLift 3106689
  have htrace : WordTrace (prefixWord ++ tailWord_3106689) baseStart_3106689 baseEnd_3106689 := by
    simpa [prefixWord, tailWord_3106689, baseEnd_3106689] using wordTrace_append hprefix tailTrace_3106689
  have hstable : (prefixWord ++ tailWord_3106689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106689).length < 2 ^ (prefixWord ++ tailWord_3106689).sum := by decide
  have hdescent : baseEnd_3106689 < baseStart_3106689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106702 : List Nat := [4, 1, 1, 5, 1, 10]
def baseStart_3106702 : Nat := 118140960795 + 3106702 * 2 ^ 59
def prefixEnd_3106702 : Nat := 4983230072969 + 3 ^ 40 * 3106702 * 2
def baseEnd_3106702 : Nat := 13129476348019829200309

theorem tailTrace_3106702 : CollatzResearch.WordTrace tailWord_3106702 prefixEnd_3106702 13129476348019829200309 := by
  unfold tailWord_3106702
  simp only [CollatzResearch.WordTrace]
  refine ⟨14163841348869588913110295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75540487193971140869921573 14163841348869588913110295)
  ·
    refine ⟨21245762023304383369665443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14163841348869588913110295 21245762023304383369665443)
    ·
      refine ⟨31868643034956575054498165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21245762023304383369665443 31868643034956575054498165)
      ·
        refine ⟨2987685284527178911359203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31868643034956575054498165 2987685284527178911359203)
        ·
          refine ⟨4481527926790768367038805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2987685284527178911359203 4481527926790768367038805)
          ·
            refine ⟨13129476348019829200309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4481527926790768367038805 13129476348019829200309)
            ·
              rfl

theorem cell22_3106702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 10].length) (baseStart_3106702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106702 prefixEnd_3106702 := by exact prefixLift 3106702
  have htrace : WordTrace (prefixWord ++ tailWord_3106702) baseStart_3106702 baseEnd_3106702 := by
    simpa [prefixWord, tailWord_3106702, baseEnd_3106702] using wordTrace_append hprefix tailTrace_3106702
  have hstable : (prefixWord ++ tailWord_3106702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106702).length < 2 ^ (prefixWord ++ tailWord_3106702).sum := by decide
  have hdescent : baseEnd_3106702 < baseStart_3106702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106706 : List Nat := [3, 2, 3, 2, 1, 2, 2, 2, 2, 3]
def baseStart_3106706 : Nat := 118140960795 + 3106706 * 2 ^ 59
def prefixEnd_3106706 : Nat := 4983230072969 + 3 ^ 40 * 3106706 * 2
def baseEnd_3106706 : Nat := 1063488953471351488125017

theorem tailTrace_3106706 : CollatzResearch.WordTrace tailWord_3106706 prefixEnd_3106706 1063488953471351488125017 := by
  unfold tailWord_3106706
  simp only [CollatzResearch.WordTrace]
  refine ⟨28327719170735554997006993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75540584455294813325351981 28327719170735554997006993)
  ·
    refine ⟨21245789378051666247755245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28327719170735554997006993 21245789378051666247755245)
    ·
      refine ⟨7967171016769374842908217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21245789378051666247755245 7967171016769374842908217)
      ·
        refine ⟨5975378262577031132181163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7967171016769374842908217 5975378262577031132181163)
        ·
          refine ⟨8963067393865546698271745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5975378262577031132181163 8963067393865546698271745)
          ·
            refine ⟨6722300545399160023703809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8963067393865546698271745 6722300545399160023703809)
            ·
              refine ⟨5041725409049370017777857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6722300545399160023703809 5041725409049370017777857)
              ·
                refine ⟨3781294056787027513333393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5041725409049370017777857 3781294056787027513333393)
                ·
                  refine ⟨2835970542590270635000045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3781294056787027513333393 2835970542590270635000045)
                  ·
                    refine ⟨1063488953471351488125017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2835970542590270635000045 1063488953471351488125017)
                    ·
                      rfl

theorem cell22_3106706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_3106706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106706 prefixEnd_3106706 := by exact prefixLift 3106706
  have htrace : WordTrace (prefixWord ++ tailWord_3106706) baseStart_3106706 baseEnd_3106706 := by
    simpa [prefixWord, tailWord_3106706, baseEnd_3106706] using wordTrace_append hprefix tailTrace_3106706
  have hstable : (prefixWord ++ tailWord_3106706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106706).length < 2 ^ (prefixWord ++ tailWord_3106706).sum := by decide
  have hdescent : baseEnd_3106706 < baseStart_3106706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106719 : List Nat := [1, 1, 2, 5, 4, 1, 1, 7]
def baseStart_3106719 : Nat := 118140960795 + 3106719 * 2 ^ 59
def prefixEnd_3106719 : Nat := 4983230072969 + 3 ^ 40 * 3106719 * 2
def baseEnd_3106719 : Nat := 118165933737447087505553

theorem tailTrace_3106719 : CollatzResearch.WordTrace tailWord_3106719 prefixEnd_3106719 118165933737447087505553 := by
  unfold tailWord_3106719
  simp only [CollatzResearch.WordTrace]
  refine ⟨113311350831895123208251211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75540900554596748805500807 113311350831895123208251211)
  ·
    refine ⟨169967026247842684812376817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113311350831895123208251211 169967026247842684812376817)
    ·
      refine ⟨127475269685882013609282613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169967026247842684812376817 127475269685882013609282613)
      ·
        refine ⟨11950806533051438775870245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127475269685882013609282613 11950806533051438775870245)
        ·
          refine ⟨2240776224947144770475671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11950806533051438775870245 2240776224947144770475671)
          ·
            refine ⟨3361164337420717155713507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2240776224947144770475671 3361164337420717155713507)
            ·
              refine ⟨5041746506131075733570261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3361164337420717155713507 5041746506131075733570261)
              ·
                refine ⟨118165933737447087505553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5041746506131075733570261 118165933737447087505553)
                ·
                  rfl

theorem cell22_3106719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 7].length) (baseStart_3106719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106719 prefixEnd_3106719 := by exact prefixLift 3106719
  have htrace : WordTrace (prefixWord ++ tailWord_3106719) baseStart_3106719 baseEnd_3106719 := by
    simpa [prefixWord, tailWord_3106719, baseEnd_3106719] using wordTrace_append hprefix tailTrace_3106719
  have hstable : (prefixWord ++ tailWord_3106719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106719).length < 2 ^ (prefixWord ++ tailWord_3106719).sum := by decide
  have hdescent : baseEnd_3106719 < baseStart_3106719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106745 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 1, 7]
def baseStart_3106745 : Nat := 118140960795 + 3106745 * 2 ^ 59
def prefixEnd_3106745 : Nat := 4983230072969 + 3 ^ 40 * 3106745 * 2
def baseEnd_3106745 : Nat := 1063502303968368386399897

theorem tailTrace_3106745 : CollatzResearch.WordTrace tailWord_3106745 prefixEnd_3106745 1063502303968368386399897 := by
  unfold tailWord_3106745
  simp only [CollatzResearch.WordTrace]
  refine ⟨113312299129800929648697689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75541532753200619765798459 113312299129800929648697689)
  ·
    refine ⟨84984224347350697236523267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113312299129800929648697689 84984224347350697236523267)
    ·
      refine ⟨127476336521026045854784901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84984224347350697236523267 127476336521026045854784901)
      ·
        refine ⟨23901813097692383597772169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127476336521026045854784901 23901813097692383597772169)
        ·
          refine ⟨17926359823269287698329127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23901813097692383597772169 17926359823269287698329127)
          ·
            refine ⟨26889539734903931547493691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17926359823269287698329127 26889539734903931547493691)
            ·
              refine ⟨40334309602355897321240537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26889539734903931547493691 40334309602355897321240537)
              ·
                refine ⟨30250732201766922990930403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40334309602355897321240537 30250732201766922990930403)
                ·
                  refine ⟨45376098302650384486395605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30250732201766922990930403 45376098302650384486395605)
                  ·
                    refine ⟨1063502303968368386399897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45376098302650384486395605 1063502303968368386399897)
                    ·
                      rfl

theorem cell22_3106745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 7].length) (baseStart_3106745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106745 prefixEnd_3106745 := by exact prefixLift 3106745
  have htrace : WordTrace (prefixWord ++ tailWord_3106745) baseStart_3106745 baseEnd_3106745 := by
    simpa [prefixWord, tailWord_3106745, baseEnd_3106745] using wordTrace_append hprefix tailTrace_3106745
  have hstable : (prefixWord ++ tailWord_3106745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106745).length < 2 ^ (prefixWord ++ tailWord_3106745).sum := by decide
  have hdescent : baseEnd_3106745 < baseStart_3106745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106764 : List Nat := [2, 2, 1, 4, 1, 4, 1, 2, 5]
def baseStart_3106764 : Nat := 118140960795 + 3106764 * 2 ^ 59
def prefixEnd_3106764 : Nat := 4983230072969 + 3 ^ 40 * 3106764 * 2
def baseEnd_3106764 : Nat := 354502936018886223391613

theorem tailTrace_3106764 : CollatzResearch.WordTrace tailWord_3106764 prefixEnd_3106764 354502936018886223391613 := by
  unfold tailWord_3106764
  simp only [CollatzResearch.WordTrace]
  refine ⟨56656496058366047946819673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75541994744488063929092897 56656496058366047946819673)
  ·
    refine ⟨42492372043774535960114755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56656496058366047946819673 42492372043774535960114755)
    ·
      refine ⟨63738558065661803940172133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42492372043774535960114755 63738558065661803940172133)
      ·
        refine ⟨11950979637311588238782275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63738558065661803940172133 11950979637311588238782275)
        ·
          refine ⟨17926469455967382358173413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11950979637311588238782275 17926469455967382358173413)
          ·
            refine ⟨3361213022993884192157515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17926469455967382358173413 3361213022993884192157515)
            ·
              refine ⟨5041819534490826288236273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3361213022993884192157515 5041819534490826288236273)
              ·
                refine ⟨3781364650868119716177205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5041819534490826288236273 3781364650868119716177205)
                ·
                  refine ⟨354502936018886223391613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3781364650868119716177205 354502936018886223391613)
                  ·
                    rfl

theorem cell22_3106764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 5].length) (baseStart_3106764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106764 prefixEnd_3106764 := by exact prefixLift 3106764
  have htrace : WordTrace (prefixWord ++ tailWord_3106764) baseStart_3106764 baseEnd_3106764 := by
    simpa [prefixWord, tailWord_3106764, baseEnd_3106764] using wordTrace_append hprefix tailTrace_3106764
  have hstable : (prefixWord ++ tailWord_3106764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106764).length < 2 ^ (prefixWord ++ tailWord_3106764).sum := by decide
  have hdescent : baseEnd_3106764 < baseStart_3106764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106781 : List Nat := [1, 4, 3, 1, 3, 1, 3, 1, 5]
def baseStart_3106781 : Nat := 118140960795 + 3106781 * 2 ^ 59
def prefixEnd_3106781 : Nat := 4983230072969 + 3 ^ 40 * 3106781 * 2
def baseEnd_3106781 : Nat := 354504875834692097499929

theorem tailTrace_3106781 : CollatzResearch.WordTrace tailWord_3106781 prefixEnd_3106781 354504875834692097499929 := by
  unfold tailWord_3106781
  simp only [CollatzResearch.WordTrace]
  refine ⟨113313612157670507797008197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75542408105113671864672131 113313612157670507797008197)
  ·
    refine ⟨21246302279563220211939037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113313612157670507797008197 21246302279563220211939037)
    ·
      refine ⟨7967363354836207579477139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21246302279563220211939037 7967363354836207579477139)
      ·
        refine ⟨11951045032254311369215709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7967363354836207579477139 11951045032254311369215709)
        ·
          refine ⟨4481641887095366763455891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11951045032254311369215709 4481641887095366763455891)
          ·
            refine ⟨6722462830643050145183837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4481641887095366763455891 6722462830643050145183837)
            ·
              refine ⟨2520923561491143804443939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6722462830643050145183837 2520923561491143804443939)
              ·
                refine ⟨3781385342236715706665909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2520923561491143804443939 3781385342236715706665909)
                ·
                  refine ⟨354504875834692097499929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3781385342236715706665909 354504875834692097499929)
                  ·
                    rfl

theorem cell22_3106781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_3106781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106781 prefixEnd_3106781 := by exact prefixLift 3106781
  have htrace : WordTrace (prefixWord ++ tailWord_3106781) baseStart_3106781 baseEnd_3106781 := by
    simpa [prefixWord, tailWord_3106781, baseEnd_3106781] using wordTrace_append hprefix tailTrace_3106781
  have hstable : (prefixWord ++ tailWord_3106781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106781).length < 2 ^ (prefixWord ++ tailWord_3106781).sum := by decide
  have hdescent : baseEnd_3106781 < baseStart_3106781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106794 : List Nat := [3, 1, 3, 1, 2, 1, 4, 2, 1, 4]
def baseStart_3106794 : Nat := 118140960795 + 3106794 * 2 ^ 59
def prefixEnd_3106794 : Nat := 4983230072969 + 3 ^ 40 * 3106794 * 2
def baseEnd_3106794 : Nat := 1063519077669748591924747

theorem tailTrace_3106794 : CollatzResearch.WordTrace tailWord_3106794 prefixEnd_3106794 1063519077669748591924747 := by
  unfold tailWord_3106794
  simp only [CollatzResearch.WordTrace]
  refine ⟨28328521576655852754307859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75542724204415607344820957 28328521576655852754307859)
  ·
    refine ⟨42492782364983779131461789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28328521576655852754307859 42492782364983779131461789)
    ·
      refine ⟨15934793386868917174298171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42492782364983779131461789 15934793386868917174298171)
      ·
        refine ⟨23902190080303375761447257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15934793386868917174298171 23902190080303375761447257)
        ·
          refine ⟨17926642560227531821085443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23902190080303375761447257 17926642560227531821085443)
          ·
            refine ⟨26889963840341297731628165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17926642560227531821085443 26889963840341297731628165)
            ·
              refine ⟨5041868220063993324680281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26889963840341297731628165 5041868220063993324680281)
              ·
                refine ⟨3781401165047994993510211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5041868220063993324680281 3781401165047994993510211)
                ·
                  refine ⟨5672101747571992490265317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3781401165047994993510211 5672101747571992490265317)
                  ·
                    refine ⟨1063519077669748591924747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5672101747571992490265317 1063519077669748591924747)
                    ·
                      rfl

theorem cell22_3106794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_3106794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106794 prefixEnd_3106794 := by exact prefixLift 3106794
  have htrace : WordTrace (prefixWord ++ tailWord_3106794) baseStart_3106794 baseEnd_3106794 := by
    simpa [prefixWord, tailWord_3106794, baseEnd_3106794] using wordTrace_append hprefix tailTrace_3106794
  have hstable : (prefixWord ++ tailWord_3106794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106794).length < 2 ^ (prefixWord ++ tailWord_3106794).sum := by decide
  have hdescent : baseEnd_3106794 < baseStart_3106794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106809 : List Nat := [1, 2, 1, 3, 1, 4, 3, 3, 4]
def baseStart_3106809 : Nat := 118140960795 + 3106809 * 2 ^ 59
def prefixEnd_3106809 : Nat := 4983230072969 + 3 ^ 40 * 3106809 * 2
def baseEnd_3106809 : Nat := 354508070825431184266567

theorem tailTrace_3106809 : CollatzResearch.WordTrace tailWord_3106809 prefixEnd_3106809 354508070825431184266567 := by
  unfold tailWord_3106809
  simp only [CollatzResearch.WordTrace]
  refine ⟨113314633401569068579027481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75543088934379379052684987 113314633401569068579027481)
  ·
    refine ⟨84985975051176801434270611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113314633401569068579027481 84985975051176801434270611)
    ·
      refine ⟨127478962576765202151405917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84985975051176801434270611 127478962576765202151405917)
      ·
        refine ⟨47804610966286950806777219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127478962576765202151405917 47804610966286950806777219)
        ·
          refine ⟨71706916449430426210165829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47804610966286950806777219 71706916449430426210165829)
          ·
            refine ⟨13445046834268204914406093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71706916449430426210165829 13445046834268204914406093)
            ·
              refine ⟨5041892562850576842902285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13445046834268204914406093 5041892562850576842902285)
              ·
                refine ⟨1890709711068966316088357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5041892562850576842902285 1890709711068966316088357)
                ·
                  refine ⟨354508070825431184266567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1890709711068966316088357 354508070825431184266567)
                  ·
                    rfl

theorem cell22_3106809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 3, 4].length) (baseStart_3106809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106809 prefixEnd_3106809 := by exact prefixLift 3106809
  have htrace : WordTrace (prefixWord ++ tailWord_3106809) baseStart_3106809 baseEnd_3106809 := by
    simpa [prefixWord, tailWord_3106809, baseEnd_3106809] using wordTrace_append hprefix tailTrace_3106809
  have hstable : (prefixWord ++ tailWord_3106809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106809).length < 2 ^ (prefixWord ++ tailWord_3106809).sum := by decide
  have hdescent : baseEnd_3106809 < baseStart_3106809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106824 : List Nat := [2, 1, 3, 2, 1, 2, 2, 4, 2, 3]
def baseStart_3106824 : Nat := 118140960795 + 3106824 * 2 ^ 59
def prefixEnd_3106824 : Nat := 4983230072969 + 3 ^ 40 * 3106824 * 2
def baseEnd_3106824 : Nat := 1063529347282838513674655

theorem tailTrace_3106824 : CollatzResearch.WordTrace tailWord_3106824 prefixEnd_3106824 1063529347282838513674655 := by
  unfold tailWord_3106824
  simp only [CollatzResearch.WordTrace]
  refine ⟨56657590248257363070411763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75543453664343150760549017 56657590248257363070411763)
  ·
    refine ⟨84986385372386044605617645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56657590248257363070411763 84986385372386044605617645)
    ·
      refine ⟨31869894514644766727106617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84986385372386044605617645 31869894514644766727106617)
      ·
        refine ⟨23902420885983575045329963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31869894514644766727106617 23902420885983575045329963)
        ·
          refine ⟨35853631328975362567994945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23902420885983575045329963 35853631328975362567994945)
          ·
            refine ⟨26890223496731521925996209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35853631328975362567994945 26890223496731521925996209)
            ·
              refine ⟨20167667622548641444497157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26890223496731521925996209 20167667622548641444497157)
              ·
                refine ⟨3781437679227870270843217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20167667622548641444497157 3781437679227870270843217)
                ·
                  refine ⟨2836078259420902703132413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3781437679227870270843217 2836078259420902703132413)
                  ·
                    refine ⟨1063529347282838513674655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2836078259420902703132413 1063529347282838513674655)
                    ·
                      rfl

theorem cell22_3106824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_3106824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106824 prefixEnd_3106824 := by exact prefixLift 3106824
  have htrace : WordTrace (prefixWord ++ tailWord_3106824) baseStart_3106824 baseEnd_3106824 := by
    simpa [prefixWord, tailWord_3106824, baseEnd_3106824] using wordTrace_append hprefix tailTrace_3106824
  have hstable : (prefixWord ++ tailWord_3106824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106824).length < 2 ^ (prefixWord ++ tailWord_3106824).sum := by decide
  have hdescent : baseEnd_3106824 < baseStart_3106824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106826 : List Nat := [3, 1, 2, 2, 5, 1, 1, 1, 6]
def baseStart_3106826 : Nat := 118140960795 + 3106826 * 2 ^ 59
def prefixEnd_3106826 : Nat := 4983230072969 + 3 ^ 40 * 3106826 * 2
def baseEnd_3106826 : Nat := 354510010641237058374883

theorem tailTrace_3106826 : CollatzResearch.WordTrace tailWord_3106826 prefixEnd_3106826 354510010641237058374883 := by
  unfold tailWord_3106826
  simp only [CollatzResearch.WordTrace]
  refine ⟨28328813360626870120599083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75543502295004986988264221 28328813360626870120599083)
  ·
    refine ⟨42493220040940305180898625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28328813360626870120599083 42493220040940305180898625)
    ·
      refine ⟨31869915030705228885673969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42493220040940305180898625 31869915030705228885673969)
      ·
        refine ⟨23902436273028921664255477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31869915030705228885673969 23902436273028921664255477)
        ·
          refine ⟨2240853400596461406023951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23902436273028921664255477 2240853400596461406023951)
          ·
            refine ⟨3361280100894692109035927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2240853400596461406023951 3361280100894692109035927)
            ·
              refine ⟨5041920151342038163553891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3361280100894692109035927 5041920151342038163553891)
              ·
                refine ⟨7562880227013057245330837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5041920151342038163553891 7562880227013057245330837)
                ·
                  refine ⟨354510010641237058374883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7562880227013057245330837 354510010641237058374883)
                  ·
                    rfl

theorem cell22_3106826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 6].length) (baseStart_3106826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106826 prefixEnd_3106826 := by exact prefixLift 3106826
  have htrace : WordTrace (prefixWord ++ tailWord_3106826) baseStart_3106826 baseEnd_3106826 := by
    simpa [prefixWord, tailWord_3106826, baseEnd_3106826] using wordTrace_append hprefix tailTrace_3106826
  have hstable : (prefixWord ++ tailWord_3106826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106826).length < 2 ^ (prefixWord ++ tailWord_3106826).sum := by decide
  have hdescent : baseEnd_3106826 < baseStart_3106826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106929 : List Nat := [1, 2, 2, 2, 1, 1, 5, 3, 1, 4]
def baseStart_3106929 : Nat := 118140960795 + 3106929 * 2 ^ 59
def prefixEnd_3106929 : Nat := 4983230072969 + 3 ^ 40 * 3106929 * 2
def baseEnd_3106929 : Nat := 1063565290928653239799333

theorem tailTrace_3106929 : CollatzResearch.WordTrace tailWord_3106929 prefixEnd_3106929 1063565290928653239799333 := by
  unfold tailWord_3106929
  simp only [CollatzResearch.WordTrace]
  refine ⟨113319010161134329073395841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75546006774089552715597227 113319010161134329073395841)
  ·
    refine ⟨84989257620850746805046881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113319010161134329073395841 84989257620850746805046881)
    ·
      refine ⟨63741943215638060103785161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84989257620850746805046881 63741943215638060103785161)
      ·
        refine ⟨47806457411728545077838871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63741943215638060103785161 47806457411728545077838871)
        ·
          refine ⟨71709686117592817616758307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47806457411728545077838871 71709686117592817616758307)
          ·
            refine ⟨107564529176389226425137461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71709686117592817616758307 107564529176389226425137461)
            ·
              refine ⟨10084174610286489977356637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107564529176389226425137461 10084174610286489977356637)
              ·
                refine ⟨3781565478857433741508739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10084174610286489977356637 3781565478857433741508739)
                ·
                  refine ⟨5672348218286150612263109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3781565478857433741508739 5672348218286150612263109)
                  ·
                    refine ⟨1063565290928653239799333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5672348218286150612263109 1063565290928653239799333)
                    ·
                      rfl

theorem cell22_3106929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_3106929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106929 prefixEnd_3106929 := by exact prefixLift 3106929
  have htrace : WordTrace (prefixWord ++ tailWord_3106929) baseStart_3106929 baseEnd_3106929 := by
    simpa [prefixWord, tailWord_3106929, baseEnd_3106929] using wordTrace_append hprefix tailTrace_3106929
  have hstable : (prefixWord ++ tailWord_3106929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106929).length < 2 ^ (prefixWord ++ tailWord_3106929).sum := by decide
  have hdescent : baseEnd_3106929 < baseStart_3106929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106978 : List Nat := [3, 3, 1, 3, 1, 1, 3, 3, 4]
def baseStart_3106978 : Nat := 118140960795 + 3106978 * 2 ^ 59
def prefixEnd_3106978 : Nat := 4983230072969 + 3 ^ 40 * 3106978 * 2
def baseEnd_3106978 : Nat := 354527354876677815108061

theorem tailTrace_3106978 : CollatzResearch.WordTrace tailWord_3106978 prefixEnd_3106978 354527354876677815108061 := by
  unfold tailWord_3106978
  simp only [CollatzResearch.WordTrace]
  refine ⟨28330199334489202610482397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75547198225304540294619725 28330199334489202610482397)
  ·
    refine ⟨10623824750433450978930899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28330199334489202610482397 10623824750433450978930899)
    ·
      refine ⟨15935737125650176468396349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10623824750433450978930899 15935737125650176468396349)
      ·
        refine ⟨5975901422118816175648631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15935737125650176468396349 5975901422118816175648631)
        ·
          refine ⟨8963852133178224263472947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5975901422118816175648631 8963852133178224263472947)
          ·
            refine ⟨13445778199767336395209421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8963852133178224263472947 13445778199767336395209421)
            ·
              refine ⟨5042166824912751148203533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13445778199767336395209421 5042166824912751148203533)
              ·
                refine ⟨1890812559342281680576325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5042166824912751148203533 1890812559342281680576325)
                ·
                  refine ⟨354527354876677815108061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1890812559342281680576325 354527354876677815108061)
                  ·
                    rfl

theorem cell22_3106978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_3106978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106978 prefixEnd_3106978 := by exact prefixLift 3106978
  have htrace : WordTrace (prefixWord ++ tailWord_3106978) baseStart_3106978 baseEnd_3106978 := by
    simpa [prefixWord, tailWord_3106978, baseEnd_3106978] using wordTrace_append hprefix tailTrace_3106978
  have hstable : (prefixWord ++ tailWord_3106978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106978).length < 2 ^ (prefixWord ++ tailWord_3106978).sum := by decide
  have hdescent : baseEnd_3106978 < baseStart_3106978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3106989 : List Nat := [1, 5, 2, 1, 2, 1, 10]
def baseStart_3106989 : Nat := 118140960795 + 3106989 * 2 ^ 59
def prefixEnd_3106989 : Nat := 4983230072969 + 3 ^ 40 * 3106989 * 2
def baseEnd_3106989 : Nat := 39392067783512336418487

theorem tailTrace_3106989 : CollatzResearch.WordTrace tailWord_3106989 prefixEnd_3106989 39392067783512336418487 := by
  unfold tailWord_3106989
  simp only [CollatzResearch.WordTrace]
  refine ⟨113321198540916959320580021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75547465693944639547053347 113321198540916959320580021)
  ·
    refine ⟨10623862363210964936304377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113321198540916959320580021 10623862363210964936304377)
    ·
      refine ⟨7967896772408223702228283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10623862363210964936304377 7967896772408223702228283)
      ·
        refine ⟨11951845158612335553342425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7967896772408223702228283 11951845158612335553342425)
        ·
          refine ⟨8963883868959251665006819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11951845158612335553342425 8963883868959251665006819)
          ·
            refine ⟨13445825803438877497510229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8963883868959251665006819 13445825803438877497510229)
            ·
              refine ⟨39392067783512336418487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13445825803438877497510229 39392067783512336418487)
              ·
                rfl

theorem cell22_3106989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 10].length) (baseStart_3106989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3106989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3106989 prefixEnd_3106989 := by exact prefixLift 3106989
  have htrace : WordTrace (prefixWord ++ tailWord_3106989) baseStart_3106989 baseEnd_3106989 := by
    simpa [prefixWord, tailWord_3106989, baseEnd_3106989] using wordTrace_append hprefix tailTrace_3106989
  have hstable : (prefixWord ++ tailWord_3106989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3106989).length < 2 ^ (prefixWord ++ tailWord_3106989).sum := by decide
  have hdescent : baseEnd_3106989 < baseStart_3106989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3106989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107006 : List Nat := [4, 2, 1, 1, 4, 1, 2, 7]
def baseStart_3107006 : Nat := 118140960795 + 3107006 * 2 ^ 59
def prefixEnd_3107006 : Nat := 4983230072969 + 3 ^ 40 * 3107006 * 2
def baseEnd_3107006 : Nat := 118176849955805633958233

theorem tailTrace_3107006 : CollatzResearch.WordTrace tailWord_3107006 prefixEnd_3107006 118176849955805633958233 := by
  unfold tailWord_3107006
  simp only [CollatzResearch.WordTrace]
  refine ⟨14165227322731921402993609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75547879054570247482632581 14165227322731921402993609)
  ·
    refine ⟨10623920492048941052245207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14165227322731921402993609 10623920492048941052245207)
    ·
      refine ⟨15935880738073411578367811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10623920492048941052245207 15935880738073411578367811)
      ·
        refine ⟨23903821107110117367551717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15935880738073411578367811 23903821107110117367551717)
        ·
          refine ⟨4481966457583147006415947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23903821107110117367551717 4481966457583147006415947)
          ·
            refine ⟨6722949686374720509623921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4481966457583147006415947 6722949686374720509623921)
            ·
              refine ⟨5042212264781040382217941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6722949686374720509623921 5042212264781040382217941)
              ·
                refine ⟨118176849955805633958233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5042212264781040382217941 118176849955805633958233)
                ·
                  rfl

theorem cell22_3107006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 7].length) (baseStart_3107006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107006 prefixEnd_3107006 := by exact prefixLift 3107006
  have htrace : WordTrace (prefixWord ++ tailWord_3107006) baseStart_3107006 baseEnd_3107006 := by
    simpa [prefixWord, tailWord_3107006, baseEnd_3107006] using wordTrace_append hprefix tailTrace_3107006
  have hstable : (prefixWord ++ tailWord_3107006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107006).length < 2 ^ (prefixWord ++ tailWord_3107006).sum := by decide
  have hdescent : baseEnd_3107006 < baseStart_3107006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107017 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 9]
def baseStart_3107017 : Nat := 118140960795 + 3107017 * 2 ^ 59
def prefixEnd_3107017 : Nat := 4983230072969 + 3 ^ 40 * 3107017 * 2
def baseEnd_3107017 : Nat := 354531805042350114533021

theorem tailTrace_3107017 : CollatzResearch.WordTrace tailWord_3107017 prefixEnd_3107017 354531805042350114533021 := by
  unfold tailWord_3107017
  simp only [CollatzResearch.WordTrace]
  refine ⟨113322219784815520102599305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75548146523210346735066203 113322219784815520102599305)
  ·
    refine ⟨84991664838611640076949479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113322219784815520102599305 84991664838611640076949479)
    ·
      refine ⟨127487497257917460115424219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84991664838611640076949479 127487497257917460115424219)
      ·
        refine ⟨191231245886876190173136329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127487497257917460115424219 191231245886876190173136329)
        ·
          refine ⟨143423434415157142629852247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191231245886876190173136329 143423434415157142629852247)
          ·
            refine ⟨215135151622735713944778371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143423434415157142629852247 215135151622735713944778371)
            ·
              refine ⟨322702727434103570917167557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215135151622735713944778371 322702727434103570917167557)
              ·
                refine ⟨60506761393894419546968917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 322702727434103570917167557 60506761393894419546968917)
                ·
                  refine ⟨354531805042350114533021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60506761393894419546968917 354531805042350114533021)
                  ·
                    rfl

theorem cell22_3107017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 9].length) (baseStart_3107017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107017 prefixEnd_3107017 := by exact prefixLift 3107017
  have htrace : WordTrace (prefixWord ++ tailWord_3107017) baseStart_3107017 baseEnd_3107017 := by
    simpa [prefixWord, tailWord_3107017, baseEnd_3107017] using wordTrace_append hprefix tailTrace_3107017
  have hstable : (prefixWord ++ tailWord_3107017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107017).length < 2 ^ (prefixWord ++ tailWord_3107017).sum := by decide
  have hdescent : baseEnd_3107017 < baseStart_3107017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107055 : List Nat := [1, 1, 2, 1, 6, 1, 4, 2, 1, 3]
def baseStart_3107055 : Nat := 118140960795 + 3107055 * 2 ^ 59
def prefixEnd_3107055 : Nat := 4983230072969 + 3 ^ 40 * 3107055 * 2
def baseEnd_3107055 : Nat := 1063608423303630911148947

theorem tailTrace_3107055 : CollatzResearch.WordTrace tailWord_3107055 prefixEnd_3107055 1063608423303630911148947 := by
  unfold tailWord_3107055
  simp only [CollatzResearch.WordTrace]
  refine ⟨113323605758677852592482619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75549070505785235061655079 113323605758677852592482619)
  ·
    refine ⟨169985408638016778888723929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113323605758677852592482619 169985408638016778888723929)
    ·
      refine ⟨127489056478512584166542947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169985408638016778888723929 127489056478512584166542947)
      ·
        refine ⟨191233584717768876249814421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127489056478512584166542947 191233584717768876249814421)
        ·
          refine ⟨8964074283645416074210051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 191233584717768876249814421 8964074283645416074210051)
          ·
            refine ⟨13446111425468124111315077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8964074283645416074210051 13446111425468124111315077)
            ·
              refine ⟨2521145892275273270871577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13446111425468124111315077 2521145892275273270871577)
              ·
                refine ⟨1890859419206454953153683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2521145892275273270871577 1890859419206454953153683)
                ·
                  refine ⟨2836289128809682429730525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1890859419206454953153683 2836289128809682429730525)
                  ·
                    refine ⟨1063608423303630911148947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2836289128809682429730525 1063608423303630911148947)
                    ·
                      rfl

theorem cell22_3107055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 2, 1, 3].length) (baseStart_3107055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107055 prefixEnd_3107055 := by exact prefixLift 3107055
  have htrace : WordTrace (prefixWord ++ tailWord_3107055) baseStart_3107055 baseEnd_3107055 := by
    simpa [prefixWord, tailWord_3107055, baseEnd_3107055] using wordTrace_append hprefix tailTrace_3107055
  have hstable : (prefixWord ++ tailWord_3107055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107055).length < 2 ^ (prefixWord ++ tailWord_3107055).sum := by decide
  have hdescent : baseEnd_3107055 < baseStart_3107055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107098 : List Nat := [3, 1, 1, 3, 4, 1, 1, 3, 1, 4]
def baseStart_3107098 : Nat := 118140960795 + 3107098 * 2 ^ 59
def prefixEnd_3107098 : Nat := 4983230072969 + 3 ^ 40 * 3107098 * 2
def baseEnd_3107098 : Nat := 1063623143082393132323815

theorem tailTrace_3107098 : CollatzResearch.WordTrace tailWord_3107098 prefixEnd_3107098 1063623143082393132323815 := by
  unfold tailWord_3107098
  simp only [CollatzResearch.WordTrace]
  refine ⟨28331293524380517734074487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75550116065014713957531965 28331293524380517734074487)
  ·
    refine ⟨42496940286570776601111731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28331293524380517734074487 42496940286570776601111731)
    ·
      refine ⟨63745410429856164901667597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42496940286570776601111731 63745410429856164901667597)
      ·
        refine ⟨23904528911196061838125349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63745410429856164901667597 23904528911196061838125349)
        ·
          refine ⟨4482099170849261594648503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23904528911196061838125349 4482099170849261594648503)
          ·
            refine ⟨6723148756273892391972755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4482099170849261594648503 6723148756273892391972755)
            ·
              refine ⟨10084723134410838587959133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6723148756273892391972755 10084723134410838587959133)
              ·
                refine ⟨3781771175404064470484675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10084723134410838587959133 3781771175404064470484675)
                ·
                  refine ⟨5672656763106096705727013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3781771175404064470484675 5672656763106096705727013)
                  ·
                    refine ⟨1063623143082393132323815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5672656763106096705727013 1063623143082393132323815)
                    ·
                      rfl

theorem cell22_3107098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_3107098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107098 prefixEnd_3107098 := by exact prefixLift 3107098
  have htrace : WordTrace (prefixWord ++ tailWord_3107098) baseStart_3107098 baseEnd_3107098 := by
    simpa [prefixWord, tailWord_3107098, baseEnd_3107098] using wordTrace_append hprefix tailTrace_3107098
  have hstable : (prefixWord ++ tailWord_3107098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107098).length < 2 ^ (prefixWord ++ tailWord_3107098).sum := by decide
  have hdescent : baseEnd_3107098 < baseStart_3107098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107173 : List Nat := [1, 3, 1, 3, 1, 3, 3, 1, 3, 3]
def baseStart_3107173 : Nat := 118140960795 + 3107173 * 2 ^ 59
def prefixEnd_3107173 : Nat := 4983230072969 + 3 ^ 40 * 3107173 * 2
def baseEnd_3107173 : Nat := 1063648817115117936698585

theorem tailTrace_3107173 : CollatzResearch.WordTrace tailWord_3107173 prefixEnd_3107173 1063648817115117936698585 := by
  unfold tailWord_3107173
  simp only [CollatzResearch.WordTrace]
  refine ⟨113327909572250358745278173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75551939714833572496852115 113327909572250358745278173)
  ·
    refine ⟨42497966089593884529479315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113327909572250358745278173 42497966089593884529479315)
    ·
      refine ⟨63746949134390826794218973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42497966089593884529479315 63746949134390826794218973)
      ·
        refine ⟨23905105925396560047832115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63746949134390826794218973 23905105925396560047832115)
        ·
          refine ⟨35857658888094840071748173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23905105925396560047832115 35857658888094840071748173)
          ·
            refine ⟨13446622083035565026905565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35857658888094840071748173 13446622083035565026905565)
            ·
              refine ⟨5042483281138336885089587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13446622083035565026905565 5042483281138336885089587)
              ·
                refine ⟨7563724921707505327634381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5042483281138336885089587 7563724921707505327634381)
                ·
                  refine ⟨2836396845640314497862893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7563724921707505327634381 2836396845640314497862893)
                  ·
                    refine ⟨1063648817115117936698585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2836396845640314497862893 1063648817115117936698585)
                    ·
                      rfl

theorem cell22_3107173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 3, 3].length) (baseStart_3107173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107173 prefixEnd_3107173 := by exact prefixLift 3107173
  have htrace : WordTrace (prefixWord ++ tailWord_3107173) baseStart_3107173 baseEnd_3107173 := by
    simpa [prefixWord, tailWord_3107173, baseEnd_3107173] using wordTrace_append hprefix tailTrace_3107173
  have hstable : (prefixWord ++ tailWord_3107173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107173).length < 2 ^ (prefixWord ++ tailWord_3107173).sum := by decide
  have hdescent : baseEnd_3107173 < baseStart_3107173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107199 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 2, 8]
def baseStart_3107199 : Nat := 118140960795 + 3107199 * 2 ^ 59
def prefixEnd_3107199 : Nat := 4983230072969 + 3 ^ 40 * 3107199 * 2
def baseEnd_3107199 : Nat := 1063657717446462535548505

theorem tailTrace_3107199 : CollatzResearch.WordTrace tailWord_3107199 prefixEnd_3107199 1063657717446462535548505 := by
  unfold tailWord_3107199
  simp only [CollatzResearch.WordTrace]
  refine ⟨113328857870156165185724651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75552571913437443457149767 113328857870156165185724651)
  ·
    refine ⟨169993286805234247778586977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113328857870156165185724651 169993286805234247778586977)
    ·
      refine ⟨127494965103925685833940233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169993286805234247778586977 127494965103925685833940233)
      ·
        refine ⟨95621223827944264375455175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127494965103925685833940233 95621223827944264375455175)
        ·
          refine ⟨143431835741916396563182763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95621223827944264375455175 143431835741916396563182763)
          ·
            refine ⟨215147753612874594844774145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143431835741916396563182763 215147753612874594844774145)
            ·
              refine ⟨161360815209655946133580609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215147753612874594844774145 161360815209655946133580609)
              ·
                refine ⟨121020611407241959600185457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161360815209655946133580609 121020611407241959600185457)
                ·
                  refine ⟨90765458555431469700139093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121020611407241959600185457 90765458555431469700139093)
                  ·
                    refine ⟨1063657717446462535548505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90765458555431469700139093 1063657717446462535548505)
                    ·
                      rfl

theorem cell22_3107199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 8].length) (baseStart_3107199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107199 prefixEnd_3107199 := by exact prefixLift 3107199
  have htrace : WordTrace (prefixWord ++ tailWord_3107199) baseStart_3107199 baseEnd_3107199 := by
    simpa [prefixWord, tailWord_3107199, baseEnd_3107199] using wordTrace_append hprefix tailTrace_3107199
  have hstable : (prefixWord ++ tailWord_3107199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107199).length < 2 ^ (prefixWord ++ tailWord_3107199).sum := by decide
  have hdescent : baseEnd_3107199 < baseStart_3107199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107220 : List Nat := [2, 4, 2, 1, 3, 1, 2, 2, 5]
def baseStart_3107220 : Nat := 118140960795 + 3107220 * 2 ^ 59
def prefixEnd_3107220 : Nat := 4983230072969 + 3 ^ 40 * 3107220 * 2
def baseEnd_3107220 : Nat := 354554968725208493591147

theorem tailTrace_3107220 : CollatzResearch.WordTrace tailWord_3107220 prefixEnd_3107220 354554968725208493591147 := by
  unfold tailWord_3107220
  simp only [CollatzResearch.WordTrace]
  refine ⟨56664811901540042886119557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75553082535386723848159409 56664811901540042886119557)
  ·
    refine ⟨10624652231538758041147417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56664811901540042886119557 10624652231538758041147417)
    ·
      refine ⟨7968489173654068530860563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10624652231538758041147417 7968489173654068530860563)
      ·
        refine ⟨11952733760481102796290845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7968489173654068530860563 11952733760481102796290845)
        ·
          refine ⟨4482275160180413548609067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11952733760481102796290845 4482275160180413548609067)
          ·
            refine ⟨6723412740270620322913601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4482275160180413548609067 6723412740270620322913601)
            ·
              refine ⟨5042559555202965242185201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6723412740270620322913601 5042559555202965242185201)
              ·
                refine ⟨3781919666402223931638901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5042559555202965242185201 3781919666402223931638901)
                ·
                  refine ⟨354554968725208493591147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3781919666402223931638901 354554968725208493591147)
                  ·
                    rfl

theorem cell22_3107220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_3107220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107220 prefixEnd_3107220 := by exact prefixLift 3107220
  have htrace : WordTrace (prefixWord ++ tailWord_3107220) baseStart_3107220 baseEnd_3107220 := by
    simpa [prefixWord, tailWord_3107220, baseEnd_3107220] using wordTrace_append hprefix tailTrace_3107220
  have hstable : (prefixWord ++ tailWord_3107220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107220).length < 2 ^ (prefixWord ++ tailWord_3107220).sum := by decide
  have hdescent : baseEnd_3107220 < baseStart_3107220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107224 : List Nat := [2, 1, 2, 5, 1, 3, 2, 2, 1, 3]
def baseStart_3107224 : Nat := 118140960795 + 3107224 * 2 ^ 59
def prefixEnd_3107224 : Nat := 4983230072969 + 3 ^ 40 * 3107224 * 2
def baseEnd_3107224 : Nat := 1063666275457370803673429

theorem tailTrace_3107224 : CollatzResearch.WordTrace tailWord_3107224 prefixEnd_3107224 1063666275457370803673429 := by
  unfold tailWord_3107224
  simp only [CollatzResearch.WordTrace]
  refine ⟨56664884847532797227692363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75553179796710396303589817 56664884847532797227692363)
  ·
    refine ⟨84997327271299195841538545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56664884847532797227692363 84997327271299195841538545)
    ·
      refine ⟨63747995453474396881153909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84997327271299195841538545 63747995453474396881153909)
      ·
        refine ⟨5976374573763224707608179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63747995453474396881153909 5976374573763224707608179)
        ·
          refine ⟨8964561860644837061412269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5976374573763224707608179 8964561860644837061412269)
          ·
            refine ⟨3361710697741813898029601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8964561860644837061412269 3361710697741813898029601)
            ·
              refine ⟨2521283023306360423522201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3361710697741813898029601 2521283023306360423522201)
              ·
                refine ⟨1890962267479770317641651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2521283023306360423522201 1890962267479770317641651)
                ·
                  refine ⟨2836443401219655476462477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1890962267479770317641651 2836443401219655476462477)
                  ·
                    refine ⟨1063666275457370803673429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2836443401219655476462477 1063666275457370803673429)
                    ·
                      rfl

theorem cell22_3107224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 2, 1, 3].length) (baseStart_3107224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107224 prefixEnd_3107224 := by exact prefixLift 3107224
  have htrace : WordTrace (prefixWord ++ tailWord_3107224) baseStart_3107224 baseEnd_3107224 := by
    simpa [prefixWord, tailWord_3107224, baseEnd_3107224] using wordTrace_append hprefix tailTrace_3107224
  have hstable : (prefixWord ++ tailWord_3107224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107224).length < 2 ^ (prefixWord ++ tailWord_3107224).sum := by decide
  have hdescent : baseEnd_3107224 < baseStart_3107224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107231 : List Nat := [1, 1, 2, 5, 1, 1, 2, 3, 6]
def baseStart_3107231 : Nat := 118140960795 + 3107231 * 2 ^ 59
def prefixEnd_3107231 : Nat := 4983230072969 + 3 ^ 40 * 3107231 * 2
def baseEnd_3107231 : Nat := 354556223900141706249469

theorem tailTrace_3107231 : CollatzResearch.WordTrace tailWord_3107231 prefixEnd_3107231 354556223900141706249469 := by
  unfold tailWord_3107231
  simp only [CollatzResearch.WordTrace]
  refine ⟨113330025006040234650889547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75553350004026823100593031 113330025006040234650889547)
  ·
    refine ⟨169995037509060351976334321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113330025006040234650889547 169995037509060351976334321)
    ·
      refine ⟨127496278131795263982250741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169995037509060351976334321 127496278131795263982250741)
      ·
        refine ⟨11952776074855805998336007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127496278131795263982250741 11952776074855805998336007)
        ·
          refine ⟨17929164112283708997504011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11952776074855805998336007 17929164112283708997504011)
          ·
            refine ⟨26893746168425563496256017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17929164112283708997504011 26893746168425563496256017)
            ·
              refine ⟨20170309626319172622192013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26893746168425563496256017 20170309626319172622192013)
              ·
                refine ⟨7563866109869689733322005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20170309626319172622192013 7563866109869689733322005)
                ·
                  refine ⟨354556223900141706249469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7563866109869689733322005 354556223900141706249469)
                  ·
                    rfl

theorem cell22_3107231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 6].length) (baseStart_3107231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107231 prefixEnd_3107231 := by exact prefixLift 3107231
  have htrace : WordTrace (prefixWord ++ tailWord_3107231) baseStart_3107231 baseEnd_3107231 := by
    simpa [prefixWord, tailWord_3107231, baseEnd_3107231] using wordTrace_append hprefix tailTrace_3107231
  have hstable : (prefixWord ++ tailWord_3107231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107231).length < 2 ^ (prefixWord ++ tailWord_3107231).sum := by decide
  have hdescent : baseEnd_3107231 < baseStart_3107231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107308 : List Nat := [2, 2, 1, 1, 2, 1, 3, 4, 3, 3]
def baseStart_3107308 : Nat := 118140960795 + 3107308 * 2 ^ 59
def prefixEnd_3107308 : Nat := 4983230072969 + 3 ^ 40 * 3107308 * 2
def baseEnd_3107308 : Nat := 1063695030374022584573171

theorem tailTrace_3107308 : CollatzResearch.WordTrace tailWord_3107308 prefixEnd_3107308 1063695030374022584573171 := by
  unfold tailWord_3107308
  simp only [CollatzResearch.WordTrace]
  refine ⟨56666416713380638400721289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75555222284507517867628385 56666416713380638400721289)
  ·
    refine ⟨42499812535035478800540967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56666416713380638400721289 42499812535035478800540967)
    ·
      refine ⟨63749718802553218200811451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42499812535035478800540967 63749718802553218200811451)
      ·
        refine ⟨95624578203829827301217177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63749718802553218200811451 95624578203829827301217177)
        ·
          refine ⟨71718433652872370475912883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95624578203829827301217177 71718433652872370475912883)
          ·
            refine ⟨107577650479308555713869325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71718433652872370475912883 107577650479308555713869325)
            ·
              refine ⟨40341618929740708392700997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107577650479308555713869325 40341618929740708392700997)
              ·
                refine ⟨7564053549326382823631437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40341618929740708392700997 7564053549326382823631437)
                ·
                  refine ⟨2836520080997393558861789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7564053549326382823631437 2836520080997393558861789)
                  ·
                    refine ⟨1063695030374022584573171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2836520080997393558861789 1063695030374022584573171)
                    ·
                      rfl

theorem cell22_3107308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 3].length) (baseStart_3107308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107308 prefixEnd_3107308 := by exact prefixLift 3107308
  have htrace : WordTrace (prefixWord ++ tailWord_3107308) baseStart_3107308 baseEnd_3107308 := by
    simpa [prefixWord, tailWord_3107308, baseEnd_3107308] using wordTrace_append hprefix tailTrace_3107308
  have hstable : (prefixWord ++ tailWord_3107308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107308).length < 2 ^ (prefixWord ++ tailWord_3107308).sum := by decide
  have hdescent : baseEnd_3107308 < baseStart_3107308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107310 : List Nat := [4, 1, 2, 1, 2, 4, 2, 6]
def baseStart_3107310 : Nat := 118140960795 + 3107310 * 2 ^ 59
def prefixEnd_3107310 : Nat := 4983230072969 + 3 ^ 40 * 3107310 * 2
def baseEnd_3107310 : Nat := 118188412779432805113685

theorem tailTrace_3107310 : CollatzResearch.WordTrace tailWord_3107310 prefixEnd_3107310 118188412779432805113685 := by
  unfold tailWord_3107310
  simp only [CollatzResearch.WordTrace]
  refine ⟨14166613296594253892876923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75555270915169354095343589 14166613296594253892876923)
  ·
    refine ⟨21249919944891380839315385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14166613296594253892876923 21249919944891380839315385)
    ·
      refine ⟨15937439958668535629486539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21249919944891380839315385 15937439958668535629486539)
      ·
        refine ⟨23906159938002803444229809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15937439958668535629486539 23906159938002803444229809)
        ·
          refine ⟨17929619953502102583172357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23906159938002803444229809 17929619953502102583172357)
          ·
            refine ⟨3361803741281644234344817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17929619953502102583172357 3361803741281644234344817)
            ·
              refine ⟨2521352805961233175758613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3361803741281644234344817 2521352805961233175758613)
              ·
                refine ⟨118188412779432805113685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2521352805961233175758613 118188412779432805113685)
                ·
                  rfl

theorem cell22_3107310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 6].length) (baseStart_3107310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107310 prefixEnd_3107310 := by exact prefixLift 3107310
  have htrace : WordTrace (prefixWord ++ tailWord_3107310) baseStart_3107310 baseEnd_3107310 := by
    simpa [prefixWord, tailWord_3107310, baseEnd_3107310] using wordTrace_append hprefix tailTrace_3107310
  have hstable : (prefixWord ++ tailWord_3107310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107310).length < 2 ^ (prefixWord ++ tailWord_3107310).sum := by decide
  have hdescent : baseEnd_3107310 < baseStart_3107310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107321 : List Nat := [1, 2, 1, 3, 1, 2, 3, 2, 7]
def baseStart_3107321 : Nat := 118140960795 + 3107321 * 2 ^ 59
def prefixEnd_3107321 : Nat := 4983230072969 + 3 ^ 40 * 3107321 * 2
def baseEnd_3107321 : Nat := 354566493513231627999377

theorem tailTrace_3107321 : CollatzResearch.WordTrace tailWord_3107321 prefixEnd_3107321 354566493513231627999377 := by
  unfold tailWord_3107321
  simp only [CollatzResearch.WordTrace]
  refine ⟨113333307575714180021665817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75555538383809453347777211 113333307575714180021665817)
  ·
    refine ⟨84999980681785635016249363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113333307575714180021665817 84999980681785635016249363)
    ·
      refine ⟨127499971022678452524374045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84999980681785635016249363 127499971022678452524374045)
      ·
        refine ⟨47812489133504419696640267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127499971022678452524374045 47812489133504419696640267)
        ·
          refine ⟨71718733700256629544960401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47812489133504419696640267 71718733700256629544960401)
          ·
            refine ⟨53789050275192472158720301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71718733700256629544960401 53789050275192472158720301)
            ·
              refine ⟨20170893853197177059520113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53789050275192472158720301 20170893853197177059520113)
              ·
                refine ⟨15128170389897882794640085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20170893853197177059520113 15128170389897882794640085)
                ·
                  refine ⟨354566493513231627999377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15128170389897882794640085 354566493513231627999377)
                  ·
                    rfl

theorem cell22_3107321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 7].length) (baseStart_3107321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107321 prefixEnd_3107321 := by exact prefixLift 3107321
  have htrace : WordTrace (prefixWord ++ tailWord_3107321) baseStart_3107321 baseEnd_3107321 := by
    simpa [prefixWord, tailWord_3107321, baseEnd_3107321] using wordTrace_append hprefix tailTrace_3107321
  have hstable : (prefixWord ++ tailWord_3107321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107321).length < 2 ^ (prefixWord ++ tailWord_3107321).sum := by decide
  have hdescent : baseEnd_3107321 < baseStart_3107321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107338 : List Nat := [3, 1, 2, 2, 2, 1, 2, 4, 5]
def baseStart_3107338 : Nat := 118140960795 + 3107338 * 2 ^ 59
def prefixEnd_3107338 : Nat := 4983230072969 + 3 ^ 40 * 3107338 * 2
def baseEnd_3107338 : Nat := 354568433329037502107693

theorem tailTrace_3107338 : CollatzResearch.WordTrace tailWord_3107338 prefixEnd_3107338 354568433329037502107693 := by
  unfold tailWord_3107338
  simp only [CollatzResearch.WordTrace]
  refine ⟨28333481904163147981258667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75555951744435061283356445 28333481904163147981258667)
  ·
    refine ⟨42500222856244721971888001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28333481904163147981258667 42500222856244721971888001)
    ·
      refine ⟨31875167142183541478916001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42500222856244721971888001 31875167142183541478916001)
      ·
        refine ⟨23906375356637656109187001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31875167142183541478916001 23906375356637656109187001)
        ·
          refine ⟨17929781517478242081890251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23906375356637656109187001 17929781517478242081890251)
          ·
            refine ⟨26894672276217363122835377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17929781517478242081890251 26894672276217363122835377)
            ·
              refine ⟨20171004207163022342126533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26894672276217363122835377 20171004207163022342126533)
              ·
                refine ⟨3782063288843066689148725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20171004207163022342126533 3782063288843066689148725)
                ·
                  refine ⟨354568433329037502107693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3782063288843066689148725 354568433329037502107693)
                  ·
                    rfl

theorem cell22_3107338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 5].length) (baseStart_3107338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107338 prefixEnd_3107338 := by exact prefixLift 3107338
  have htrace : WordTrace (prefixWord ++ tailWord_3107338) baseStart_3107338 baseEnd_3107338 := by
    simpa [prefixWord, tailWord_3107338, baseEnd_3107338] using wordTrace_append hprefix tailTrace_3107338
  have hstable : (prefixWord ++ tailWord_3107338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107338).length < 2 ^ (prefixWord ++ tailWord_3107338).sum := by decide
  have hdescent : baseEnd_3107338 < baseStart_3107338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107342 : List Nat := [4, 1, 1, 2, 3, 3, 1, 1, 3, 3]
def baseStart_3107342 : Nat := 118140960795 + 3107342 * 2 ^ 59
def prefixEnd_3107342 : Nat := 4983230072969 + 3 ^ 40 * 3107342 * 2
def baseEnd_3107342 : Nat := 1063706669268857829223067

theorem tailTrace_3107342 : CollatzResearch.WordTrace tailWord_3107342 prefixEnd_3107342 1063706669268857829223067 := by
  unfold tailWord_3107342
  simp only [CollatzResearch.WordTrace]
  refine ⟨14166759188579762576022535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75556049005758733738786853 14166759188579762576022535)
  ·
    refine ⟨21250138782869643864033803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14166759188579762576022535 21250138782869643864033803)
    ·
      refine ⟨31875208174304465796050705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21250138782869643864033803 31875208174304465796050705)
      ·
        refine ⟨23906406130728349347038029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31875208174304465796050705 23906406130728349347038029)
        ·
          refine ⟨8964902299023131005139261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23906406130728349347038029 8964902299023131005139261)
          ·
            refine ⟨3361838362133674126927223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8964902299023131005139261 3361838362133674126927223)
            ·
              refine ⟨5042757543200511190390835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3361838362133674126927223 5042757543200511190390835)
              ·
                refine ⟨7564136314800766785586253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5042757543200511190390835 7564136314800766785586253)
                ·
                  refine ⟨2836551118050287544594845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7564136314800766785586253 2836551118050287544594845)
                  ·
                    refine ⟨1063706669268857829223067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2836551118050287544594845 1063706669268857829223067)
                    ·
                      rfl

theorem cell22_3107342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_3107342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107342 prefixEnd_3107342 := by exact prefixLift 3107342
  have htrace : WordTrace (prefixWord ++ tailWord_3107342) baseStart_3107342 baseEnd_3107342 := by
    simpa [prefixWord, tailWord_3107342, baseEnd_3107342] using wordTrace_append hprefix tailTrace_3107342
  have hstable : (prefixWord ++ tailWord_3107342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107342).length < 2 ^ (prefixWord ++ tailWord_3107342).sum := by decide
  have hdescent : baseEnd_3107342 < baseStart_3107342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107413 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 4, 4]
def baseStart_3107413 : Nat := 118140960795 + 3107413 * 2 ^ 59
def prefixEnd_3107413 : Nat := 4983230072969 + 3 ^ 40 * 3107413 * 2
def baseEnd_3107413 : Nat := 1063730974019837310697849

theorem tailTrace_3107413 : CollatzResearch.WordTrace tailWord_3107413 prefixEnd_3107413 1063730974019837310697849 := by
  unfold tailWord_3107413
  simp only [CollatzResearch.WordTrace]
  refine ⟨113336663091380879734014893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75557775394253919822676595 113336663091380879734014893)
  ·
    refine ⟨42501248659267829900255585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113336663091380879734014893 42501248659267829900255585)
    ·
      refine ⟨31875936494450872425191689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42501248659267829900255585 31875936494450872425191689)
      ·
        refine ⟨23906952370838154318893767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31875936494450872425191689 23906952370838154318893767)
        ·
          refine ⟨35860428556257231478340651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23906952370838154318893767 35860428556257231478340651)
          ·
            refine ⟨53790642834385847217510977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35860428556257231478340651 53790642834385847217510977)
            ·
              refine ⟨40342982125789385413133233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53790642834385847217510977 40342982125789385413133233)
              ·
                refine ⟨30257236594342039059849925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40342982125789385413133233 30257236594342039059849925)
                ·
                  refine ⟨5673231861439132323721861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30257236594342039059849925 5673231861439132323721861)
                  ·
                    refine ⟨1063730974019837310697849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5673231861439132323721861 1063730974019837310697849)
                    ·
                      rfl

theorem cell22_3107413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_3107413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107413 prefixEnd_3107413 := by exact prefixLift 3107413
  have htrace : WordTrace (prefixWord ++ tailWord_3107413) baseStart_3107413 baseEnd_3107413 := by
    simpa [prefixWord, tailWord_3107413, baseEnd_3107413] using wordTrace_append hprefix tailTrace_3107413
  have hstable : (prefixWord ++ tailWord_3107413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107413).length < 2 ^ (prefixWord ++ tailWord_3107413).sum := by decide
  have hdescent : baseEnd_3107413 < baseStart_3107413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107415 : List Nat := [1, 1, 3, 2, 2, 2, 1, 5, 2, 3]
def baseStart_3107415 : Nat := 118140960795 + 3107415 * 2 ^ 59
def prefixEnd_3107415 : Nat := 4983230072969 + 3 ^ 40 * 3107415 * 2
def baseEnd_3107415 : Nat := 1063731658660709972147843

theorem tailTrace_3107415 : CollatzResearch.WordTrace tailWord_3107415 prefixEnd_3107415 1063731658660709972147843 := by
  unfold tailWord_3107415
  simp only [CollatzResearch.WordTrace]
  refine ⟨113336736037373634075587699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75557824024915756050391799 113336736037373634075587699)
  ·
    refine ⟨170005104056060451113381549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113336736037373634075587699 170005104056060451113381549)
    ·
      refine ⟨63751914021022669167518081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170005104056060451113381549 63751914021022669167518081)
      ·
        refine ⟨47813935515767001875638561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63751914021022669167518081 47813935515767001875638561)
        ·
          refine ⟨35860451636825251406728921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47813935515767001875638561 35860451636825251406728921)
          ·
            refine ⟨26895338727618938555046691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35860451636825251406728921 26895338727618938555046691)
            ·
              refine ⟨40343008091428407832570037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26895338727618938555046691 40343008091428407832570037)
              ·
                refine ⟨3782157008571413234303441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40343008091428407832570037 3782157008571413234303441)
                ·
                  refine ⟨2836617756428559925727581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3782157008571413234303441 2836617756428559925727581)
                  ·
                    refine ⟨1063731658660709972147843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2836617756428559925727581 1063731658660709972147843)
                    ·
                      rfl

theorem cell22_3107415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 2, 3].length) (baseStart_3107415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107415 prefixEnd_3107415 := by exact prefixLift 3107415
  have htrace : WordTrace (prefixWord ++ tailWord_3107415) baseStart_3107415 baseEnd_3107415 := by
    simpa [prefixWord, tailWord_3107415, baseEnd_3107415] using wordTrace_append hprefix tailTrace_3107415
  have hstable : (prefixWord ++ tailWord_3107415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107415).length < 2 ^ (prefixWord ++ tailWord_3107415).sum := by decide
  have hdescent : baseEnd_3107415 < baseStart_3107415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107445 : List Nat := [1, 3, 4, 2, 2, 1, 9]
def baseStart_3107445 : Nat := 118140960795 + 3107445 * 2 ^ 59
def prefixEnd_3107445 : Nat := 4983230072969 + 3 ^ 40 * 3107445 * 2
def baseEnd_3107445 : Nat := 39397849195325921996213

theorem tailTrace_3107445 : CollatzResearch.WordTrace tailWord_3107445 prefixEnd_3107445 39397849195325921996213 := by
  unfold tailWord_3107445
  simp only [CollatzResearch.WordTrace]
  refine ⟨113337830227264949199179789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75558553484843299466119859 113337830227264949199179789)
  ·
    refine ⟨42501686335224355949692421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113337830227264949199179789 42501686335224355949692421)
    ·
      refine ⟨7969066187854566740567329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42501686335224355949692421 7969066187854566740567329)
      ·
        refine ⟨5976799640890925055425497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7969066187854566740567329 5976799640890925055425497)
        ·
          refine ⟨4482599730668193791569123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5976799640890925055425497 4482599730668193791569123)
          ·
            refine ⟨6723899596002290687353685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4482599730668193791569123 6723899596002290687353685)
            ·
              refine ⟨39397849195325921996213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6723899596002290687353685 39397849195325921996213)
              ·
                rfl

theorem cell22_3107445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 9].length) (baseStart_3107445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107445 prefixEnd_3107445 := by exact prefixLift 3107445
  have htrace : WordTrace (prefixWord ++ tailWord_3107445) baseStart_3107445 baseEnd_3107445 := by
    simpa [prefixWord, tailWord_3107445, baseEnd_3107445] using wordTrace_append hprefix tailTrace_3107445
  have hstable : (prefixWord ++ tailWord_3107445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107445).length < 2 ^ (prefixWord ++ tailWord_3107445).sum := by decide
  have hdescent : baseEnd_3107445 < baseStart_3107445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107511 : List Nat := [1, 1, 3, 1, 6, 1, 3, 2, 1, 3]
def baseStart_3107511 : Nat := 118140960795 + 3107511 * 2 ^ 59
def prefixEnd_3107511 : Nat := 4983230072969 + 3 ^ 40 * 3107511 * 2
def baseEnd_3107511 : Nat := 1063764521422597721747549

theorem tailTrace_3107511 : CollatzResearch.WordTrace tailWord_3107511 prefixEnd_3107511 1063764521422597721747549 := by
  unfold tailWord_3107511
  simp only [CollatzResearch.WordTrace]
  refine ⟨113340237445025842471082387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75560158296683894980721591 113340237445025842471082387)
  ·
    refine ⟨170010356167538763706623581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113340237445025842471082387 170010356167538763706623581)
    ·
      refine ⟨63753883562827036389983843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170010356167538763706623581 63753883562827036389983843)
      ·
        refine ⟨95630825344240554584975765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63753883562827036389983843 95630825344240554584975765)
        ·
          refine ⟨4482694938011275996170739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 95630825344240554584975765 4482694938011275996170739)
          ·
            refine ⟨6724042407016913994256109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4482694938011275996170739 6724042407016913994256109)
            ·
              refine ⟨2521515902631342747846041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6724042407016913994256109 2521515902631342747846041)
              ·
                refine ⟨1891136926973507060884531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2521515902631342747846041 1891136926973507060884531)
                ·
                  refine ⟨2836705390460260591326797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1891136926973507060884531 2836705390460260591326797)
                  ·
                    refine ⟨1063764521422597721747549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2836705390460260591326797 1063764521422597721747549)
                    ·
                      rfl

theorem cell22_3107511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 2, 1, 3].length) (baseStart_3107511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107511 prefixEnd_3107511 := by exact prefixLift 3107511
  have htrace : WordTrace (prefixWord ++ tailWord_3107511) baseStart_3107511 baseEnd_3107511 := by
    simpa [prefixWord, tailWord_3107511, baseEnd_3107511] using wordTrace_append hprefix tailTrace_3107511
  have hstable : (prefixWord ++ tailWord_3107511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107511).length < 2 ^ (prefixWord ++ tailWord_3107511).sum := by decide
  have hdescent : baseEnd_3107511 < baseStart_3107511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107524 : List Nat := [2, 3, 3, 1, 1, 4, 2, 1, 5]
def baseStart_3107524 : Nat := 118140960795 + 3107524 * 2 ^ 59
def prefixEnd_3107524 : Nat := 4983230072969 + 3 ^ 40 * 3107524 * 2
def baseEnd_3107524 : Nat := 354589657196090007057503

theorem tailTrace_3107524 : CollatzResearch.WordTrace tailWord_3107524 prefixEnd_3107524 354589657196090007057503 := by
  unfold tailWord_3107524
  simp only [CollatzResearch.WordTrace]
  refine ⟨56670355796989372845652813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75560474395985830460870417 56670355796989372845652813)
  ·
    refine ⟨21251383423871014817119805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56670355796989372845652813 21251383423871014817119805)
    ·
      refine ⟨7969268783951630556419927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21251383423871014817119805 7969268783951630556419927)
      ·
        refine ⟨11953903175927445834629891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7969268783951630556419927 11953903175927445834629891)
        ·
          refine ⟨17930854763891168751944837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11953903175927445834629891 17930854763891168751944837)
          ·
            refine ⟨3362035268229594140989657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17930854763891168751944837 3362035268229594140989657)
            ·
              refine ⟨2521526451172195605742243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3362035268229594140989657 2521526451172195605742243)
              ·
                refine ⟨3782289676758293408613365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2521526451172195605742243 3782289676758293408613365)
                ·
                  refine ⟨354589657196090007057503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3782289676758293408613365 354589657196090007057503)
                  ·
                    rfl

theorem cell22_3107524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_3107524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107524 prefixEnd_3107524 := by exact prefixLift 3107524
  have htrace : WordTrace (prefixWord ++ tailWord_3107524) baseStart_3107524 baseEnd_3107524 := by
    simpa [prefixWord, tailWord_3107524, baseEnd_3107524] using wordTrace_append hprefix tailTrace_3107524
  have hstable : (prefixWord ++ tailWord_3107524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107524).length < 2 ^ (prefixWord ++ tailWord_3107524).sum := by decide
  have hdescent : baseEnd_3107524 < baseStart_3107524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107567 : List Nat := [1, 1, 2, 1, 5, 2, 1, 4, 2, 3]
def baseStart_3107567 : Nat := 118140960795 + 3107567 * 2 ^ 59
def prefixEnd_3107567 : Nat := 4983230072969 + 3 ^ 40 * 3107567 * 2
def baseEnd_3107567 : Nat := 1063783691367032242347377

theorem tailTrace_3107567 : CollatzResearch.WordTrace tailWord_3107567 prefixEnd_3107567 1063783691367032242347377 := by
  unfold tailWord_3107567
  simp only [CollatzResearch.WordTrace]
  refine ⟨113342279932822964035120955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75561519955215309356747303 113342279932822964035120955)
  ·
    refine ⟨170013419899234446052681433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113342279932822964035120955 170013419899234446052681433)
    ·
      refine ⟨127510064924425834539511075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170013419899234446052681433 127510064924425834539511075)
      ·
        refine ⟨191265097386638751809266613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127510064924425834539511075 191265097386638751809266613)
        ·
          refine ⟨17931102879997382982118745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 191265097386638751809266613 17931102879997382982118745)
          ·
            refine ⟨13448327159998037236589059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17931102879997382982118745 13448327159998037236589059)
            ·
              refine ⟨20172490739997055854883589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13448327159998037236589059 20172490739997055854883589)
              ·
                refine ⟨3782342013749447972790673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20172490739997055854883589 3782342013749447972790673)
                ·
                  refine ⟨2836756510312085979593005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3782342013749447972790673 2836756510312085979593005)
                  ·
                    refine ⟨1063783691367032242347377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2836756510312085979593005 1063783691367032242347377)
                    ·
                      rfl

theorem cell22_3107567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 2, 3].length) (baseStart_3107567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107567 prefixEnd_3107567 := by exact prefixLift 3107567
  have htrace : WordTrace (prefixWord ++ tailWord_3107567) baseStart_3107567 baseEnd_3107567 := by
    simpa [prefixWord, tailWord_3107567, baseEnd_3107567] using wordTrace_append hprefix tailTrace_3107567
  have hstable : (prefixWord ++ tailWord_3107567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107567).length < 2 ^ (prefixWord ++ tailWord_3107567).sum := by decide
  have hdescent : baseEnd_3107567 < baseStart_3107567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107580 : List Nat := [2, 2, 2, 1, 3, 2, 3, 7]
def baseStart_3107580 : Nat := 118140960795 + 3107580 * 2 ^ 59
def prefixEnd_3107580 : Nat := 4983230072969 + 3 ^ 40 * 3107580 * 2
def baseEnd_3107580 : Nat := 118198682392522726863593

theorem tailTrace_3107580 : CollatzResearch.WordTrace tailWord_3107580 prefixEnd_3107580 118198682392522726863593 := by
  unfold tailWord_3107580
  simp only [CollatzResearch.WordTrace]
  refine ⟨56671377040887933627672097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75561836054517244836896129 56671377040887933627672097)
  ·
    refine ⟨42503532780665950220754073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56671377040887933627672097 42503532780665950220754073)
    ·
      refine ⟨31877649585499462665565555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42503532780665950220754073 31877649585499462665565555)
      ·
        refine ⟨47816474378249193998348333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31877649585499462665565555 47816474378249193998348333)
        ·
          refine ⟨17931177891843447749380625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47816474378249193998348333 17931177891843447749380625)
          ·
            refine ⟨13448383418882585812035469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17931177891843447749380625 13448383418882585812035469)
            ·
              refine ⟨5043143782080969679513301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13448383418882585812035469 5043143782080969679513301)
              ·
                refine ⟨118198682392522726863593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5043143782080969679513301 118198682392522726863593)
                ·
                  rfl

theorem cell22_3107580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 7].length) (baseStart_3107580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107580 prefixEnd_3107580 := by exact prefixLift 3107580
  have htrace : WordTrace (prefixWord ++ tailWord_3107580) baseStart_3107580 baseEnd_3107580 := by
    simpa [prefixWord, tailWord_3107580, baseEnd_3107580] using wordTrace_append hprefix tailTrace_3107580
  have hstable : (prefixWord ++ tailWord_3107580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107580).length < 2 ^ (prefixWord ++ tailWord_3107580).sum := by decide
  have hdescent : baseEnd_3107580 < baseStart_3107580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107640 : List Nat := [2, 1, 2, 1, 3, 2, 1, 3, 2, 5]
def baseStart_3107640 : Nat := 118140960795 + 3107640 * 2 ^ 59
def prefixEnd_3107640 : Nat := 4983230072969 + 3 ^ 40 * 3107640 * 2
def baseEnd_3107640 : Nat := 1063808680758884385272153

theorem tailTrace_3107640 : CollatzResearch.WordTrace tailWord_3107640 prefixEnd_3107640 1063808680758884385272153 := by
  unfold tailWord_3107640
  simp only [CollatzResearch.WordTrace]
  refine ⟨56672471230779248751264187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75563294974372331668352249 56672471230779248751264187)
  ·
    refine ⟨85008706846168873126896281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56672471230779248751264187 85008706846168873126896281)
    ·
      refine ⟨63756530134626654845172211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85008706846168873126896281 63756530134626654845172211)
      ·
        refine ⟨95634795201939982267758317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63756530134626654845172211 95634795201939982267758317)
        ·
          refine ⟨35863048200727493350409369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95634795201939982267758317 35863048200727493350409369)
          ·
            refine ⟨26897286150545620012807027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35863048200727493350409369 26897286150545620012807027)
            ·
              refine ⟨40345929225818430019210541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26897286150545620012807027 40345929225818430019210541)
              ·
                refine ⟨15129723459681911257203953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40345929225818430019210541 15129723459681911257203953)
                ·
                  refine ⟨11347292594761433442902965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15129723459681911257203953 11347292594761433442902965)
                  ·
                    refine ⟨1063808680758884385272153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11347292594761433442902965 1063808680758884385272153)
                    ·
                      rfl

theorem cell22_3107640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_3107640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107640 prefixEnd_3107640 := by exact prefixLift 3107640
  have htrace : WordTrace (prefixWord ++ tailWord_3107640) baseStart_3107640 baseEnd_3107640 := by
    simpa [prefixWord, tailWord_3107640, baseEnd_3107640] using wordTrace_append hprefix tailTrace_3107640
  have hstable : (prefixWord ++ tailWord_3107640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107640).length < 2 ^ (prefixWord ++ tailWord_3107640).sum := by decide
  have hdescent : baseEnd_3107640 < baseStart_3107640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107687 : List Nat := [1, 1, 5, 1, 2, 2, 3, 1, 6]
def baseStart_3107687 : Nat := 118140960795 + 3107687 * 2 ^ 59
def prefixEnd_3107687 : Nat := 4983230072969 + 3 ^ 40 * 3107687 * 2
def baseEnd_3107687 : Nat := 354608256606463976449003

theorem tailTrace_3107687 : CollatzResearch.WordTrace tailWord_3107687 prefixEnd_3107687 354608256606463976449003 := by
  unfold tailWord_3107687
  simp only [CollatzResearch.WordTrace]
  refine ⟨113346656692388224529489315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75564437794925483019659543 113346656692388224529489315)
  ·
    refine ⟨170019985038582336794233973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113346656692388224529489315 170019985038582336794233973)
    ·
      refine ⟨15939373597367094074459435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170019985038582336794233973 15939373597367094074459435)
      ·
        refine ⟨23909060396050641111689153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15939373597367094074459435 23909060396050641111689153)
        ·
          refine ⟨17931795297037980833766865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23909060396050641111689153 17931795297037980833766865)
          ·
            refine ⟨13448846472778485625325149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17931795297037980833766865 13448846472778485625325149)
            ·
              refine ⟨5043317427291932109496931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13448846472778485625325149 5043317427291932109496931)
              ·
                refine ⟨7564976140937898164245397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5043317427291932109496931 7564976140937898164245397)
                ·
                  refine ⟨354608256606463976449003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7564976140937898164245397 354608256606463976449003)
                  ·
                    rfl

theorem cell22_3107687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 6].length) (baseStart_3107687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107687 prefixEnd_3107687 := by exact prefixLift 3107687
  have htrace : WordTrace (prefixWord ++ tailWord_3107687) baseStart_3107687 baseEnd_3107687 := by
    simpa [prefixWord, tailWord_3107687, baseEnd_3107687] using wordTrace_append hprefix tailTrace_3107687
  have hstable : (prefixWord ++ tailWord_3107687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107687).length < 2 ^ (prefixWord ++ tailWord_3107687).sum := by decide
  have hdescent : baseEnd_3107687 < baseStart_3107687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107715 : List Nat := [1, 1, 1, 3, 4, 1, 1, 10]
def baseStart_3107715 : Nat := 118140960795 + 3107715 * 2 ^ 59
def prefixEnd_3107715 : Nat := 4983230072969 + 3 ^ 40 * 3107715 * 2
def baseEnd_3107715 : Nat := 118203817199067687738547

theorem tailTrace_3107715 : CollatzResearch.WordTrace tailWord_3107715 prefixEnd_3107715 118203817199067687738547 := by
  unfold tailWord_3107715
  simp only [CollatzResearch.WordTrace]
  refine ⟨113347677936286785311508599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75565118624191190207672399 113347677936286785311508599)
  ·
    refine ⟨170021516904430177967262899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113347677936286785311508599 170021516904430177967262899)
    ·
      refine ⟨255032275356645266950894349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170021516904430177967262899 255032275356645266950894349)
      ·
        refine ⟨95637103258741975106585381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255032275356645266950894349 95637103258741975106585381)
        ·
          refine ⟨17931956861014120332484759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95637103258741975106585381 17931956861014120332484759)
          ·
            refine ⟨26897935291521180498727139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17931956861014120332484759 26897935291521180498727139)
            ·
              refine ⟨40346902937281770748090709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26897935291521180498727139 40346902937281770748090709)
              ·
                refine ⟨118203817199067687738547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40346902937281770748090709 118203817199067687738547)
                ·
                  rfl

theorem cell22_3107715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 10].length) (baseStart_3107715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107715 prefixEnd_3107715 := by exact prefixLift 3107715
  have htrace : WordTrace (prefixWord ++ tailWord_3107715) baseStart_3107715 baseEnd_3107715 := by
    simpa [prefixWord, tailWord_3107715, baseEnd_3107715] using wordTrace_append hprefix tailTrace_3107715
  have hstable : (prefixWord ++ tailWord_3107715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107715).length < 2 ^ (prefixWord ++ tailWord_3107715).sum := by decide
  have hdescent : baseEnd_3107715 < baseStart_3107715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107717 : List Nat := [1, 3, 1, 1, 3, 3, 1, 3, 2, 4]
def baseStart_3107717 : Nat := 118140960795 + 3107717 * 2 ^ 59
def prefixEnd_3107717 : Nat := 4983230072969 + 3 ^ 40 * 3107717 * 2
def baseEnd_3107717 : Nat := 1063835039432481851096917

theorem tailTrace_3107717 : CollatzResearch.WordTrace tailWord_3107717 prefixEnd_3107717 1063835039432481851096917 := by
  unfold tailWord_3107717
  simp only [CollatzResearch.WordTrace]
  refine ⟨113347750882279539653081405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75565167254853026435387603 113347750882279539653081405)
  ·
    refine ⟨42505406580854827369905527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113347750882279539653081405 42505406580854827369905527)
    ·
      refine ⟨63758109871282241054858291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42505406580854827369905527 63758109871282241054858291)
      ·
        refine ⟨95637164806923361582287437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63758109871282241054858291 95637164806923361582287437)
        ·
          refine ⟨35863936802596260593357789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95637164806923361582287437 35863936802596260593357789)
          ·
            refine ⟨13448976300973597722509171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35863936802596260593357789 13448976300973597722509171)
            ·
              refine ⟨20173464451460396583763757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13448976300973597722509171 20173464451460396583763757)
              ·
                refine ⟨7565049169297648718911409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20173464451460396583763757 7565049169297648718911409)
                ·
                  refine ⟨5673786876973236539183557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7565049169297648718911409 5673786876973236539183557)
                  ·
                    refine ⟨1063835039432481851096917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5673786876973236539183557 1063835039432481851096917)
                    ·
                      rfl

theorem cell22_3107717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_3107717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107717 prefixEnd_3107717 := by exact prefixLift 3107717
  have htrace : WordTrace (prefixWord ++ tailWord_3107717) baseStart_3107717 baseEnd_3107717 := by
    simpa [prefixWord, tailWord_3107717, baseEnd_3107717] using wordTrace_append hprefix tailTrace_3107717
  have hstable : (prefixWord ++ tailWord_3107717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107717).length < 2 ^ (prefixWord ++ tailWord_3107717).sum := by decide
  have hdescent : baseEnd_3107717 < baseStart_3107717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107738 : List Nat := [3, 1, 1, 4, 3, 2, 2, 2, 4]
def baseStart_3107738 : Nat := 118140960795 + 3107738 * 2 ^ 59
def prefixEnd_3107738 : Nat := 4983230072969 + 3 ^ 40 * 3107738 * 2
def baseEnd_3107738 : Nat := 354614076053881598773951

theorem tailTrace_3107738 : CollatzResearch.WordTrace tailWord_3107738 prefixEnd_3107738 354614076053881598773951 := by
  unfold tailWord_3107738
  simp only [CollatzResearch.WordTrace]
  refine ⟨28337129203800865059898967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75565677876802306826397245 28337129203800865059898967)
  ·
    refine ⟨42505693805701297589848451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28337129203800865059898967 42505693805701297589848451)
    ·
      refine ⟨63758540708551946384772677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42505693805701297589848451 63758540708551946384772677)
      ·
        refine ⟨11954726382853489947144877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63758540708551946384772677 11954726382853489947144877)
        ·
          refine ⟨4483022393570058730179329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11954726382853489947144877 4483022393570058730179329)
          ·
            refine ⟨3362266795177544047634497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4483022393570058730179329 3362266795177544047634497)
            ·
              refine ⟨2521700096383158035725873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3362266795177544047634497 2521700096383158035725873)
              ·
                refine ⟨1891275072287368526794405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2521700096383158035725873 1891275072287368526794405)
                ·
                  refine ⟨354614076053881598773951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1891275072287368526794405 354614076053881598773951)
                  ·
                    rfl

theorem cell22_3107738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 2, 4].length) (baseStart_3107738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107738 prefixEnd_3107738 := by exact prefixLift 3107738
  have htrace : WordTrace (prefixWord ++ tailWord_3107738) baseStart_3107738 baseEnd_3107738 := by
    simpa [prefixWord, tailWord_3107738, baseEnd_3107738] using wordTrace_append hprefix tailTrace_3107738
  have hstable : (prefixWord ++ tailWord_3107738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107738).length < 2 ^ (prefixWord ++ tailWord_3107738).sum := by decide
  have hdescent : baseEnd_3107738 < baseStart_3107738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107794 : List Nat := [3, 2, 2, 3, 1, 2, 1, 1, 7]
def baseStart_3107794 : Nat := 118140960795 + 3107794 * 2 ^ 59
def prefixEnd_3107794 : Nat := 4983230072969 + 3 ^ 40 * 3107794 * 2
def baseEnd_3107794 : Nat := 354620466035359772307227

theorem tailTrace_3107794 : CollatzResearch.WordTrace tailWord_3107794 prefixEnd_3107794 354620466035359772307227 := by
  unfold tailWord_3107794
  simp only [CollatzResearch.WordTrace]
  refine ⟨28337639825750145450908609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75567039535333721202422957 28337639825750145450908609)
  ·
    refine ⟨21253229869312609088181457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28337639825750145450908609 21253229869312609088181457)
    ·
      refine ⟨15939922401984456816136093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21253229869312609088181457 15939922401984456816136093)
      ·
        refine ⟨5977470900744171306051035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15939922401984456816136093 5977470900744171306051035)
        ·
          refine ⟨8966206351116256959076553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5977470900744171306051035 8966206351116256959076553)
          ·
            refine ⟨6724654763337192719307415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8966206351116256959076553 6724654763337192719307415)
            ·
              refine ⟨10086982145005789078961123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6724654763337192719307415 10086982145005789078961123)
              ·
                refine ⟨15130473217508683618441685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10086982145005789078961123 15130473217508683618441685)
                ·
                  refine ⟨354620466035359772307227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15130473217508683618441685 354620466035359772307227)
                  ·
                    rfl

theorem cell22_3107794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_3107794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107794 prefixEnd_3107794 := by exact prefixLift 3107794
  have htrace : WordTrace (prefixWord ++ tailWord_3107794) baseStart_3107794 baseEnd_3107794 := by
    simpa [prefixWord, tailWord_3107794, baseEnd_3107794] using wordTrace_append hprefix tailTrace_3107794
  have hstable : (prefixWord ++ tailWord_3107794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107794).length < 2 ^ (prefixWord ++ tailWord_3107794).sum := by decide
  have hdescent : baseEnd_3107794 < baseStart_3107794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107798 : List Nat := [5, 2, 1, 1, 2, 2, 2, 1, 3, 3]
def baseStart_3107798 : Nat := 118140960795 + 3107798 * 2 ^ 59
def prefixEnd_3107798 : Nat := 4983230072969 + 3 ^ 40 * 3107798 * 2
def baseEnd_3107798 : Nat := 1063862767387824639821669

theorem tailTrace_3107798 : CollatzResearch.WordTrace tailWord_3107798 prefixEnd_3107798 1063862767387824639821669 := by
  unfold tailWord_3107798
  simp only [CollatzResearch.WordTrace]
  refine ⟨7084419074686630655423753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75567136796657393657853365 7084419074686630655423753)
  ·
    refine ⟨5313314306014972991567815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7084419074686630655423753 5313314306014972991567815)
    ·
      refine ⟨7969971459022459487351723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5313314306014972991567815 7969971459022459487351723)
      ·
        refine ⟨11954957188533689231027585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7969971459022459487351723 11954957188533689231027585)
        ·
          refine ⟨8966217891400266923270689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11954957188533689231027585 8966217891400266923270689)
          ·
            refine ⟨6724663418550200192453017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8966217891400266923270689 6724663418550200192453017)
            ·
              refine ⟨5043497563912650144339763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6724663418550200192453017 5043497563912650144339763)
              ·
                refine ⟨7565246345868975216509645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5043497563912650144339763 7565246345868975216509645)
                ·
                  refine ⟨2836967379700865706191117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7565246345868975216509645 2836967379700865706191117)
                  ·
                    refine ⟨1063862767387824639821669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2836967379700865706191117 1063862767387824639821669)
                    ·
                      rfl

theorem cell22_3107798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_3107798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107798 prefixEnd_3107798 := by exact prefixLift 3107798
  have htrace : WordTrace (prefixWord ++ tailWord_3107798) baseStart_3107798 baseEnd_3107798 := by
    simpa [prefixWord, tailWord_3107798, baseEnd_3107798] using wordTrace_append hprefix tailTrace_3107798
  have hstable : (prefixWord ++ tailWord_3107798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107798).length < 2 ^ (prefixWord ++ tailWord_3107798).sum := by decide
  have hdescent : baseEnd_3107798 < baseStart_3107798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107837 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 3, 5]
def baseStart_3107837 : Nat := 118140960795 + 3107837 * 2 ^ 59
def prefixEnd_3107837 : Nat := 4983230072969 + 3 ^ 40 * 3107837 * 2
def baseEnd_3107837 : Nat := 1063876117884841538096549

theorem tailTrace_3107837 : CollatzResearch.WordTrace tailWord_3107837 prefixEnd_3107837 1063876117884841538096549 := by
  unfold tailWord_3107837
  simp only [CollatzResearch.WordTrace]
  refine ⟨113352127641844800147449765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75568085094563200098299843 113352127641844800147449765)
  ·
    refine ⟨21253523932845900027646831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113352127641844800147449765 21253523932845900027646831)
    ·
      refine ⟨31880285899268850041470247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21253523932845900027646831 31880285899268850041470247)
      ·
        refine ⟨47820428848903275062205371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31880285899268850041470247 47820428848903275062205371)
        ·
          refine ⟨71730643273354912593308057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47820428848903275062205371 71730643273354912593308057)
          ·
            refine ⟨53797982455016184444981043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71730643273354912593308057 53797982455016184444981043)
            ·
              refine ⟨80696973682524276667471565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53797982455016184444981043 80696973682524276667471565)
              ·
                refine ⟨30261365130946603750301837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80696973682524276667471565 30261365130946603750301837)
                ·
                  refine ⟨11348011924104976406363189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30261365130946603750301837 11348011924104976406363189)
                  ·
                    refine ⟨1063876117884841538096549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11348011924104976406363189 1063876117884841538096549)
                    ·
                      rfl

theorem cell22_3107837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_3107837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107837 prefixEnd_3107837 := by exact prefixLift 3107837
  have htrace : WordTrace (prefixWord ++ tailWord_3107837) baseStart_3107837 baseEnd_3107837 := by
    simpa [prefixWord, tailWord_3107837, baseEnd_3107837] using wordTrace_append hprefix tailTrace_3107837
  have hstable : (prefixWord ++ tailWord_3107837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107837).length < 2 ^ (prefixWord ++ tailWord_3107837).sum := by decide
  have hdescent : baseEnd_3107837 < baseStart_3107837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107871 : List Nat := [1, 1, 2, 4, 1, 4, 1, 3, 2, 3]
def baseStart_3107871 : Nat := 118140960795 + 3107871 * 2 ^ 59
def prefixEnd_3107871 : Nat := 4983230072969 + 3 ^ 40 * 3107871 * 2
def baseEnd_3107871 : Nat := 1063887756779676782746445

theorem tailTrace_3107871 : CollatzResearch.WordTrace tailWord_3107871 prefixEnd_3107871 1063887756779676782746445 := by
  unfold tailWord_3107871
  simp only [CollatzResearch.WordTrace]
  refine ⟨113353367723721623954187467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75568911815814415969458311 113353367723721623954187467)
  ·
    refine ⟨170030051585582435931281201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113353367723721623954187467 170030051585582435931281201)
    ·
      refine ⟨127522538689186826948460901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170030051585582435931281201 127522538689186826948460901)
      ·
        refine ⟨23910476004222530052836419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127522538689186826948460901 23910476004222530052836419)
        ·
          refine ⟨35865714006333795079254629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23910476004222530052836419 35865714006333795079254629)
          ·
            refine ⟨6724821376187586577360243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35865714006333795079254629 6724821376187586577360243)
            ·
              refine ⟨10087232064281379866040365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6724821376187586577360243 10087232064281379866040365)
              ·
                refine ⟨3782712024105517449765137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10087232064281379866040365 3782712024105517449765137)
                ·
                  refine ⟨2837034018079138087323853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3782712024105517449765137 2837034018079138087323853)
                  ·
                    refine ⟨1063887756779676782746445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2837034018079138087323853 1063887756779676782746445)
                    ·
                      rfl

theorem cell22_3107871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 2, 3].length) (baseStart_3107871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107871 prefixEnd_3107871 := by exact prefixLift 3107871
  have htrace : WordTrace (prefixWord ++ tailWord_3107871) baseStart_3107871 baseEnd_3107871 := by
    simpa [prefixWord, tailWord_3107871, baseEnd_3107871] using wordTrace_append hprefix tailTrace_3107871
  have hstable : (prefixWord ++ tailWord_3107871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107871).length < 2 ^ (prefixWord ++ tailWord_3107871).sum := by decide
  have hdescent : baseEnd_3107871 < baseStart_3107871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107886 : List Nat := [4, 1, 3, 1, 1, 1, 4, 1, 2, 4]
def baseStart_3107886 : Nat := 118140960795 + 3107886 * 2 ^ 59
def prefixEnd_3107886 : Nat := 4983230072969 + 3 ^ 40 * 3107886 * 2
def baseEnd_3107886 : Nat := 1063892891586221743621399

theorem tailTrace_3107886 : CollatzResearch.WordTrace tailWord_3107886 prefixEnd_3107886 1063892891586221743621399 := by
  unfold tailWord_3107886
  simp only [CollatzResearch.WordTrace]
  refine ⟨14169239352333410189497939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75569276545778187677322341 14169239352333410189497939)
  ·
    refine ⟨21253859028500115284246909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14169239352333410189497939 21253859028500115284246909)
    ·
      refine ⟨7970197135687543231592591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21253859028500115284246909 7970197135687543231592591)
      ·
        refine ⟨11955295703531314847388887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7970197135687543231592591 11955295703531314847388887)
        ·
          refine ⟨17932943555296972271083331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11955295703531314847388887 17932943555296972271083331)
          ·
            refine ⟨26899415332945458406624997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17932943555296972271083331 26899415332945458406624997)
            ·
              refine ⟨5043640374927273451242187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26899415332945458406624997 5043640374927273451242187)
              ·
                refine ⟨7565460562390910176863281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5043640374927273451242187 7565460562390910176863281)
                ·
                  refine ⟨5674095421793182632647461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7565460562390910176863281 5674095421793182632647461)
                  ·
                    refine ⟨1063892891586221743621399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5674095421793182632647461 1063892891586221743621399)
                    ·
                      rfl

theorem cell22_3107886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_3107886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107886 prefixEnd_3107886 := by exact prefixLift 3107886
  have htrace : WordTrace (prefixWord ++ tailWord_3107886) baseStart_3107886 baseEnd_3107886 := by
    simpa [prefixWord, tailWord_3107886, baseEnd_3107886] using wordTrace_append hprefix tailTrace_3107886
  have hstable : (prefixWord ++ tailWord_3107886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107886).length < 2 ^ (prefixWord ++ tailWord_3107886).sum := by decide
  have hdescent : baseEnd_3107886 < baseStart_3107886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107950 : List Nat := [4, 1, 2, 2, 1, 3, 2, 3, 1, 3]
def baseStart_3107950 : Nat := 118140960795 + 3107950 * 2 ^ 59
def prefixEnd_3107950 : Nat := 4983230072969 + 3 ^ 40 * 3107950 * 2
def baseEnd_3107950 : Nat := 1063914800094146910021203

theorem tailTrace_3107950 : CollatzResearch.WordTrace tailWord_3107950 prefixEnd_3107950 1063914800094146910021203 := by
  unfold tailWord_3107950
  simp only [CollatzResearch.WordTrace]
  refine ⟨14169531136304427555789163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75570832726956946964208869 14169531136304427555789163)
  ·
    refine ⟨21254296704456641333683745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14169531136304427555789163 21254296704456641333683745)
    ·
      refine ⟨15940722528342481000262809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21254296704456641333683745 15940722528342481000262809)
      ·
        refine ⟨11955541896256860750197107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15940722528342481000262809 11955541896256860750197107)
        ·
          refine ⟨17933312844385291125295661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11955541896256860750197107 17933312844385291125295661)
          ·
            refine ⟨6724992316644484171985873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17933312844385291125295661 6724992316644484171985873)
            ·
              refine ⟨5043744237483363128989405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6724992316644484171985873 5043744237483363128989405)
              ·
                refine ⟨1891404089056261173371027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5043744237483363128989405 1891404089056261173371027)
                ·
                  refine ⟨2837106133584391760056541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1891404089056261173371027 2837106133584391760056541)
                  ·
                    refine ⟨1063914800094146910021203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2837106133584391760056541 1063914800094146910021203)
                    ·
                      rfl

theorem cell22_3107950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_3107950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107950 prefixEnd_3107950 := by exact prefixLift 3107950
  have htrace : WordTrace (prefixWord ++ tailWord_3107950) baseStart_3107950 baseEnd_3107950 := by
    simpa [prefixWord, tailWord_3107950, baseEnd_3107950] using wordTrace_append hprefix tailTrace_3107950
  have hstable : (prefixWord ++ tailWord_3107950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107950).length < 2 ^ (prefixWord ++ tailWord_3107950).sum := by decide
  have hdescent : baseEnd_3107950 < baseStart_3107950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3107989 : List Nat := [1, 3, 2, 1, 1, 1, 2, 5, 1, 5]
def baseStart_3107989 : Nat := 118140960795 + 3107989 * 2 ^ 59
def prefixEnd_3107989 : Nat := 4983230072969 + 3 ^ 40 * 3107989 * 2
def baseEnd_3107989 : Nat := 1063928150591163808296083

theorem tailTrace_3107989 : CollatzResearch.WordTrace tailWord_3107989 prefixEnd_3107989 1063928150591163808296083 := by
  unfold tailWord_3107989
  simp only [CollatzResearch.WordTrace]
  refine ⟨113357671537294130106983021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75571781024862753404655347 113357671537294130106983021)
  ·
    refine ⟨42509126826485298790118633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113357671537294130106983021 42509126826485298790118633)
    ·
      refine ⟨31881845119863974092588975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42509126826485298790118633 31881845119863974092588975)
      ·
        refine ⟨47822767679795961138883463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31881845119863974092588975 47822767679795961138883463)
        ·
          refine ⟨71734151519693941708325195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47822767679795961138883463 71734151519693941708325195)
          ·
            refine ⟨107601227279540912562487793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71734151519693941708325195 107601227279540912562487793)
            ·
              refine ⟨80700920459655684421865845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107601227279540912562487793 80700920459655684421865845)
              ·
                refine ⟨7565711293092720414549923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80700920459655684421865845 7565711293092720414549923)
                ·
                  refine ⟨11348566939639080621824885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7565711293092720414549923 11348566939639080621824885)
                  ·
                    refine ⟨1063928150591163808296083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11348566939639080621824885 1063928150591163808296083)
                    ·
                      rfl

theorem cell22_3107989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_3107989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3107989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3107989 prefixEnd_3107989 := by exact prefixLift 3107989
  have htrace : WordTrace (prefixWord ++ tailWord_3107989) baseStart_3107989 baseEnd_3107989 := by
    simpa [prefixWord, tailWord_3107989, baseEnd_3107989] using wordTrace_append hprefix tailTrace_3107989
  have hstable : (prefixWord ++ tailWord_3107989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3107989).length < 2 ^ (prefixWord ++ tailWord_3107989).sum := by decide
  have hdescent : baseEnd_3107989 < baseStart_3107989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3107989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108139 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 2, 10]
def baseStart_3108139 : Nat := 118140960795 + 3108139 * 2 ^ 59
def prefixEnd_3108139 : Nat := 4983230072969 + 3 ^ 40 * 3108139 * 2
def baseEnd_3108139 : Nat := 1063979498656613417045623

theorem tailTrace_3108139 : CollatzResearch.WordTrace tailWord_3108139 prefixEnd_3108139 1063979498656613417045623 := by
  unfold tailWord_3108139
  simp only [CollatzResearch.WordTrace]
  refine ⟨113363142486750705724943471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75575428324500470483295647 113363142486750705724943471)
  ·
    refine ⟨170044713730126058587415207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113363142486750705724943471 170044713730126058587415207)
    ·
      refine ⟨255067070595189087881122811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170044713730126058587415207 255067070595189087881122811)
      ·
        refine ⟨382600605892783631821684217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255067070595189087881122811 382600605892783631821684217)
        ·
          refine ⟨286950454419587723866263163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382600605892783631821684217 286950454419587723866263163)
          ·
            refine ⟨430425681629381585799394745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286950454419587723866263163 430425681629381585799394745)
            ·
              refine ⟨322819261222036189349546059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 430425681629381585799394745 322819261222036189349546059)
              ·
                refine ⟨484228891833054284024319089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322819261222036189349546059 484228891833054284024319089)
                ·
                  refine ⟨363171668874790713018239317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 484228891833054284024319089 363171668874790713018239317)
                  ·
                    refine ⟨1063979498656613417045623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 363171668874790713018239317 1063979498656613417045623)
                    ·
                      rfl

theorem cell22_3108139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 10].length) (baseStart_3108139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3108139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3108139 prefixEnd_3108139 := by exact prefixLift 3108139
  have htrace : WordTrace (prefixWord ++ tailWord_3108139) baseStart_3108139 baseEnd_3108139 := by
    simpa [prefixWord, tailWord_3108139, baseEnd_3108139] using wordTrace_append hprefix tailTrace_3108139
  have hstable : (prefixWord ++ tailWord_3108139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108139).length < 2 ^ (prefixWord ++ tailWord_3108139).sum := by decide
  have hdescent : baseEnd_3108139 < baseStart_3108139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108156 : List Nat := [2, 2, 2, 2, 1, 3, 1, 2, 1, 6]
def baseStart_3108156 : Nat := 118140960795 + 3108156 * 2 ^ 59
def prefixEnd_3108156 : Nat := 4983230072969 + 3 ^ 40 * 3108156 * 2
def baseEnd_3108156 : Nat := 1063985318104031039370571

theorem tailTrace_3108156 : CollatzResearch.WordTrace tailWord_3108156 prefixEnd_3108156 1063985318104031039370571 := by
  unfold tailWord_3108156
  simp only [CollatzResearch.WordTrace]
  refine ⟨56681881263844558814156161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75575841685126078418874881 56681881263844558814156161)
  ·
    refine ⟨42511410947883419110617121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56681881263844558814156161 42511410947883419110617121)
    ·
      refine ⟨31883558210912564332962841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42511410947883419110617121 31883558210912564332962841)
      ·
        refine ⟨23912668658184423249722131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31883558210912564332962841 23912668658184423249722131)
        ·
          refine ⟨35869002987276634874583197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23912668658184423249722131 35869002987276634874583197)
          ·
            refine ⟨13450876120228738077968699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35869002987276634874583197 13450876120228738077968699)
            ·
              refine ⟨20176314180343107116953049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13450876120228738077968699 20176314180343107116953049)
              ·
                refine ⟨15132235635257330337714787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20176314180343107116953049 15132235635257330337714787)
                ·
                  refine ⟨22698353452885995506572181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15132235635257330337714787 22698353452885995506572181)
                  ·
                    refine ⟨1063985318104031039370571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22698353452885995506572181 1063985318104031039370571)
                    ·
                      rfl

theorem cell22_3108156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_3108156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3108156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3108156 prefixEnd_3108156 := by exact prefixLift 3108156
  have htrace : WordTrace (prefixWord ++ tailWord_3108156) baseStart_3108156 baseEnd_3108156 := by
    simpa [prefixWord, tailWord_3108156, baseEnd_3108156] using wordTrace_append hprefix tailTrace_3108156
  have hstable : (prefixWord ++ tailWord_3108156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108156).length < 2 ^ (prefixWord ++ tailWord_3108156).sum := by decide
  have hdescent : baseEnd_3108156 < baseStart_3108156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108263 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 5, 4]
def baseStart_3108263 : Nat := 118140960795 + 3108263 * 2 ^ 59
def prefixEnd_3108263 : Nat := 4983230072969 + 3 ^ 40 * 3108263 * 2
def baseEnd_3108263 : Nat := 1064021946390718426945243

theorem tailTrace_3108263 : CollatzResearch.WordTrace tailWord_3108263 prefixEnd_3108263 1064021946390718426945243 := by
  unfold tailWord_3108263
  simp only [CollatzResearch.WordTrace]
  refine ⟨113367665138301474902457443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75578443425534316601638295 113367665138301474902457443)
  ·
    refine ⟨170051497707452212353686165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113367665138301474902457443 170051497707452212353686165)
    ·
      refine ⟨7971163955036822454079039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 170051497707452212353686165 7971163955036822454079039)
      ·
        refine ⟨11956745932555233681118559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7971163955036822454079039 11956745932555233681118559)
        ·
          refine ⟨17935118898832850521677839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11956745932555233681118559 17935118898832850521677839)
          ·
            refine ⟨26902678348249275782516759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17935118898832850521677839 26902678348249275782516759)
            ·
              refine ⟨40354017522373913673775139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26902678348249275782516759 40354017522373913673775139)
              ·
                refine ⟨60531026283560870510662709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40354017522373913673775139 60531026283560870510662709)
                ·
                  refine ⟨5674783714083831610374629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60531026283560870510662709 5674783714083831610374629)
                  ·
                    refine ⟨1064021946390718426945243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5674783714083831610374629 1064021946390718426945243)
                    ·
                      rfl

theorem cell22_3108263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_3108263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3108263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3108263 prefixEnd_3108263 := by exact prefixLift 3108263
  have htrace : WordTrace (prefixWord ++ tailWord_3108263) baseStart_3108263 baseEnd_3108263 := by
    simpa [prefixWord, tailWord_3108263, baseEnd_3108263] using wordTrace_append hprefix tailTrace_3108263
  have hstable : (prefixWord ++ tailWord_3108263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108263).length < 2 ^ (prefixWord ++ tailWord_3108263).sum := by decide
  have hdescent : baseEnd_3108263 < baseStart_3108263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108295 : List Nat := [1, 1, 4, 1, 1, 3, 4, 3, 4]
def baseStart_3108295 : Nat := 118140960795 + 3108295 * 2 ^ 59
def prefixEnd_3108295 : Nat := 4983230072969 + 3 ^ 40 * 3108295 * 2
def baseEnd_3108295 : Nat := 354677633548227003381715

theorem tailTrace_3108295 : CollatzResearch.WordTrace tailWord_3108295 prefixEnd_3108295 354677633548227003381715 := by
  unfold tailWord_3108295
  simp only [CollatzResearch.WordTrace]
  refine ⟨113368832274185544367622339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75579221516123696245081559 113368832274185544367622339)
  ·
    refine ⟨170053248411278316551433509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113368832274185544367622339 170053248411278316551433509)
    ·
      refine ⟨31884984077114684353393783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170053248411278316551433509 31884984077114684353393783)
      ·
        refine ⟨47827476115672026530090675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31884984077114684353393783 47827476115672026530090675)
        ·
          refine ⟨71741214173508039795136013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47827476115672026530090675 71741214173508039795136013)
          ·
            refine ⟨26902955315065514923176005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71741214173508039795136013 26902955315065514923176005)
            ·
              refine ⟨5044304121574784048095501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26902955315065514923176005 5044304121574784048095501)
              ·
                refine ⟨1891614045590544018035813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5044304121574784048095501 1891614045590544018035813)
                ·
                  refine ⟨354677633548227003381715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1891614045590544018035813 354677633548227003381715)
                  ·
                    rfl

theorem cell22_3108295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 3, 4].length) (baseStart_3108295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3108295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3108295 prefixEnd_3108295 := by exact prefixLift 3108295
  have htrace : WordTrace (prefixWord ++ tailWord_3108295) baseStart_3108295 baseEnd_3108295 := by
    simpa [prefixWord, tailWord_3108295, baseEnd_3108295] using wordTrace_append hprefix tailTrace_3108295
  have hstable : (prefixWord ++ tailWord_3108295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108295).length < 2 ^ (prefixWord ++ tailWord_3108295).sum := by decide
  have hdescent : baseEnd_3108295 < baseStart_3108295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108383 : List Nat := [1, 1, 2, 4, 1, 1, 2, 3, 2, 5]
def baseStart_3108383 : Nat := 118140960795 + 3108383 * 2 ^ 59
def prefixEnd_3108383 : Nat := 4983230072969 + 3 ^ 40 * 3108383 * 2
def baseEnd_3108383 : Nat := 1064063024843078113944875

theorem tailTrace_3108383 : CollatzResearch.WordTrace tailWord_3108383 prefixEnd_3108383 1064063024843078113944875 := by
  unfold tailWord_3108383
  simp only [CollatzResearch.WordTrace]
  refine ⟨113372041897866735396825803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75581361265244490264550535 113372041897866735396825803)
  ·
    refine ⟨170058062846800103095238705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113372041897866735396825803 170058062846800103095238705)
    ·
      refine ⟨127543547135100077321429029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170058062846800103095238705 127543547135100077321429029)
      ·
        refine ⟨23914415087831264497767943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127543547135100077321429029 23914415087831264497767943)
        ·
          refine ⟨35871622631746896746651915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23914415087831264497767943 35871622631746896746651915)
          ·
            refine ⟨53807433947620345119977873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35871622631746896746651915 53807433947620345119977873)
            ·
              refine ⟨40355575460715258839983405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53807433947620345119977873 40355575460715258839983405)
              ·
                refine ⟨15133340797768222064993777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40355575460715258839983405 15133340797768222064993777)
                ·
                  refine ⟨11350005598326166548745333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15133340797768222064993777 11350005598326166548745333)
                  ·
                    refine ⟨1064063024843078113944875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11350005598326166548745333 1064063024843078113944875)
                    ·
                      rfl

theorem cell22_3108383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 5].length) (baseStart_3108383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3108383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3108383 prefixEnd_3108383 := by exact prefixLift 3108383
  have htrace : WordTrace (prefixWord ++ tailWord_3108383) baseStart_3108383 baseEnd_3108383 := by
    simpa [prefixWord, tailWord_3108383, baseEnd_3108383] using wordTrace_append hprefix tailTrace_3108383
  have hstable : (prefixWord ++ tailWord_3108383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108383).length < 2 ^ (prefixWord ++ tailWord_3108383).sum := by decide
  have hdescent : baseEnd_3108383 < baseStart_3108383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108385 : List Nat := [1, 2, 3, 2, 2, 3, 1, 3, 5]
def baseStart_3108385 : Nat := 118140960795 + 3108385 * 2 ^ 59
def prefixEnd_3108385 : Nat := 4983230072969 + 3 ^ 40 * 3108385 * 2
def baseEnd_3108385 : Nat := 354687903161316925131623

theorem tailTrace_3108385 : CollatzResearch.WordTrace tailWord_3108385 prefixEnd_3108385 354687903161316925131623 := by
  unfold tailWord_3108385
  simp only [CollatzResearch.WordTrace]
  refine ⟨113372114843859489738398609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75581409895906326492265739 113372114843859489738398609)
  ·
    refine ⟨85029086132894617303798957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113372114843859489738398609 85029086132894617303798957)
    ·
      refine ⟨31885907299835481488924609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85029086132894617303798957 31885907299835481488924609)
      ·
        refine ⟨23914430474876611116693457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31885907299835481488924609 23914430474876611116693457)
        ·
          refine ⟨17935822856157458337520093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23914430474876611116693457 17935822856157458337520093)
          ·
            refine ⟨6725933571059046876570035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17935822856157458337520093 6725933571059046876570035)
            ·
              refine ⟨10088900356588570314855053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6725933571059046876570035 10088900356588570314855053)
              ·
                refine ⟨3783337633720713868070645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10088900356588570314855053 3783337633720713868070645)
                ·
                  refine ⟨354687903161316925131623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3783337633720713868070645 354687903161316925131623)
                  ·
                    rfl

theorem cell22_3108385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 5].length) (baseStart_3108385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3108385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3108385 prefixEnd_3108385 := by exact prefixLift 3108385
  have htrace : WordTrace (prefixWord ++ tailWord_3108385) baseStart_3108385 baseEnd_3108385 := by
    simpa [prefixWord, tailWord_3108385, baseEnd_3108385] using wordTrace_append hprefix tailTrace_3108385
  have hstable : (prefixWord ++ tailWord_3108385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108385).length < 2 ^ (prefixWord ++ tailWord_3108385).sum := by decide
  have hdescent : baseEnd_3108385 < baseStart_3108385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108423 : List Nat := [1, 1, 4, 1, 6, 1, 2, 2, 1, 3]
def baseStart_3108423 : Nat := 118140960795 + 3108423 * 2 ^ 59
def prefixEnd_3108423 : Nat := 4983230072969 + 3 ^ 40 * 3108423 * 2
def baseEnd_3108423 : Nat := 1064076717660531342944753

theorem tailTrace_3108423 : CollatzResearch.WordTrace tailWord_3108423 prefixEnd_3108423 1064076717660531342944753 := by
  unfold tailWord_3108423
  simp only [CollatzResearch.WordTrace]
  refine ⟨113373500817721822228281923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75582333878481214818854615 113373500817721822228281923)
  ·
    refine ⟨170060251226582733342422885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113373500817721822228281923 170060251226582733342422885)
    ·
      refine ⟨31886297104984262501704291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170060251226582733342422885 31886297104984262501704291)
      ·
        refine ⟨47829445657476393752556437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31886297104984262501704291 47829445657476393752556437)
        ·
          refine ⟨2242005265194205957151083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47829445657476393752556437 2242005265194205957151083)
          ·
            refine ⟨3363007897791308935726625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2242005265194205957151083 3363007897791308935726625)
            ·
              refine ⟨2522255923343481701794969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3363007897791308935726625 2522255923343481701794969)
              ·
                refine ⟨1891691942507611276346227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2522255923343481701794969 1891691942507611276346227)
                ·
                  refine ⟨2837537913761416914519341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1891691942507611276346227 2837537913761416914519341)
                  ·
                    refine ⟨1064076717660531342944753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2837537913761416914519341 1064076717660531342944753)
                    ·
                      rfl

theorem cell22_3108423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_3108423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3108423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3108423 prefixEnd_3108423 := by exact prefixLift 3108423
  have htrace : WordTrace (prefixWord ++ tailWord_3108423) baseStart_3108423 baseEnd_3108423 := by
    simpa [prefixWord, tailWord_3108423, baseEnd_3108423] using wordTrace_append hprefix tailTrace_3108423
  have hstable : (prefixWord ++ tailWord_3108423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108423).length < 2 ^ (prefixWord ++ tailWord_3108423).sum := by decide
  have hdescent : baseEnd_3108423 < baseStart_3108423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108541 : List Nat := [1, 4, 1, 2, 1, 2, 5, 2, 1, 3]
def baseStart_3108541 : Nat := 118140960795 + 3108541 * 2 ^ 59
def prefixEnd_3108541 : Nat := 4983230072969 + 3 ^ 40 * 3108541 * 2
def baseEnd_3108541 : Nat := 1064117111472018368494391

theorem tailTrace_3108541 : CollatzResearch.WordTrace tailWord_3108541 prefixEnd_3108541 1064117111472018368494391 := by
  unfold tailWord_3108541
  simp only [CollatzResearch.WordTrace]
  refine ⟨113377804631294328381077477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75585203087529552254051651 113377804631294328381077477)
  ·
    refine ⟨21258338368367686571452027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113377804631294328381077477 21258338368367686571452027)
    ·
      refine ⟨31887507552551529857178041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21258338368367686571452027 31887507552551529857178041)
      ·
        refine ⟨23915630664413647392883531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31887507552551529857178041 23915630664413647392883531)
        ·
          refine ⟨35873445996620471089325297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23915630664413647392883531 35873445996620471089325297)
          ·
            refine ⟨26905084497465353316993973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35873445996620471089325297 26905084497465353316993973)
            ·
              refine ⟨2522351671637376873468185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26905084497465353316993973 2522351671637376873468185)
              ·
                refine ⟨1891763753728032655101139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2522351671637376873468185 1891763753728032655101139)
                ·
                  refine ⟨2837645630592048982651709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1891763753728032655101139 2837645630592048982651709)
                  ·
                    refine ⟨1064117111472018368494391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2837645630592048982651709 1064117111472018368494391)
                    ·
                      rfl

theorem cell22_3108541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_3108541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3108541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3108541 prefixEnd_3108541 := by exact prefixLift 3108541
  have htrace : WordTrace (prefixWord ++ tailWord_3108541) baseStart_3108541 baseEnd_3108541 := by
    simpa [prefixWord, tailWord_3108541, baseEnd_3108541] using wordTrace_append hprefix tailTrace_3108541
  have hstable : (prefixWord ++ tailWord_3108541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108541).length < 2 ^ (prefixWord ++ tailWord_3108541).sum := by decide
  have hdescent : baseEnd_3108541 < baseStart_3108541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108599 : List Nat := [1, 1, 3, 1, 1, 1, 8, 2, 4]
def baseStart_3108599 : Nat := 118140960795 + 3108599 * 2 ^ 59
def prefixEnd_3108599 : Nat := 4983230072969 + 3 ^ 40 * 3108599 * 2
def baseEnd_3108599 : Nat := 354712322019108516848071

theorem tailTrace_3108599 : CollatzResearch.WordTrace tailWord_3108599 prefixEnd_3108599 354712322019108516848071 := by
  unfold tailWord_3108599
  simp only [CollatzResearch.WordTrace]
  refine ⟨113379920065084204286688851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75586613376722802857792567 113379920065084204286688851)
  ·
    refine ⟨170069880097626306430033277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113379920065084204286688851 170069880097626306430033277)
    ·
      refine ⟨63776205036609864911262479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170069880097626306430033277 63776205036609864911262479)
      ·
        refine ⟨95664307554914797366893719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63776205036609864911262479 95664307554914797366893719)
        ·
          refine ⟨143496461332372196050340579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95664307554914797366893719 143496461332372196050340579)
          ·
            refine ⟨215244691998558294075510869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143496461332372196050340579 215244691998558294075510869)
            ·
              refine ⟨2522398734358105008697393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 215244691998558294075510869 2522398734358105008697393)
              ·
                refine ⟨1891799050768578756523045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2522398734358105008697393 1891799050768578756523045)
                ·
                  refine ⟨354712322019108516848071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1891799050768578756523045 354712322019108516848071)
                  ·
                    rfl

theorem cell22_3108599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 2, 4].length) (baseStart_3108599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3108599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3108599 prefixEnd_3108599 := by exact prefixLift 3108599
  have htrace : WordTrace (prefixWord ++ tailWord_3108599) baseStart_3108599 baseEnd_3108599 := by
    simpa [prefixWord, tailWord_3108599, baseEnd_3108599] using wordTrace_append hprefix tailTrace_3108599
  have hstable : (prefixWord ++ tailWord_3108599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108599).length < 2 ^ (prefixWord ++ tailWord_3108599).sum := by decide
  have hdescent : baseEnd_3108599 < baseStart_3108599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108629 : List Nat := [1, 3, 2, 1, 2, 5, 1, 1, 2, 4]
def baseStart_3108629 : Nat := 118140960795 + 3108629 * 2 ^ 59
def prefixEnd_3108629 : Nat := 4983230072969 + 3 ^ 40 * 3108629 * 2
def baseEnd_3108629 : Nat := 1064147235670415472294121

theorem tailTrace_3108629 : CollatzResearch.WordTrace tailWord_3108629 prefixEnd_3108629 1064147235670415472294121 := by
  unfold tailWord_3108629
  simp only [CollatzResearch.WordTrace]
  refine ⟨113381014254975519410280941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75587342836650346273520627 113381014254975519410280941)
  ·
    refine ⟨42517880345615819778855353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113381014254975519410280941 42517880345615819778855353)
    ·
      refine ⟨31888410259211864834141515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42517880345615819778855353 31888410259211864834141515)
      ·
        refine ⟨47832615388817797251212273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31888410259211864834141515 47832615388817797251212273)
        ·
          refine ⟨35874461541613347938409205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47832615388817797251212273 35874461541613347938409205)
          ·
            refine ⟨3363230769526251369225863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35874461541613347938409205 3363230769526251369225863)
            ·
              refine ⟨5044846154289377053838795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3363230769526251369225863 5044846154289377053838795)
              ·
                refine ⟨7567269231434065580758193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5044846154289377053838795 7567269231434065580758193)
                ·
                  refine ⟨5675451923575549185568645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7567269231434065580758193 5675451923575549185568645)
                  ·
                    refine ⟨1064147235670415472294121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5675451923575549185568645 1064147235670415472294121)
                    ·
                      rfl

theorem cell22_3108629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_3108629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3108629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3108629 prefixEnd_3108629 := by exact prefixLift 3108629
  have htrace : WordTrace (prefixWord ++ tailWord_3108629) baseStart_3108629 baseEnd_3108629 := by
    simpa [prefixWord, tailWord_3108629, baseEnd_3108629] using wordTrace_append hprefix tailTrace_3108629
  have hstable : (prefixWord ++ tailWord_3108629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108629).length < 2 ^ (prefixWord ++ tailWord_3108629).sum := by decide
  have hdescent : baseEnd_3108629 < baseStart_3108629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108655 : List Nat := [1, 1, 2, 1, 2, 1, 2, 5, 7]
def baseStart_3108655 : Nat := 118140960795 + 3108655 * 2 ^ 59
def prefixEnd_3108655 : Nat := 4983230072969 + 3 ^ 40 * 3108655 * 2
def baseEnd_3108655 : Nat := 354718712000586690381347

theorem tailTrace_3108655 : CollatzResearch.WordTrace tailWord_3108655 prefixEnd_3108655 354718712000586690381347 := by
  unfold tailWord_3108655
  simp only [CollatzResearch.WordTrace]
  refine ⟨113381962552881325850727419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75587975035254217233818279 113381962552881325850727419)
  ·
    refine ⟨170072943829321988776091129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113381962552881325850727419 170072943829321988776091129)
    ·
      refine ⟨127554707871991491582068347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170072943829321988776091129 127554707871991491582068347)
      ·
        refine ⟨191332061807987237373102521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127554707871991491582068347 191332061807987237373102521)
        ·
          refine ⟨143499046355990428029826891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191332061807987237373102521 143499046355990428029826891)
          ·
            refine ⟨215248569533985642044740337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143499046355990428029826891 215248569533985642044740337)
            ·
              refine ⟨161436427150489231533555253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215248569533985642044740337 161436427150489231533555253)
              ·
                refine ⟨15134665045358365456270805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 161436427150489231533555253 15134665045358365456270805)
                ·
                  refine ⟨354718712000586690381347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15134665045358365456270805 354718712000586690381347)
                  ·
                    rfl

theorem cell22_3108655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 7].length) (baseStart_3108655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3108655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3108655 prefixEnd_3108655 := by exact prefixLift 3108655
  have htrace : WordTrace (prefixWord ++ tailWord_3108655) baseStart_3108655 baseEnd_3108655 := by
    simpa [prefixWord, tailWord_3108655, baseEnd_3108655] using wordTrace_append hprefix tailTrace_3108655
  have hstable : (prefixWord ++ tailWord_3108655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108655).length < 2 ^ (prefixWord ++ tailWord_3108655).sum := by decide
  have hdescent : baseEnd_3108655 < baseStart_3108655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108678 : List Nat := [6, 1, 1, 2, 1, 3, 2, 6]
def baseStart_3108678 : Nat := 118140960795 + 3108678 * 2 ^ 59
def prefixEnd_3108678 : Nat := 4983230072969 + 3 ^ 40 * 3108678 * 2
def baseEnd_3108678 : Nat := 118240445485755075313219

theorem tailTrace_3108678 : CollatzResearch.WordTrace tailWord_3108678 prefixEnd_3108678 118240445485755075313219 := by
  unfold tailWord_3108678
  simp only [CollatzResearch.WordTrace]
  refine ⟨3543212544743687524337959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 75588534287865333852543125 3543212544743687524337959)
  ·
    refine ⟨5314818817115531286506939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3543212544743687524337959 5314818817115531286506939)
    ·
      refine ⟨7972228225673296929760409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5314818817115531286506939 7972228225673296929760409)
      ·
        refine ⟨5979171169254972697320307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7972228225673296929760409 5979171169254972697320307)
        ·
          refine ⟨8968756753882459045980461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5979171169254972697320307 8968756753882459045980461)
          ·
            refine ⟨3363283782705922142242673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8968756753882459045980461 3363283782705922142242673)
            ·
              refine ⟨2522462837029441606682005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3363283782705922142242673 2522462837029441606682005)
              ·
                refine ⟨118240445485755075313219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2522462837029441606682005 118240445485755075313219)
                ·
                  rfl

theorem cell22_3108678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_3108678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3108678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3108678 prefixEnd_3108678 := by exact prefixLift 3108678
  have htrace : WordTrace (prefixWord ++ tailWord_3108678) baseStart_3108678 baseEnd_3108678 := by
    simpa [prefixWord, tailWord_3108678, baseEnd_3108678] using wordTrace_append hprefix tailTrace_3108678
  have hstable : (prefixWord ++ tailWord_3108678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108678).length < 2 ^ (prefixWord ++ tailWord_3108678).sum := by decide
  have hdescent : baseEnd_3108678 < baseStart_3108678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108693 : List Nat := [1, 3, 2, 2, 2, 4, 1, 3, 1, 3]
def baseStart_3108693 : Nat := 118140960795 + 3108693 * 2 ^ 59
def prefixEnd_3108693 : Nat := 4983230072969 + 3 ^ 40 * 3108693 * 2
def baseEnd_3108693 : Nat := 1064169144178340638693925

theorem tailTrace_3108693 : CollatzResearch.WordTrace tailWord_3108693 prefixEnd_3108693 1064169144178340638693925 := by
  unfold tailWord_3108693
  simp only [CollatzResearch.WordTrace]
  refine ⟨113383348526743658340610733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75588899017829105560407155 113383348526743658340610733)
  ·
    refine ⟨42518755697528871877729025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113383348526743658340610733 42518755697528871877729025)
    ·
      refine ⟨31889066773146653908296769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42518755697528871877729025 31889066773146653908296769)
      ·
        refine ⟨23916800079859990431222577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31889066773146653908296769 23916800079859990431222577)
        ·
          refine ⟨17937600059894992823416933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23916800079859990431222577 17937600059894992823416933)
          ·
            refine ⟨3363300011230311154390675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17937600059894992823416933 3363300011230311154390675)
            ·
              refine ⟨5044950016845466731586013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3363300011230311154390675 5044950016845466731586013)
              ·
                refine ⟨1891856256317050024344755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5044950016845466731586013 1891856256317050024344755)
                ·
                  refine ⟨2837784384475575036517133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1891856256317050024344755 2837784384475575036517133)
                  ·
                    refine ⟨1064169144178340638693925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2837784384475575036517133 1064169144178340638693925)
                    ·
                      rfl

theorem cell22_3108693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_3108693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3108693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3108693 prefixEnd_3108693 := by exact prefixLift 3108693
  have htrace : WordTrace (prefixWord ++ tailWord_3108693) baseStart_3108693 baseEnd_3108693 := by
    simpa [prefixWord, tailWord_3108693, baseEnd_3108693] using wordTrace_append hprefix tailTrace_3108693
  have hstable : (prefixWord ++ tailWord_3108693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108693).length < 2 ^ (prefixWord ++ tailWord_3108693).sum := by decide
  have hdescent : baseEnd_3108693 < baseStart_3108693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108762 : List Nat := [3, 1, 1, 4, 2, 11]
def baseStart_3108762 : Nat := 118140960795 + 3108762 * 2 ^ 59
def prefixEnd_3108762 : Nat := 4983230072969 + 3 ^ 40 * 3108762 * 2
def baseEnd_3108762 : Nat := 13138182275166018008873

theorem tailTrace_3108762 : CollatzResearch.WordTrace tailWord_3108762 prefixEnd_3108762 13138182275166018008873 := by
  unfold tailWord_3108762
  simp only [CollatzResearch.WordTrace]
  refine ⟨28346466290873420781218135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75590576775662455416581693 28346466290873420781218135)
  ·
    refine ⟨42519699436310131171827203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28346466290873420781218135 42519699436310131171827203)
    ·
      refine ⟨63779549154465196757740805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42519699436310131171827203 63779549154465196757740805)
      ·
        refine ⟨11958665466462224392076401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63779549154465196757740805 11958665466462224392076401)
        ·
          refine ⟨8968999099846668294057301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11958665466462224392076401 8968999099846668294057301)
          ·
            refine ⟨13138182275166018008873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8968999099846668294057301 13138182275166018008873)
            ·
              rfl

theorem cell22_3108762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 11].length) (baseStart_3108762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3108762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3108762 prefixEnd_3108762 := by exact prefixLift 3108762
  have htrace : WordTrace (prefixWord ++ tailWord_3108762) baseStart_3108762 baseEnd_3108762 := by
    simpa [prefixWord, tailWord_3108762, baseEnd_3108762] using wordTrace_append hprefix tailTrace_3108762
  have hstable : (prefixWord ++ tailWord_3108762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108762).length < 2 ^ (prefixWord ++ tailWord_3108762).sum := by decide
  have hdescent : baseEnd_3108762 < baseStart_3108762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108792 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 2, 6]
def baseStart_3108792 : Nat := 118140960795 + 3108792 * 2 ^ 59
def prefixEnd_3108792 : Nat := 4983230072969 + 3 ^ 40 * 3108792 * 2
def baseEnd_3108792 : Nat := 1064203033901537380468621

theorem tailTrace_3108792 : CollatzResearch.WordTrace tailWord_3108792 prefixEnd_3108792 1064203033901537380468621 := by
  unfold tailWord_3108792
  simp only [CollatzResearch.WordTrace]
  refine ⟨56693479676692499124232315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75591306235589998832309753 56693479676692499124232315)
  ·
    refine ⟨85040219515038748686348473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56693479676692499124232315 85040219515038748686348473)
    ·
      refine ⟨63780164636279061514761355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85040219515038748686348473 63780164636279061514761355)
      ·
        refine ⟨95670246954418592272142033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63780164636279061514761355 95670246954418592272142033)
        ·
          refine ⟨71752685215813944204106525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95670246954418592272142033 71752685215813944204106525)
          ·
            refine ⟨26907256955930229076539947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71752685215813944204106525 26907256955930229076539947)
            ·
              refine ⟨40360885433895343614809921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26907256955930229076539947 40360885433895343614809921)
              ·
                refine ⟨30270664075421507711107441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40360885433895343614809921 30270664075421507711107441)
                ·
                  refine ⟨22702998056566130783330581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30270664075421507711107441 22702998056566130783330581)
                  ·
                    refine ⟨1064203033901537380468621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22702998056566130783330581 1064203033901537380468621)
                    ·
                      rfl

theorem cell22_3108792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_3108792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3108792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3108792 prefixEnd_3108792 := by exact prefixLift 3108792
  have htrace : WordTrace (prefixWord ++ tailWord_3108792) baseStart_3108792 baseEnd_3108792 := by
    simpa [prefixWord, tailWord_3108792, baseEnd_3108792] using wordTrace_append hprefix tailTrace_3108792
  have hstable : (prefixWord ++ tailWord_3108792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108792).length < 2 ^ (prefixWord ++ tailWord_3108792).sum := by decide
  have hdescent : baseEnd_3108792 < baseStart_3108792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108807 : List Nat := [1, 1, 4, 1, 1, 2, 1, 4, 7]
def baseStart_3108807 : Nat := 118140960795 + 3108807 * 2 ^ 59
def prefixEnd_3108807 : Nat := 4983230072969 + 3 ^ 40 * 3108807 * 2
def baseEnd_3108807 : Nat := 354736056236027447114525

theorem tailTrace_3108807 : CollatzResearch.WordTrace tailWord_3108807 prefixEnd_3108807 354736056236027447114525 := by
  unfold tailWord_3108807
  simp only [CollatzResearch.WordTrace]
  refine ⟨113387506448330655810260675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75591670965553770540173783 113387506448330655810260675)
  ·
    refine ⟨170081259672495983715391013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113387506448330655810260675 170081259672495983715391013)
    ·
      refine ⟨31890236188592996946635815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170081259672495983715391013 31890236188592996946635815)
      ·
        refine ⟨47835354282889495419953723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31890236188592996946635815 47835354282889495419953723)
        ·
          refine ⟨71753031424334243129930585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47835354282889495419953723 71753031424334243129930585)
          ·
            refine ⟨53814773568250682347447939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71753031424334243129930585 53814773568250682347447939)
            ·
              refine ⟨80722160352376023521171909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53814773568250682347447939 80722160352376023521171909)
              ·
                refine ⟨15135405066070504410219733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80722160352376023521171909 15135405066070504410219733)
                ·
                  refine ⟨354736056236027447114525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15135405066070504410219733 354736056236027447114525)
                  ·
                    rfl

theorem cell22_3108807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 7].length) (baseStart_3108807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3108807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3108807 prefixEnd_3108807 := by exact prefixLift 3108807
  have htrace : WordTrace (prefixWord ++ tailWord_3108807) baseStart_3108807 baseEnd_3108807 := by
    simpa [prefixWord, tailWord_3108807, baseEnd_3108807] using wordTrace_append hprefix tailTrace_3108807
  have hstable : (prefixWord ++ tailWord_3108807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108807).length < 2 ^ (prefixWord ++ tailWord_3108807).sum := by decide
  have hdescent : baseEnd_3108807 < baseStart_3108807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108862 : List Nat := [4, 2, 2, 2, 1, 3, 1, 3, 1, 3]
def baseStart_3108862 : Nat := 118140960795 + 3108862 * 2 ^ 59
def prefixEnd_3108862 : Nat := 4983230072969 + 3 ^ 40 * 3108862 * 2
def baseEnd_3108862 : Nat := 1064226996332080531218407

theorem tailTrace_3108862 : CollatzResearch.WordTrace tailWord_3108862 prefixEnd_3108862 1064226996332080531218407 := by
  unfold tailWord_3108862
  simp only [CollatzResearch.WordTrace]
  refine ⟨14173689057891425025439105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75593008308754266802341893 14173689057891425025439105)
  ·
    refine ⟨10630266793418568769079329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14173689057891425025439105 10630266793418568769079329)
    ·
      refine ⟨7972700095063926576809497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10630266793418568769079329 7972700095063926576809497)
      ·
        refine ⟨5979525071297944932607123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7972700095063926576809497 5979525071297944932607123)
        ·
          refine ⟨8969287606946917398910685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5979525071297944932607123 8969287606946917398910685)
          ·
            refine ⟨3363482852605094024591507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8969287606946917398910685 3363482852605094024591507)
            ·
              refine ⟨5045224278907641036887261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3363482852605094024591507 5045224278907641036887261)
              ·
                refine ⟨1891959104590365388832723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5045224278907641036887261 1891959104590365388832723)
                ·
                  refine ⟨2837938656885548083249085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1891959104590365388832723 2837938656885548083249085)
                  ·
                    refine ⟨1064226996332080531218407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2837938656885548083249085 1064226996332080531218407)
                    ·
                      rfl

theorem cell22_3108862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_3108862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3108862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3108862 prefixEnd_3108862 := by exact prefixLift 3108862
  have htrace : WordTrace (prefixWord ++ tailWord_3108862) baseStart_3108862 baseEnd_3108862 := by
    simpa [prefixWord, tailWord_3108862, baseEnd_3108862] using wordTrace_append hprefix tailTrace_3108862
  have hstable : (prefixWord ++ tailWord_3108862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108862).length < 2 ^ (prefixWord ++ tailWord_3108862).sum := by decide
  have hdescent : baseEnd_3108862 < baseStart_3108862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108871 : List Nat := [1, 1, 4, 3, 1, 2, 2, 3, 1, 4]
def baseStart_3108871 : Nat := 118140960795 + 3108871 * 2 ^ 59
def prefixEnd_3108871 : Nat := 4983230072969 + 3 ^ 40 * 3108871 * 2
def baseEnd_3108871 : Nat := 1064230077216007507743379

theorem tailTrace_3108871 : CollatzResearch.WordTrace tailWord_3108871 prefixEnd_3108871 1064230077216007507743379 := by
  unfold tailWord_3108871
  simp only [CollatzResearch.WordTrace]
  refine ⟨113389840720098794740590467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75593227146732529827060311 113389840720098794740590467)
  ·
    refine ⟨170084761080148192110885701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113389840720098794740590467 170084761080148192110885701)
    ·
      refine ⟨31890892702527786020791069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170084761080148192110885701 31890892702527786020791069)
      ·
        refine ⟨11959084763447919757796651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31890892702527786020791069 11959084763447919757796651)
        ·
          refine ⟨17938627145171879636694977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11959084763447919757796651 17938627145171879636694977)
          ·
            refine ⟨13453970358878909727521233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17938627145171879636694977 13453970358878909727521233)
            ·
              refine ⟨10090477769159182295640925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13453970358878909727521233 10090477769159182295640925)
              ·
                refine ⟨3783929163434693360865347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10090477769159182295640925 3783929163434693360865347)
                ·
                  refine ⟨5675893745152040041298021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3783929163434693360865347 5675893745152040041298021)
                  ·
                    refine ⟨1064230077216007507743379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5675893745152040041298021 1064230077216007507743379)
                    ·
                      rfl

theorem cell22_3108871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_3108871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3108871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3108871 prefixEnd_3108871 := by exact prefixLift 3108871
  have htrace : WordTrace (prefixWord ++ tailWord_3108871) baseStart_3108871 baseEnd_3108871 := by
    simpa [prefixWord, tailWord_3108871, baseEnd_3108871] using wordTrace_append hprefix tailTrace_3108871
  have hstable : (prefixWord ++ tailWord_3108871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108871).length < 2 ^ (prefixWord ++ tailWord_3108871).sum := by decide
  have hdescent : baseEnd_3108871 < baseStart_3108871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108899 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 4, 4]
def baseStart_3108899 : Nat := 118140960795 + 3108899 * 2 ^ 59
def prefixEnd_3108899 : Nat := 4983230072969 + 3 ^ 40 * 3108899 * 2
def baseEnd_3108899 : Nat := 1064239662188224768043293

theorem tailTrace_3108899 : CollatzResearch.WordTrace tailWord_3108899 prefixEnd_3108899 1064239662188224768043293 := by
  unfold tailWord_3108899
  simp only [CollatzResearch.WordTrace]
  refine ⟨113390861963997355522609751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75593907975998237015073167 113390861963997355522609751)
  ·
    refine ⟨170086292945996033283914627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113390861963997355522609751 170086292945996033283914627)
    ·
      refine ⟨255129439418994049925871941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170086292945996033283914627 255129439418994049925871941)
      ·
        refine ⟨47836769891061384361100989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 255129439418994049925871941 47836769891061384361100989)
        ·
          refine ⟨17938788709148019135412871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47836769891061384361100989 17938788709148019135412871)
          ·
            refine ⟨26908183063722028703119307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17938788709148019135412871 26908183063722028703119307)
            ·
              refine ⟨40362274595583043054678961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26908183063722028703119307 40362274595583043054678961)
              ·
                refine ⟨30271705946687282291009221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40362274595583043054678961 30271705946687282291009221)
                ·
                  refine ⟨5675944865003865429564229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30271705946687282291009221 5675944865003865429564229)
                  ·
                    refine ⟨1064239662188224768043293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5675944865003865429564229 1064239662188224768043293)
                    ·
                      rfl

theorem cell22_3108899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 4].length) (baseStart_3108899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3108899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3108899 prefixEnd_3108899 := by exact prefixLift 3108899
  have htrace : WordTrace (prefixWord ++ tailWord_3108899) baseStart_3108899 baseEnd_3108899 := by
    simpa [prefixWord, tailWord_3108899, baseEnd_3108899] using wordTrace_append hprefix tailTrace_3108899
  have hstable : (prefixWord ++ tailWord_3108899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108899).length < 2 ^ (prefixWord ++ tailWord_3108899).sum := by decide
  have hdescent : baseEnd_3108899 < baseStart_3108899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3108914 : List Nat := [3, 2, 1, 1, 2, 3, 2, 8]
def baseStart_3108914 : Nat := 118140960795 + 3108914 * 2 ^ 59
def prefixEnd_3108914 : Nat := 4983230072969 + 3 ^ 40 * 3108914 * 2
def baseEnd_3108914 : Nat := 118249421888307747657583

theorem tailTrace_3108914 : CollatzResearch.WordTrace tailWord_3108914 prefixEnd_3108914 118249421888307747657583 := by
  unfold tailWord_3108914
  simp only [CollatzResearch.WordTrace]
  refine ⟨28347852264735753271101449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75594272705962008722937197 28347852264735753271101449)
  ·
    refine ⟨21260889198551814953326087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28347852264735753271101449 21260889198551814953326087)
    ·
      refine ⟨31891333797827722429989131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21260889198551814953326087 31891333797827722429989131)
      ·
        refine ⟨47837000696741583644983697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31891333797827722429989131 47837000696741583644983697)
        ·
          refine ⟨35877750522556187733737773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47837000696741583644983697 35877750522556187733737773)
          ·
            refine ⟨13454156445958570400151665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35877750522556187733737773 13454156445958570400151665)
            ·
              refine ⟨10090617334468927800113749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13454156445958570400151665 10090617334468927800113749)
              ·
                refine ⟨118249421888307747657583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10090617334468927800113749 118249421888307747657583)
                ·
                  rfl

theorem cell22_3108914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 8].length) (baseStart_3108914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3108914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3108914 prefixEnd_3108914 := by exact prefixLift 3108914
  have htrace : WordTrace (prefixWord ++ tailWord_3108914) baseStart_3108914 baseEnd_3108914 := by
    simpa [prefixWord, tailWord_3108914, baseEnd_3108914] using wordTrace_append hprefix tailTrace_3108914
  have hstable : (prefixWord ++ tailWord_3108914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3108914).length < 2 ^ (prefixWord ++ tailWord_3108914).sum := by decide
  have hdescent : baseEnd_3108914 < baseStart_3108914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3108914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109019 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 5, 5]
def baseStart_3109019 : Nat := 118140960795 + 3109019 * 2 ^ 59
def prefixEnd_3109019 : Nat := 4983230072969 + 3 ^ 40 * 3109019 * 2
def baseEnd_3109019 : Nat := 1064280740640584455042925

theorem tailTrace_3109019 : CollatzResearch.WordTrace tailWord_3109019 prefixEnd_3109019 1064280740640584455042925 := by
  unfold tailWord_3109019
  simp only [CollatzResearch.WordTrace]
  refine ⟨113395238723562616016978111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75596825815708410677985407 113395238723562616016978111)
  ·
    refine ⟨170092858085343924025467167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113395238723562616016978111 170092858085343924025467167)
    ·
      refine ⟨255139287128015886038200751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170092858085343924025467167 255139287128015886038200751)
      ·
        refine ⟨382708930692023829057301127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255139287128015886038200751 382708930692023829057301127)
        ·
          refine ⟨574063396038035743585951691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382708930692023829057301127 574063396038035743585951691)
          ·
            refine ⟨861095094057053615378927537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574063396038035743585951691 861095094057053615378927537)
            ·
              refine ⟨645821320542790211534195653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 861095094057053615378927537 645821320542790211534195653)
              ·
                refine ⟨121091497601773164662661685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 645821320542790211534195653 121091497601773164662661685)
                ·
                  refine ⟨11352327900166234187124533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 121091497601773164662661685 11352327900166234187124533)
                  ·
                    refine ⟨1064280740640584455042925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11352327900166234187124533 1064280740640584455042925)
                    ·
                      rfl

theorem cell22_3109019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 5].length) (baseStart_3109019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109019 prefixEnd_3109019 := by exact prefixLift 3109019
  have htrace : WordTrace (prefixWord ++ tailWord_3109019) baseStart_3109019 baseEnd_3109019 := by
    simpa [prefixWord, tailWord_3109019, baseEnd_3109019] using wordTrace_append hprefix tailTrace_3109019
  have hstable : (prefixWord ++ tailWord_3109019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109019).length < 2 ^ (prefixWord ++ tailWord_3109019).sum := by decide
  have hdescent : baseEnd_3109019 < baseStart_3109019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109021 : List Nat := [1, 4, 2, 1, 1, 3, 2, 2, 6]
def baseStart_3109021 : Nat := 118140960795 + 3109021 * 2 ^ 59
def prefixEnd_3109021 : Nat := 4983230072969 + 3 ^ 40 * 3109021 * 2
def baseEnd_3109021 : Nat := 354760475093819038830973

theorem tailTrace_3109021 : CollatzResearch.WordTrace tailWord_3109021 prefixEnd_3109021 354760475093819038830973 := by
  unfold tailWord_3109021
  simp only [CollatzResearch.WordTrace]
  refine ⟨113395311669555370358550917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75596874446370246905700611 113395311669555370358550917)
  ·
    refine ⟨21261620938041631942228297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113395311669555370358550917 21261620938041631942228297)
    ·
      refine ⟨15946215703531223956671223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21261620938041631942228297 15946215703531223956671223)
      ·
        refine ⟨23919323555296835935006835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15946215703531223956671223 23919323555296835935006835)
        ·
          refine ⟨35878985332945253902510253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23919323555296835935006835 35878985332945253902510253)
          ·
            refine ⟨13454619499854470213441345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35878985332945253902510253 13454619499854470213441345)
            ·
              refine ⟨10090964624890852660081009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13454619499854470213441345 10090964624890852660081009)
              ·
                refine ⟨7568223468668139495060757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10090964624890852660081009 7568223468668139495060757)
                ·
                  refine ⟨354760475093819038830973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7568223468668139495060757 354760475093819038830973)
                  ·
                    rfl

theorem cell22_3109021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_3109021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109021 prefixEnd_3109021 := by exact prefixLift 3109021
  have htrace : WordTrace (prefixWord ++ tailWord_3109021) baseStart_3109021 baseEnd_3109021 := by
    simpa [prefixWord, tailWord_3109021, baseEnd_3109021] using wordTrace_append hprefix tailTrace_3109021
  have hstable : (prefixWord ++ tailWord_3109021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109021).length < 2 ^ (prefixWord ++ tailWord_3109021).sum := by decide
  have hdescent : baseEnd_3109021 < baseStart_3109021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109023 : List Nat := [1, 1, 2, 6, 1, 1, 1, 4, 1, 4]
def baseStart_3109023 : Nat := 118140960795 + 3109023 * 2 ^ 59
def prefixEnd_3109023 : Nat := 4983230072969 + 3 ^ 40 * 3109023 * 2
def baseEnd_3109023 : Nat := 1064282109922329777942913

theorem tailTrace_3109023 : CollatzResearch.WordTrace tailWord_3109023 prefixEnd_3109023 1064282109922329777942913 := by
  unfold tailWord_3109023
  simp only [CollatzResearch.WordTrace]
  refine ⟨113395384615548124700123723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75596923077032083133415815 113395384615548124700123723)
  ·
    refine ⟨170093076923322187050185585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113395384615548124700123723 170093076923322187050185585)
    ·
      refine ⟨127569807692491640287639189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170093076923322187050185585 127569807692491640287639189)
      ·
        refine ⟨5979834735585545638483087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 127569807692491640287639189 5979834735585545638483087)
        ·
          refine ⟨8969752103378318457724631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5979834735585545638483087 8969752103378318457724631)
          ·
            refine ⟨13454628155067477686586947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8969752103378318457724631 13454628155067477686586947)
            ·
              refine ⟨20181942232601216529880421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13454628155067477686586947 20181942232601216529880421)
              ·
                refine ⟨3784114168612728099352579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20181942232601216529880421 3784114168612728099352579)
                ·
                  refine ⟨5676171252919092149028869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3784114168612728099352579 5676171252919092149028869)
                  ·
                    refine ⟨1064282109922329777942913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5676171252919092149028869 1064282109922329777942913)
                    ·
                      rfl

theorem cell22_3109023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 4].length) (baseStart_3109023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109023 prefixEnd_3109023 := by exact prefixLift 3109023
  have htrace : WordTrace (prefixWord ++ tailWord_3109023) baseStart_3109023 baseEnd_3109023 := by
    simpa [prefixWord, tailWord_3109023, baseEnd_3109023] using wordTrace_append hprefix tailTrace_3109023
  have hstable : (prefixWord ++ tailWord_3109023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109023).length < 2 ^ (prefixWord ++ tailWord_3109023).sum := by decide
  have hdescent : baseEnd_3109023 < baseStart_3109023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109051 : List Nat := [1, 1, 1, 1, 1, 2, 7, 2, 2, 4]
def baseStart_3109051 : Nat := 118140960795 + 3109051 * 2 ^ 59
def prefixEnd_3109051 : Nat := 4983230072969 + 3 ^ 40 * 3109051 * 2
def baseEnd_3109051 : Nat := 1064291694894547038242827

theorem tailTrace_3109051 : CollatzResearch.WordTrace tailWord_3109051 prefixEnd_3109051 1064291694894547038242827 := by
  unfold tailWord_3109051
  simp only [CollatzResearch.WordTrace]
  refine ⟨113396405859446685482143007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75597603906297790321428671 113396405859446685482143007)
  ·
    refine ⟨170094608789170028223214511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113396405859446685482143007 170094608789170028223214511)
    ·
      refine ⟨255141913183755042334821767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170094608789170028223214511 255141913183755042334821767)
      ·
        refine ⟨382712869775632563502232651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255141913183755042334821767 382712869775632563502232651)
        ·
          refine ⟨574069304663448845253348977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382712869775632563502232651 574069304663448845253348977)
          ·
            refine ⟨430551978497586633940011733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 574069304663448845253348977 430551978497586633940011733)
            ·
              refine ⟨10091061996037186732969025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 430551978497586633940011733 10091061996037186732969025)
              ·
                refine ⟨7568296497027890049726769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10091061996037186732969025 7568296497027890049726769)
                ·
                  refine ⟨5676222372770917537295077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7568296497027890049726769 5676222372770917537295077)
                  ·
                    refine ⟨1064291694894547038242827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5676222372770917537295077 1064291694894547038242827)
                    ·
                      rfl

theorem cell22_3109051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 4].length) (baseStart_3109051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109051 prefixEnd_3109051 := by exact prefixLift 3109051
  have htrace : WordTrace (prefixWord ++ tailWord_3109051) baseStart_3109051 baseEnd_3109051 := by
    simpa [prefixWord, tailWord_3109051, baseEnd_3109051] using wordTrace_append hprefix tailTrace_3109051
  have hstable : (prefixWord ++ tailWord_3109051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109051).length < 2 ^ (prefixWord ++ tailWord_3109051).sum := by decide
  have hdescent : baseEnd_3109051 < baseStart_3109051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109053 : List Nat := [1, 4, 1, 2, 1, 1, 1, 6, 2, 3]
def baseStart_3109053 : Nat := 118140960795 + 3109053 * 2 ^ 59
def prefixEnd_3109053 : Nat := 4983230072969 + 3 ^ 40 * 3109053 * 2
def baseEnd_3109053 : Nat := 1064292379535419699692821

theorem tailTrace_3109053 : CollatzResearch.WordTrace tailWord_3109053 prefixEnd_3109053 1064292379535419699692821 := by
  unfold tailWord_3109053
  simp only [CollatzResearch.WordTrace]
  refine ⟨113396478805439439823715813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75597652536959626549143875 113396478805439439823715813)
  ·
    refine ⟨21261839776019894966946715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113396478805439439823715813 21261839776019894966946715)
    ·
      refine ⟨31892759664029842450420073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21261839776019894966946715 31892759664029842450420073)
      ·
        refine ⟨23919569748022381837815055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31892759664029842450420073 23919569748022381837815055)
        ·
          refine ⟨35879354622033572756722583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23919569748022381837815055 35879354622033572756722583)
          ·
            refine ⟨53819031933050359135083875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35879354622033572756722583 53819031933050359135083875)
            ·
              refine ⟨80728547899575538702625813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53819031933050359135083875 80728547899575538702625813)
              ·
                refine ⟨3784150682792603376685585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 80728547899575538702625813 3784150682792603376685585)
                ·
                  refine ⟨2838113012094452532514189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3784150682792603376685585 2838113012094452532514189)
                  ·
                    refine ⟨1064292379535419699692821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2838113012094452532514189 1064292379535419699692821)
                    ·
                      rfl

theorem cell22_3109053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_3109053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109053 prefixEnd_3109053 := by exact prefixLift 3109053
  have htrace : WordTrace (prefixWord ++ tailWord_3109053) baseStart_3109053 baseEnd_3109053 := by
    simpa [prefixWord, tailWord_3109053, baseEnd_3109053] using wordTrace_append hprefix tailTrace_3109053
  have hstable : (prefixWord ++ tailWord_3109053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109053).length < 2 ^ (prefixWord ++ tailWord_3109053).sum := by decide
  have hdescent : baseEnd_3109053 < baseStart_3109053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109066 : List Nat := [3, 1, 2, 1, 3, 1, 4, 7]
def baseStart_3109066 : Nat := 118140960795 + 3109066 * 2 ^ 59
def prefixEnd_3109066 : Nat := 4983230072969 + 3 ^ 40 * 3109066 * 2
def baseEnd_3109066 : Nat := 118255203300121333235309

theorem tailTrace_3109066 : CollatzResearch.WordTrace tailWord_3109066 prefixEnd_3109066 118255203300121333235309 := by
  unfold tailWord_3109066
  simp only [CollatzResearch.WordTrace]
  refine ⟨28349238238598085760984763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75597968636261562029292701 28349238238598085760984763)
  ·
    refine ⟨42523857357897128641477145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28349238238598085760984763 42523857357897128641477145)
    ·
      refine ⟨31892893018422846481107859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42523857357897128641477145 31892893018422846481107859)
      ·
        refine ⟨47839339527634269721661789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31892893018422846481107859 47839339527634269721661789)
        ·
          refine ⟨17939752322862851145623171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47839339527634269721661789 17939752322862851145623171)
          ·
            refine ⟨26909628484294276718434757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17939752322862851145623171 26909628484294276718434757)
            ·
              refine ⟨5045555340805176884706517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26909628484294276718434757 5045555340805176884706517)
              ·
                refine ⟨118255203300121333235309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5045555340805176884706517 118255203300121333235309)
                ·
                  rfl

theorem cell22_3109066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 7].length) (baseStart_3109066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109066 prefixEnd_3109066 := by exact prefixLift 3109066
  have htrace : WordTrace (prefixWord ++ tailWord_3109066) baseStart_3109066 baseEnd_3109066 := by
    simpa [prefixWord, tailWord_3109066, baseEnd_3109066] using wordTrace_append hprefix tailTrace_3109066
  have hstable : (prefixWord ++ tailWord_3109066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109066).length < 2 ^ (prefixWord ++ tailWord_3109066).sum := by decide
  have hdescent : baseEnd_3109066 < baseStart_3109066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109070 : List Nat := [4, 1, 1, 1, 4, 2, 1, 3, 2, 3]
def baseStart_3109070 : Nat := 118140960795 + 3109070 * 2 ^ 59
def prefixEnd_3109070 : Nat := 4983230072969 + 3 ^ 40 * 3109070 * 2
def baseEnd_3109070 : Nat := 1064298198982837322017769

theorem tailTrace_3109070 : CollatzResearch.WordTrace tailWord_3109070 prefixEnd_3109070 1064298198982837322017769 := by
  unfold tailWord_3109070
  simp only [CollatzResearch.WordTrace]
  refine ⟨14174637355797231465885583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75598065897585234484723109 14174637355797231465885583)
  ·
    refine ⟨21261956033695847198828375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14174637355797231465885583 21261956033695847198828375)
    ·
      refine ⟨31892934050543770798242563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21261956033695847198828375 31892934050543770798242563)
      ·
        refine ⟨47839401075815656197363845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31892934050543770798242563 47839401075815656197363845)
        ·
          refine ⟨8969887701715435537005721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47839401075815656197363845 8969887701715435537005721)
          ·
            refine ⟨6727415776286576652754291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8969887701715435537005721 6727415776286576652754291)
            ·
              refine ⟨10091123664429864979131437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6727415776286576652754291 10091123664429864979131437)
              ·
                refine ⟨3784171374161199367174289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10091123664429864979131437 3784171374161199367174289)
                ·
                  refine ⟨2838128530620899525380717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3784171374161199367174289 2838128530620899525380717)
                  ·
                    refine ⟨1064298198982837322017769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2838128530620899525380717 1064298198982837322017769)
                    ·
                      rfl

theorem cell22_3109070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_3109070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109070 prefixEnd_3109070 := by exact prefixLift 3109070
  have htrace : WordTrace (prefixWord ++ tailWord_3109070) baseStart_3109070 baseEnd_3109070 := by
    simpa [prefixWord, tailWord_3109070, baseEnd_3109070] using wordTrace_append hprefix tailTrace_3109070
  have hstable : (prefixWord ++ tailWord_3109070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109070).length < 2 ^ (prefixWord ++ tailWord_3109070).sum := by decide
  have hdescent : baseEnd_3109070 < baseStart_3109070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109085 : List Nat := [1, 4, 3, 2, 1, 2, 2, 1, 2, 4]
def baseStart_3109085 : Nat := 118140960795 + 3109085 * 2 ^ 59
def prefixEnd_3109085 : Nat := 4983230072969 + 3 ^ 40 * 3109085 * 2
def baseEnd_3109085 : Nat := 1064303333789382282892723

theorem tailTrace_3109085 : CollatzResearch.WordTrace tailWord_3109085 prefixEnd_3109085 1064303333789382282892723 := by
  unfold tailWord_3109085
  simp only [CollatzResearch.WordTrace]
  refine ⟨113397645941323509288880709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75598430627549006192587139 113397645941323509288880709)
  ·
    refine ⟨21262058613998157991665133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113397645941323509288880709 21262058613998157991665133)
    ·
      refine ⟨7973271980249309246874425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21262058613998157991665133 7973271980249309246874425)
      ·
        refine ⟨5979953985186981935155819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7973271980249309246874425 5979953985186981935155819)
        ·
          refine ⟨8969930977780472902733729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5979953985186981935155819 8969930977780472902733729)
          ·
            refine ⟨6727448233335354677050297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8969930977780472902733729 6727448233335354677050297)
            ·
              refine ⟨5045586175001516007787723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6727448233335354677050297 5045586175001516007787723)
              ·
                refine ⟨7568379262502274011681585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5045586175001516007787723 7568379262502274011681585)
                ·
                  refine ⟨5676284446876705508761189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7568379262502274011681585 5676284446876705508761189)
                  ·
                    refine ⟨1064303333789382282892723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5676284446876705508761189 1064303333789382282892723)
                    ·
                      rfl

theorem cell22_3109085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_3109085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109085 prefixEnd_3109085 := by exact prefixLift 3109085
  have htrace : WordTrace (prefixWord ++ tailWord_3109085) baseStart_3109085 baseEnd_3109085 := by
    simpa [prefixWord, tailWord_3109085, baseEnd_3109085] using wordTrace_append hprefix tailTrace_3109085
  have hstable : (prefixWord ++ tailWord_3109085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109085).length < 2 ^ (prefixWord ++ tailWord_3109085).sum := by decide
  have hdescent : baseEnd_3109085 < baseStart_3109085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109128 : List Nat := [2, 1, 3, 2, 3, 1, 2, 3, 5]
def baseStart_3109128 : Nat := 118140960795 + 3109128 * 2 ^ 59
def prefixEnd_3109128 : Nat := 4983230072969 + 3 ^ 40 * 3109128 * 2
def baseEnd_3109128 : Nat := 354772684522714834689197

theorem tailTrace_3109128 : CollatzResearch.WordTrace tailWord_3109128 prefixEnd_3109128 354772684522714834689197 := by
  unfold tailWord_3109128
  simp only [CollatzResearch.WordTrace]
  refine ⟨56699607140083863816348019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75599476186778485088464025 56699607140083863816348019)
  ·
    refine ⟨85049410710125795724522029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56699607140083863816348019 85049410710125795724522029)
    ·
      refine ⟨31893529016297173396695761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85049410710125795724522029 31893529016297173396695761)
      ·
        refine ⟨23920146762222880047521821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31893529016297173396695761 23920146762222880047521821)
        ·
          refine ⟨8970055035833580017820683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23920146762222880047521821 8970055035833580017820683)
          ·
            refine ⟨13455082553750370026731025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8970055035833580017820683 13455082553750370026731025)
            ·
              refine ⟨10091311915312777520048269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13455082553750370026731025 10091311915312777520048269)
              ·
                refine ⟨3784241968242291570018101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10091311915312777520048269 3784241968242291570018101)
                ·
                  refine ⟨354772684522714834689197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3784241968242291570018101 354772684522714834689197)
                  ·
                    rfl

theorem cell22_3109128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 5].length) (baseStart_3109128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109128 prefixEnd_3109128 := by exact prefixLift 3109128
  have htrace : WordTrace (prefixWord ++ tailWord_3109128) baseStart_3109128 baseEnd_3109128 := by
    simpa [prefixWord, tailWord_3109128, baseEnd_3109128] using wordTrace_append hprefix tailTrace_3109128
  have hstable : (prefixWord ++ tailWord_3109128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109128).length < 2 ^ (prefixWord ++ tailWord_3109128).sum := by decide
  have hdescent : baseEnd_3109128 < baseStart_3109128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109149 : List Nat := [1, 4, 2, 3, 2, 1, 2, 3, 1, 3]
def baseStart_3109149 : Nat := 118140960795 + 3109149 * 2 ^ 59
def prefixEnd_3109149 : Nat := 4983230072969 + 3 ^ 40 * 3109149 * 2
def baseEnd_3109149 : Nat := 1064325242297307449292527

theorem tailTrace_3109149 : CollatzResearch.WordTrace tailWord_3109149 prefixEnd_3109149 1064325242297307449292527 := by
  unfold tailWord_3109149
  simp only [CollatzResearch.WordTrace]
  refine ⟨113399980213091648219210501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75599986808727765479473667 113399980213091648219210501)
  ·
    refine ⟨21262496289954684041101969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113399980213091648219210501 21262496289954684041101969)
    ·
      refine ⟨15946872217466013030826477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21262496289954684041101969 15946872217466013030826477)
      ·
        refine ⟨5980077081549754886559929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15946872217466013030826477 5980077081549754886559929)
        ·
          refine ⟨4485057811162316164919947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5980077081549754886559929 4485057811162316164919947)
          ·
            refine ⟨6727586716743474247379921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4485057811162316164919947 6727586716743474247379921)
            ·
              refine ⟨5045690037557605685534941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6727586716743474247379921 5045690037557605685534941)
              ·
                refine ⟨1892133764084102132075603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5045690037557605685534941 1892133764084102132075603)
                ·
                  refine ⟨2838200646126153198113405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1892133764084102132075603 2838200646126153198113405)
                  ·
                    refine ⟨1064325242297307449292527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2838200646126153198113405 1064325242297307449292527)
                    ·
                      rfl

theorem cell22_3109149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_3109149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109149 prefixEnd_3109149 := by exact prefixLift 3109149
  have htrace : WordTrace (prefixWord ++ tailWord_3109149) baseStart_3109149 baseEnd_3109149 := by
    simpa [prefixWord, tailWord_3109149, baseEnd_3109149] using wordTrace_append hprefix tailTrace_3109149
  have hstable : (prefixWord ++ tailWord_3109149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109149).length < 2 ^ (prefixWord ++ tailWord_3109149).sum := by decide
  have hdescent : baseEnd_3109149 < baseStart_3109149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109162 : List Nat := [3, 1, 4, 2, 2, 2, 1, 2, 5]
def baseStart_3109162 : Nat := 118140960795 + 3109162 * 2 ^ 59
def prefixEnd_3109162 : Nat := 4983230072969 + 3 ^ 40 * 3109162 * 2
def baseEnd_3109162 : Nat := 354776564154326582905829

theorem tailTrace_3109162 : CollatzResearch.WordTrace tailWord_3109162 prefixEnd_3109162 354776564154326582905829 := by
  unfold tailWord_3109162
  simp only [CollatzResearch.WordTrace]
  refine ⟨28350113590511137859858435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75600302908029700959622493 28350113590511137859858435)
  ·
    refine ⟨42525170385766706789787653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28350113590511137859858435 42525170385766706789787653)
    ·
      refine ⟨7973469447331257523085185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42525170385766706789787653 7973469447331257523085185)
      ·
        refine ⟨5980102085498443142313889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7973469447331257523085185 5980102085498443142313889)
        ·
          refine ⟨4485076564123832356735417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5980102085498443142313889 4485076564123832356735417)
          ·
            refine ⟨3363807423092874267551563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4485076564123832356735417 3363807423092874267551563)
            ·
              refine ⟨5045711134639311401327345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3363807423092874267551563 5045711134639311401327345)
              ·
                refine ⟨3784283350979483550995509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5045711134639311401327345 3784283350979483550995509)
                ·
                  refine ⟨354776564154326582905829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3784283350979483550995509 354776564154326582905829)
                  ·
                    rfl

theorem cell22_3109162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 5].length) (baseStart_3109162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109162 prefixEnd_3109162 := by exact prefixLift 3109162
  have htrace : WordTrace (prefixWord ++ tailWord_3109162) baseStart_3109162 baseEnd_3109162 := by
    simpa [prefixWord, tailWord_3109162, baseEnd_3109162] using wordTrace_append hprefix tailTrace_3109162
  have hstable : (prefixWord ++ tailWord_3109162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109162).length < 2 ^ (prefixWord ++ tailWord_3109162).sum := by decide
  have hdescent : baseEnd_3109162 < baseStart_3109162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109173 : List Nat := [1, 3, 3, 1, 2, 1, 4, 1, 6]
def baseStart_3109173 : Nat := 118140960795 + 3109173 * 2 ^ 59
def prefixEnd_3109173 : Nat := 4983230072969 + 3 ^ 40 * 3109173 * 2
def baseEnd_3109173 : Nat := 354777819329259795564151

theorem tailTrace_3109173 : CollatzResearch.WordTrace tailWord_3109173 prefixEnd_3109173 354777819329259795564151 := by
  unfold tailWord_3109173
  simp only [CollatzResearch.WordTrace]
  refine ⟨113400855565004700318084173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75600570376669800212056115 113400855565004700318084173)
  ·
    refine ⟨42525320836876762619281565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113400855565004700318084173 42525320836876762619281565)
    ·
      refine ⟨15946995313828785982230587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42525320836876762619281565 15946995313828785982230587)
      ·
        refine ⟨23920492970743178973345881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15946995313828785982230587 23920492970743178973345881)
        ·
          refine ⟨17940369728057384230009411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23920492970743178973345881 17940369728057384230009411)
          ·
            refine ⟨26910554592086076345014117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17940369728057384230009411 26910554592086076345014117)
            ·
              refine ⟨5045728986016139314690147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26910554592086076345014117 5045728986016139314690147)
              ·
                refine ⟨7568593479024208972035221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5045728986016139314690147 7568593479024208972035221)
                ·
                  refine ⟨354777819329259795564151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7568593479024208972035221 354777819329259795564151)
                  ·
                    rfl

theorem cell22_3109173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 6].length) (baseStart_3109173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109173 prefixEnd_3109173 := by exact prefixLift 3109173
  have htrace : WordTrace (prefixWord ++ tailWord_3109173) baseStart_3109173 baseEnd_3109173 := by
    simpa [prefixWord, tailWord_3109173, baseEnd_3109173] using wordTrace_append hprefix tailTrace_3109173
  have hstable : (prefixWord ++ tailWord_3109173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109173).length < 2 ^ (prefixWord ++ tailWord_3109173).sum := by decide
  have hdescent : baseEnd_3109173 < baseStart_3109173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109218 : List Nat := [3, 3, 2, 1, 1, 2, 10]
def baseStart_3109218 : Nat := 118140960795 + 3109218 * 2 ^ 59
def prefixEnd_3109218 : Nat := 4983230072969 + 3 ^ 40 * 3109218 * 2
def baseEnd_3109218 : Nat := 39420328237311639604345

theorem tailTrace_3109218 : CollatzResearch.WordTrace tailWord_3109218 prefixEnd_3109218 39420328237311639604345 := by
  unfold tailWord_3109218
  simp only [CollatzResearch.WordTrace]
  refine ⟨28350624212460418250868077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75601664566561115335648205 28350624212460418250868077)
  ·
    refine ⟨10631484079672656844075529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28350624212460418250868077 10631484079672656844075529)
    ·
      refine ⟨7973613059754492633056647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10631484079672656844075529 7973613059754492633056647)
      ·
        refine ⟨11960419589631738949584971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7973613059754492633056647 11960419589631738949584971)
        ·
          refine ⟨17940629384447608424377457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11960419589631738949584971 17940629384447608424377457)
          ·
            refine ⟨13455472038335706318283093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17940629384447608424377457 13455472038335706318283093)
            ·
              refine ⟨39420328237311639604345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13455472038335706318283093 39420328237311639604345)
              ·
                rfl

theorem cell22_3109218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 10].length) (baseStart_3109218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109218 prefixEnd_3109218 := by exact prefixLift 3109218
  have htrace : WordTrace (prefixWord ++ tailWord_3109218) baseStart_3109218 baseEnd_3109218 := by
    simpa [prefixWord, tailWord_3109218, baseEnd_3109218] using wordTrace_append hprefix tailTrace_3109218
  have hstable : (prefixWord ++ tailWord_3109218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109218).length < 2 ^ (prefixWord ++ tailWord_3109218).sum := by decide
  have hdescent : baseEnd_3109218 < baseStart_3109218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109280 : List Nat := [2, 1, 1, 4, 1, 4, 2, 2, 5]
def baseStart_3109280 : Nat := 118140960795 + 3109280 * 2 ^ 59
def prefixEnd_3109280 : Nat := 4983230072969 + 3 ^ 40 * 3109280 * 2
def baseEnd_3109280 : Nat := 354790028758155591422375

theorem tailTrace_3109280 : CollatzResearch.WordTrace tailWord_3109280 prefixEnd_3109280 354790028758155591422375 := by
  unfold tailWord_3109280
  simp only [CollatzResearch.WordTrace]
  refine ⟨56702379087808528796114647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75603172117078038394819529 56702379087808528796114647)
  ·
    refine ⟨85053568631712793194171971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56702379087808528796114647 85053568631712793194171971)
    ·
      refine ⟨127580352947569189791257957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85053568631712793194171971 127580352947569189791257957)
      ·
        refine ⟨23921316177669223085860867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127580352947569189791257957 23921316177669223085860867)
        ·
          refine ⟨35881974266503834628791301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23921316177669223085860867 35881974266503834628791301)
          ·
            refine ⟨6727870174969468992898369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35881974266503834628791301 6727870174969468992898369)
            ·
              refine ⟨5045902631227101744673777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6727870174969468992898369 5045902631227101744673777)
              ·
                refine ⟨3784426973420326308505333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5045902631227101744673777 3784426973420326308505333)
                ·
                  refine ⟨354790028758155591422375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3784426973420326308505333 354790028758155591422375)
                  ·
                    rfl

theorem cell22_3109280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 5].length) (baseStart_3109280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109280 prefixEnd_3109280 := by exact prefixLift 3109280
  have htrace : WordTrace (prefixWord ++ tailWord_3109280) baseStart_3109280 baseEnd_3109280 := by
    simpa [prefixWord, tailWord_3109280, baseEnd_3109280] using wordTrace_append hprefix tailTrace_3109280
  have hstable : (prefixWord ++ tailWord_3109280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109280).length < 2 ^ (prefixWord ++ tailWord_3109280).sum := by decide
  have hdescent : baseEnd_3109280 < baseStart_3109280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109284 : List Nat := [2, 3, 1, 2, 1, 1, 6, 2, 1, 3]
def baseStart_3109284 : Nat := 118140960795 + 3109284 * 2 ^ 59
def prefixEnd_3109284 : Nat := 4983230072969 + 3 ^ 40 * 3109284 * 2
def baseEnd_3109284 : Nat := 1064371455556212097167113

theorem tailTrace_3109284 : CollatzResearch.WordTrace tailWord_3109284 prefixEnd_3109284 1064371455556212097167113 := by
  unfold tailWord_3109284
  simp only [CollatzResearch.WordTrace]
  refine ⟨56702452033801283137687453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75603269378401710850249937 56702452033801283137687453)
  ·
    refine ⟨21263419512675481176632795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56702452033801283137687453 21263419512675481176632795)
    ·
      refine ⟨31895129269013221764949193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21263419512675481176632795 31895129269013221764949193)
      ·
        refine ⟨23921346951759916323711895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31895129269013221764949193 23921346951759916323711895)
        ·
          refine ⟨35882020427639874485567843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23921346951759916323711895 35882020427639874485567843)
          ·
            refine ⟨53823030641459811728351765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35882020427639874485567843 53823030641459811728351765)
            ·
              refine ⟨2522954561318428674766489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53823030641459811728351765 2522954561318428674766489)
              ·
                refine ⟨1892215920988821506074867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2522954561318428674766489 1892215920988821506074867)
                ·
                  refine ⟨2838323881483232259112301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1892215920988821506074867 2838323881483232259112301)
                  ·
                    refine ⟨1064371455556212097167113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2838323881483232259112301 1064371455556212097167113)
                    ·
                      rfl

theorem cell22_3109284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_3109284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109284 prefixEnd_3109284 := by exact prefixLift 3109284
  have htrace : WordTrace (prefixWord ++ tailWord_3109284) baseStart_3109284 baseEnd_3109284 := by
    simpa [prefixWord, tailWord_3109284, baseEnd_3109284] using wordTrace_append hprefix tailTrace_3109284
  have hstable : (prefixWord ++ tailWord_3109284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109284).length < 2 ^ (prefixWord ++ tailWord_3109284).sum := by decide
  have hdescent : baseEnd_3109284 < baseStart_3109284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109310 : List Nat := [4, 2, 1, 1, 1, 1, 4, 1, 3, 4]
def baseStart_3109310 : Nat := 118140960795 + 3109310 * 2 ^ 59
def prefixEnd_3109310 : Nat := 4983230072969 + 3 ^ 40 * 3109310 * 2
def baseEnd_3109310 : Nat := 1064380355887556696017033

theorem tailTrace_3109310 : CollatzResearch.WordTrace tailWord_3109310 prefixEnd_3109310 1064380355887556696017033 := by
  unfold tailWord_3109310
  simp only [CollatzResearch.WordTrace]
  refine ⟨14175731545688546589477673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75603901577005581810547589 14175731545688546589477673)
  ·
    refine ⟨10631798659266409942108255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14175731545688546589477673 10631798659266409942108255)
    ·
      refine ⟨15947697988899614913162383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10631798659266409942108255 15947697988899614913162383)
      ·
        refine ⟨23921546983349422369743575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15947697988899614913162383 23921546983349422369743575)
        ·
          refine ⟨35882320475024133554615363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23921546983349422369743575 35882320475024133554615363)
          ·
            refine ⟨53823480712536200331923045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35882320475024133554615363 53823480712536200331923045)
            ·
              refine ⟨10091902633600537562235571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53823480712536200331923045 10091902633600537562235571)
              ·
                refine ⟨15137853950400806343353357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10091902633600537562235571 15137853950400806343353357)
                ·
                  refine ⟨5676695231400302378757509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15137853950400806343353357 5676695231400302378757509)
                  ·
                    refine ⟨1064380355887556696017033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5676695231400302378757509 1064380355887556696017033)
                    ·
                      rfl

theorem cell22_3109310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_3109310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109310 prefixEnd_3109310 := by exact prefixLift 3109310
  have htrace : WordTrace (prefixWord ++ tailWord_3109310) baseStart_3109310 baseEnd_3109310 := by
    simpa [prefixWord, tailWord_3109310, baseEnd_3109310] using wordTrace_append hprefix tailTrace_3109310
  have hstable : (prefixWord ++ tailWord_3109310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109310).length < 2 ^ (prefixWord ++ tailWord_3109310).sum := by decide
  have hdescent : baseEnd_3109310 < baseStart_3109310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109357 : List Nat := [1, 5, 1, 3, 1, 1, 3, 1, 1, 5]
def baseStart_3109357 : Nat := 118140960795 + 3109357 * 2 ^ 59
def prefixEnd_3109357 : Nat := 4983230072969 + 3 ^ 40 * 3109357 * 2
def baseEnd_3109357 : Nat := 1064396444948064240091889

theorem tailTrace_3109357 : CollatzResearch.WordTrace tailWord_3109357 prefixEnd_3109357 1064396444948064240091889 := by
  unfold tailWord_3109357
  simp only [CollatzResearch.WordTrace]
  refine ⟨113407566596338099742782325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75605044397558733161854883 113407566596338099742782325)
  ·
    refine ⟨10631959368406696850885843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113407566596338099742782325 10631959368406696850885843)
    ·
      refine ⟨15947939052610045276328765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10631959368406696850885843 15947939052610045276328765)
      ·
        refine ⟨5980477144728766978623287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15947939052610045276328765 5980477144728766978623287)
        ·
          refine ⟨8970715717093150467934931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5980477144728766978623287 8970715717093150467934931)
          ·
            refine ⟨13456073575639725701902397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8970715717093150467934931 13456073575639725701902397)
            ·
              refine ⟨5046027590864897138213399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13456073575639725701902397 5046027590864897138213399)
              ·
                refine ⟨7569041386297345707320099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5046027590864897138213399 7569041386297345707320099)
                ·
                  refine ⟨11353562079446018560980149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7569041386297345707320099 11353562079446018560980149)
                  ·
                    refine ⟨1064396444948064240091889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11353562079446018560980149 1064396444948064240091889)
                    ·
                      rfl

theorem cell22_3109357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_3109357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109357 prefixEnd_3109357 := by exact prefixLift 3109357
  have htrace : WordTrace (prefixWord ++ tailWord_3109357) baseStart_3109357 baseEnd_3109357 := by
    simpa [prefixWord, tailWord_3109357, baseEnd_3109357] using wordTrace_append hprefix tailTrace_3109357
  have hstable : (prefixWord ++ tailWord_3109357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109357).length < 2 ^ (prefixWord ++ tailWord_3109357).sum := by decide
  have hdescent : baseEnd_3109357 < baseStart_3109357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109368 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 2, 7]
def baseStart_3109368 : Nat := 118140960795 + 3109368 * 2 ^ 59
def prefixEnd_3109368 : Nat := 4983230072969 + 3 ^ 40 * 3109368 * 2
def baseEnd_3109368 : Nat := 1064400210472863878066855

theorem tailTrace_3109368 : CollatzResearch.WordTrace tailWord_3109368 prefixEnd_3109368 1064400210472863878066855 := by
  unfold tailWord_3109368
  simp only [CollatzResearch.WordTrace]
  refine ⟨56703983899649124310716379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75605311866198832414288505 56703983899649124310716379)
  ·
    refine ⟨85055975849473686466074569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56703983899649124310716379 85055975849473686466074569)
    ·
      refine ⟨63791981887105264849555927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85055975849473686466074569 63791981887105264849555927)
      ·
        refine ⟨95687972830657897274333891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63791981887105264849555927 95687972830657897274333891)
        ·
          refine ⟨143531959245986845911500837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95687972830657897274333891 143531959245986845911500837)
          ·
            refine ⟨26912242358622533608406407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143531959245986845911500837 26912242358622533608406407)
            ·
              refine ⟨40368363537933800412609611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26912242358622533608406407 40368363537933800412609611)
              ·
                refine ⟨60552545306900700618914417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40368363537933800412609611 60552545306900700618914417)
                ·
                  refine ⟨45414408980175525464185813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60552545306900700618914417 45414408980175525464185813)
                  ·
                    refine ⟨1064400210472863878066855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45414408980175525464185813 1064400210472863878066855)
                    ·
                      rfl

theorem cell22_3109368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_3109368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109368 prefixEnd_3109368 := by exact prefixLift 3109368
  have htrace : WordTrace (prefixWord ++ tailWord_3109368) baseStart_3109368 baseEnd_3109368 := by
    simpa [prefixWord, tailWord_3109368, baseEnd_3109368] using wordTrace_append hprefix tailTrace_3109368
  have hstable : (prefixWord ++ tailWord_3109368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109368).length < 2 ^ (prefixWord ++ tailWord_3109368).sum := by decide
  have hdescent : baseEnd_3109368 < baseStart_3109368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109389 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_3109389 : Nat := 118140960795 + 3109389 * 2 ^ 59
def prefixEnd_3109389 : Nat := 4983230072969 + 3 ^ 40 * 3109389 * 2
def baseEnd_3109389 : Nat := 1064407399202026823291791

theorem tailTrace_3109389 : CollatzResearch.WordTrace tailWord_3109389 prefixEnd_3109389 1064407399202026823291791 := by
  unfold tailWord_3109389
  simp only [CollatzResearch.WordTrace]
  refine ⟨113408733732222169207947221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75605822488148112805298147 113408733732222169207947221)
  ·
    refine ⟨2658017196848957090811263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 113408733732222169207947221 2658017196848957090811263)
    ·
      refine ⟨3987025795273435636216895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2658017196848957090811263 3987025795273435636216895)
      ·
        refine ⟨5980538692910153454325343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3987025795273435636216895 5980538692910153454325343)
        ·
          refine ⟨8970808039365230181488015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5980538692910153454325343 8970808039365230181488015)
          ·
            refine ⟨13456212059047845272232023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8970808039365230181488015 13456212059047845272232023)
            ·
              refine ⟨20184318088571767908348035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13456212059047845272232023 20184318088571767908348035)
              ·
                refine ⟨30276477132857651862522053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20184318088571767908348035 30276477132857651862522053)
                ·
                  refine ⟨5676839462410809724222885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30276477132857651862522053 5676839462410809724222885)
                  ·
                    refine ⟨1064407399202026823291791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5676839462410809724222885 1064407399202026823291791)
                    ·
                      rfl

theorem cell22_3109389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_3109389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109389 prefixEnd_3109389 := by exact prefixLift 3109389
  have htrace : WordTrace (prefixWord ++ tailWord_3109389) baseStart_3109389 baseEnd_3109389 := by
    simpa [prefixWord, tailWord_3109389, baseEnd_3109389] using wordTrace_append hprefix tailTrace_3109389
  have hstable : (prefixWord ++ tailWord_3109389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109389).length < 2 ^ (prefixWord ++ tailWord_3109389).sum := by decide
  have hdescent : baseEnd_3109389 < baseStart_3109389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109402 : List Nat := [3, 1, 1, 3, 1, 1, 5, 1, 3, 3]
def baseStart_3109402 : Nat := 118140960795 + 3109402 * 2 ^ 59
def prefixEnd_3109402 : Nat := 4983230072969 + 3 ^ 40 * 3109402 * 2
def baseEnd_3109402 : Nat := 1064411849367699122716751

theorem tailTrace_3109402 : CollatzResearch.WordTrace tailWord_3109402 prefixEnd_3109402 1064411849367699122716751 := by
  unfold tailWord_3109402
  simp only [CollatzResearch.WordTrace]
  refine ⟨28352301970293768107042615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75606138587450048285446973 28352301970293768107042615)
  ·
    refine ⟨42528452955440652160563923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28352301970293768107042615 42528452955440652160563923)
    ·
      refine ⟨63792679433160978240845885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42528452955440652160563923 63792679433160978240845885)
      ·
        refine ⟨23922254787435366840317207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63792679433160978240845885 23922254787435366840317207)
        ·
          refine ⟨35883382181153050260475811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23922254787435366840317207 35883382181153050260475811)
          ·
            refine ⟨53825073271729575390713717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35883382181153050260475811 53825073271729575390713717)
            ·
              refine ⟨5046100619224647692879411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53825073271729575390713717 5046100619224647692879411)
              ·
                refine ⟨7569150928836971539319117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5046100619224647692879411 7569150928836971539319117)
                ·
                  refine ⟨2838431598313864327244669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7569150928836971539319117 2838431598313864327244669)
                  ·
                    refine ⟨1064411849367699122716751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2838431598313864327244669 1064411849367699122716751)
                    ·
                      rfl

theorem cell22_3109402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 3, 3].length) (baseStart_3109402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109402 prefixEnd_3109402 := by exact prefixLift 3109402
  have htrace : WordTrace (prefixWord ++ tailWord_3109402) baseStart_3109402 baseEnd_3109402 := by
    simpa [prefixWord, tailWord_3109402, baseEnd_3109402] using wordTrace_append hprefix tailTrace_3109402
  have hstable : (prefixWord ++ tailWord_3109402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109402).length < 2 ^ (prefixWord ++ tailWord_3109402).sum := by decide
  have hdescent : baseEnd_3109402 < baseStart_3109402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109408 : List Nat := [2, 1, 1, 6, 3, 1, 2, 1, 2, 3]
def baseStart_3109408 : Nat := 118140960795 + 3109408 * 2 ^ 59
def prefixEnd_3109408 : Nat := 4983230072969 + 3 ^ 40 * 3109408 * 2
def baseEnd_3109408 : Nat := 1064413903290317107066733

theorem tailTrace_3109408 : CollatzResearch.WordTrace tailWord_3109408 prefixEnd_3109408 1064413903290317107066733 := by
  unfold tailWord_3109408
  simp only [CollatzResearch.WordTrace]
  refine ⟨56704713359576667726444439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75606284479435556968592585 56704713359576667726444439)
  ·
    refine ⟨85057070039365001589666659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56704713359576667726444439 85057070039365001589666659)
    ·
      refine ⟨127585605059047502384499989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85057070039365001589666659 127585605059047502384499989)
      ·
        refine ⟨5980575237142851674273437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 127585605059047502384499989 5980575237142851674273437)
        ·
          refine ⟨2242715713928569377852539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5980575237142851674273437 2242715713928569377852539)
          ·
            refine ⟨3364073570892854066778809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2242715713928569377852539 3364073570892854066778809)
            ·
              refine ⟨2523055178169640550084107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3364073570892854066778809 2523055178169640550084107)
              ·
                refine ⟨3784582767254460825126161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2523055178169640550084107 3784582767254460825126161)
                ·
                  refine ⟨2838437075440845618844621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3784582767254460825126161 2838437075440845618844621)
                  ·
                    refine ⟨1064413903290317107066733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2838437075440845618844621 1064413903290317107066733)
                    ·
                      rfl

theorem cell22_3109408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 2, 3].length) (baseStart_3109408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109408 prefixEnd_3109408 := by exact prefixLift 3109408
  have htrace : WordTrace (prefixWord ++ tailWord_3109408) baseStart_3109408 baseEnd_3109408 := by
    simpa [prefixWord, tailWord_3109408, baseEnd_3109408] using wordTrace_append hprefix tailTrace_3109408
  have hstable : (prefixWord ++ tailWord_3109408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109408).length < 2 ^ (prefixWord ++ tailWord_3109408).sum := by decide
  have hdescent : baseEnd_3109408 < baseStart_3109408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109453 : List Nat := [1, 6, 1, 1, 2, 1, 4, 2, 1, 3]
def baseStart_3109453 : Nat := 118140960795 + 3109453 * 2 ^ 59
def prefixEnd_3109453 : Nat := 4983230072969 + 3 ^ 40 * 3109453 * 2
def baseEnd_3109453 : Nat := 1064429307709951989691595

theorem tailTrace_3109453 : CollatzResearch.WordTrace tailWord_3109453 prefixEnd_3109453 1064429307709951989691595 := by
  unfold tailWord_3109453
  simp only [CollatzResearch.WordTrace]
  refine ⟨113411068003990308138277013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75607378669326872092184675 113411068003990308138277013)
  ·
    refine ⟨5316143812687045693981735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 113411068003990308138277013 5316143812687045693981735)
    ·
      refine ⟨7974215719030568540972603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5316143812687045693981735 7974215719030568540972603)
      ·
        refine ⟨11961323578545852811458905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7974215719030568540972603 11961323578545852811458905)
        ·
          refine ⟨8970992683909389608594179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11961323578545852811458905 8970992683909389608594179)
          ·
            refine ⟨13456489025864084412891269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8970992683909389608594179 13456489025864084412891269)
            ·
              refine ⟨2523091692349515827417113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13456489025864084412891269 2523091692349515827417113)
              ·
                refine ⟨1892318769262136870562835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2523091692349515827417113 1892318769262136870562835)
                ·
                  refine ⟨2838478153893205305844253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1892318769262136870562835 2838478153893205305844253)
                  ·
                    refine ⟨1064429307709951989691595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2838478153893205305844253 1064429307709951989691595)
                    ·
                      rfl

theorem cell22_3109453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_3109453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109453 prefixEnd_3109453 := by exact prefixLift 3109453
  have htrace : WordTrace (prefixWord ++ tailWord_3109453) baseStart_3109453 baseEnd_3109453 := by
    simpa [prefixWord, tailWord_3109453, baseEnd_3109453] using wordTrace_append hprefix tailTrace_3109453
  have hstable : (prefixWord ++ tailWord_3109453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109453).length < 2 ^ (prefixWord ++ tailWord_3109453).sum := by decide
  have hdescent : baseEnd_3109453 < baseStart_3109453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109477 : List Nat := [1, 3, 1, 3, 4, 1, 1, 2, 6]
def baseStart_3109477 : Nat := 118140960795 + 3109477 * 2 ^ 59
def prefixEnd_3109477 : Nat := 4983230072969 + 3 ^ 40 * 3109477 * 2
def baseEnd_3109477 : Nat := 354812507800141309030507

theorem tailTrace_3109477 : CollatzResearch.WordTrace tailWord_3109477 prefixEnd_3109477 354812507800141309030507 := by
  unfold tailWord_3109477
  simp only [CollatzResearch.WordTrace]
  refine ⟨113411943355903360237150685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75607962237268906824767123 113411943355903360237150685)
  ·
    refine ⟨42529478758463760088931507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113411943355903360237150685 42529478758463760088931507)
    ·
      refine ⟨63794218137695640133397261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42529478758463760088931507 63794218137695640133397261)
      ·
        refine ⟨23922831801635865050023973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63794218137695640133397261 23922831801635865050023973)
        ·
          refine ⟨4485530962806724696879495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23922831801635865050023973 4485530962806724696879495)
          ·
            refine ⟨6728296444210087045319243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4485530962806724696879495 6728296444210087045319243)
            ·
              refine ⟨10092444666315130567978865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6728296444210087045319243 10092444666315130567978865)
              ·
                refine ⟨7569333499736347925984149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10092444666315130567978865 7569333499736347925984149)
                ·
                  refine ⟨354812507800141309030507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7569333499736347925984149 354812507800141309030507)
                  ·
                    rfl

theorem cell22_3109477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 6].length) (baseStart_3109477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109477 prefixEnd_3109477 := by exact prefixLift 3109477
  have htrace : WordTrace (prefixWord ++ tailWord_3109477) baseStart_3109477 baseEnd_3109477 := by
    simpa [prefixWord, tailWord_3109477, baseEnd_3109477] using wordTrace_append hprefix tailTrace_3109477
  have hstable : (prefixWord ++ tailWord_3109477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109477).length < 2 ^ (prefixWord ++ tailWord_3109477).sum := by decide
  have hdescent : baseEnd_3109477 < baseStart_3109477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109505 : List Nat := [1, 2, 4, 2, 1, 1, 11]
def baseStart_3109505 : Nat := 118140960795 + 3109505 * 2 ^ 59
def prefixEnd_3109505 : Nat := 4983230072969 + 3 ^ 40 * 3109505 * 2
def baseEnd_3109505 : Nat := 39423966976764488421905

theorem tailTrace_3109505 : CollatzResearch.WordTrace tailWord_3109505 prefixEnd_3109505 39423966976764488421905 := by
  unfold tailWord_3109505
  simp only [CollatzResearch.WordTrace]
  refine ⟨113412964599801921019169969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75608643066534614012779979 113412964599801921019169969)
  ·
    refine ⟨85059723449851440764377477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113412964599801921019169969 85059723449851440764377477)
    ·
      refine ⟨15948698146847145143320777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85059723449851440764377477 15948698146847145143320777)
      ·
        refine ⟨11961523610135358857490583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15948698146847145143320777 11961523610135358857490583)
        ·
          refine ⟨17942285415203038286235875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11961523610135358857490583 17942285415203038286235875)
          ·
            refine ⟨26913428122804557429353813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17942285415203038286235875 26913428122804557429353813)
            ·
              refine ⟨39423966976764488421905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 26913428122804557429353813 39423966976764488421905)
              ·
                rfl

theorem cell22_3109505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 11].length) (baseStart_3109505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109505 prefixEnd_3109505 := by exact prefixLift 3109505
  have htrace : WordTrace (prefixWord ++ tailWord_3109505) baseStart_3109505 baseEnd_3109505 := by
    simpa [prefixWord, tailWord_3109505, baseEnd_3109505] using wordTrace_append hprefix tailTrace_3109505
  have hstable : (prefixWord ++ tailWord_3109505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109505).length < 2 ^ (prefixWord ++ tailWord_3109505).sum := by decide
  have hdescent : baseEnd_3109505 < baseStart_3109505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109509 : List Nat := [1, 3, 1, 1, 4, 2, 3, 2, 2, 3]
def baseStart_3109509 : Nat := 118140960795 + 3109509 * 2 ^ 59
def prefixEnd_3109509 : Nat := 4983230072969 + 3 ^ 40 * 3109509 * 2
def baseEnd_3109509 : Nat := 1064448477654386510291423

theorem tailTrace_3109509 : CollatzResearch.WordTrace tailWord_3109509 prefixEnd_3109509 1064448477654386510291423 := by
  unfold tailWord_3109509
  simp only [CollatzResearch.WordTrace]
  refine ⟨113413110491787429702315581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75608740327858286468210387 113413110491787429702315581)
  ·
    refine ⟨42529916434420286138368343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113413110491787429702315581 42529916434420286138368343)
    ·
      refine ⟨63794874651630429207552515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42529916434420286138368343 63794874651630429207552515)
      ·
        refine ⟨95692311977445643811328773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63794874651630429207552515 95692311977445643811328773)
        ·
          refine ⟨17942308495771058214624145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95692311977445643811328773 17942308495771058214624145)
          ·
            refine ⟨13456731371828293660968109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17942308495771058214624145 13456731371828293660968109)
            ·
              refine ⟨5046274264435610122863041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13456731371828293660968109 5046274264435610122863041)
              ·
                refine ⟨3784705698326707592147281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5046274264435610122863041 3784705698326707592147281)
                ·
                  refine ⟨2838529273745030694110461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3784705698326707592147281 2838529273745030694110461)
                  ·
                    refine ⟨1064448477654386510291423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2838529273745030694110461 1064448477654386510291423)
                    ·
                      rfl

theorem cell22_3109509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 2, 3].length) (baseStart_3109509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109509 prefixEnd_3109509 := by exact prefixLift 3109509
  have htrace : WordTrace (prefixWord ++ tailWord_3109509) baseStart_3109509 baseEnd_3109509 := by
    simpa [prefixWord, tailWord_3109509, baseEnd_3109509] using wordTrace_append hprefix tailTrace_3109509
  have hstable : (prefixWord ++ tailWord_3109509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109509).length < 2 ^ (prefixWord ++ tailWord_3109509).sum := by decide
  have hdescent : baseEnd_3109509 < baseStart_3109509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109627 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 8, 3]
def baseStart_3109627 : Nat := 118140960795 + 3109627 * 2 ^ 59
def prefixEnd_3109627 : Nat := 4983230072969 + 3 ^ 40 * 3109627 * 2
def baseEnd_3109627 : Nat := 1064488871465873535841061

theorem tailTrace_3109627 : CollatzResearch.WordTrace tailWord_3109627 prefixEnd_3109627 1064488871465873535841061 := by
  unfold tailWord_3109627
  simp only [CollatzResearch.WordTrace]
  refine ⟨113417414305359935855111135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75611609536906623903407423 113417414305359935855111135)
  ·
    refine ⟨170126121458039903782666703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113417414305359935855111135 170126121458039903782666703)
    ·
      refine ⟨255189182187059855674000055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170126121458039903782666703 255189182187059855674000055)
      ·
        refine ⟨382783773280589783511000083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255189182187059855674000055 382783773280589783511000083)
        ·
          refine ⟨574175659920884675266500125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382783773280589783511000083 574175659920884675266500125)
          ·
            refine ⟨215315872470331753224937547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 574175659920884675266500125 215315872470331753224937547)
            ·
              refine ⟨322973808705497629837406321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215315872470331753224937547 322973808705497629837406321)
              ·
                refine ⟨242230356529123222378054741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 322973808705497629837406321 242230356529123222378054741)
                ·
                  refine ⟨2838636990575662762242829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 242230356529123222378054741 2838636990575662762242829)
                  ·
                    refine ⟨1064488871465873535841061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2838636990575662762242829 1064488871465873535841061)
                    ·
                      rfl

theorem cell22_3109627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 8, 3].length) (baseStart_3109627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109627 prefixEnd_3109627 := by exact prefixLift 3109627
  have htrace : WordTrace (prefixWord ++ tailWord_3109627) baseStart_3109627 baseEnd_3109627 := by
    simpa [prefixWord, tailWord_3109627, baseEnd_3109627] using wordTrace_append hprefix tailTrace_3109627
  have hstable : (prefixWord ++ tailWord_3109627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109627).length < 2 ^ (prefixWord ++ tailWord_3109627).sum := by decide
  have hdescent : baseEnd_3109627 < baseStart_3109627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109629 : List Nat := [1, 4, 1, 1, 1, 1, 5, 4, 4]
def baseStart_3109629 : Nat := 118140960795 + 3109629 * 2 ^ 59
def prefixEnd_3109629 : Nat := 4983230072969 + 3 ^ 40 * 3109629 * 2
def baseEnd_3109629 : Nat := 354829852035582065763685

theorem tailTrace_3109629 : CollatzResearch.WordTrace tailWord_3109629 prefixEnd_3109629 354829852035582065763685 := by
  unfold tailWord_3109629
  simp only [CollatzResearch.WordTrace]
  refine ⟨113417487251352690196683941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75611658167568460131122627 113417487251352690196683941)
  ·
    refine ⟨21265778859628629411878239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113417487251352690196683941 21265778859628629411878239)
    ·
      refine ⟨31898668289442944117817359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21265778859628629411878239 31898668289442944117817359)
      ·
        refine ⟨47848002434164416176726039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31898668289442944117817359 47848002434164416176726039)
        ·
          refine ⟨71772003651246624265089059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47848002434164416176726039 71772003651246624265089059)
          ·
            refine ⟨107658005476869936397633589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71772003651246624265089059 107658005476869936397633589)
            ·
              refine ⟨10092938013456556537278149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107658005476869936397633589 10092938013456556537278149)
              ·
                refine ⟨1892425877523104350739653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10092938013456556537278149 1892425877523104350739653)
                ·
                  refine ⟨354829852035582065763685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1892425877523104350739653 354829852035582065763685)
                  ·
                    rfl

theorem cell22_3109629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_3109629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109629 prefixEnd_3109629 := by exact prefixLift 3109629
  have htrace : WordTrace (prefixWord ++ tailWord_3109629) baseStart_3109629 baseEnd_3109629 := by
    simpa [prefixWord, tailWord_3109629, baseEnd_3109629] using wordTrace_append hprefix tailTrace_3109629
  have hstable : (prefixWord ++ tailWord_3109629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109629).length < 2 ^ (prefixWord ++ tailWord_3109629).sum := by decide
  have hdescent : baseEnd_3109629 < baseStart_3109629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109642 : List Nat := [3, 1, 2, 2, 1, 2, 2, 2, 1, 6]
def baseStart_3109642 : Nat := 118140960795 + 3109642 * 2 ^ 59
def prefixEnd_3109642 : Nat := 4983230072969 + 3 ^ 40 * 3109642 * 2
def baseEnd_3109642 : Nat := 1064494006272418496716015

theorem tailTrace_3109642 : CollatzResearch.WordTrace tailWord_3109642 prefixEnd_3109642 1064494006272418496716015 := by
  unfold tailWord_3109642
  simp only [CollatzResearch.WordTrace]
  refine ⟨28354490350076398354226795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75611974266870395611271453 28354490350076398354226795)
  ·
    refine ⟨42531735525114597531340193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28354490350076398354226795 42531735525114597531340193)
    ·
      refine ⟨31898801643835948148505145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42531735525114597531340193 31898801643835948148505145)
      ·
        refine ⟨23924101232876961111378859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31898801643835948148505145 23924101232876961111378859)
        ·
          refine ⟨35886151849315441667068289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23924101232876961111378859 35886151849315441667068289)
          ·
            refine ⟨26914613886986581250301217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35886151849315441667068289 26914613886986581250301217)
            ·
              refine ⟨20185960415239935937725913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26914613886986581250301217 20185960415239935937725913)
              ·
                refine ⟨15139470311429951953294435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20185960415239935937725913 15139470311429951953294435)
                ·
                  refine ⟨22709205467144927929941653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15139470311429951953294435 22709205467144927929941653)
                  ·
                    refine ⟨1064494006272418496716015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22709205467144927929941653 1064494006272418496716015)
                    ·
                      rfl

theorem cell22_3109642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_3109642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109642 prefixEnd_3109642 := by exact prefixLift 3109642
  have htrace : WordTrace (prefixWord ++ tailWord_3109642) baseStart_3109642 baseEnd_3109642 := by
    simpa [prefixWord, tailWord_3109642, baseEnd_3109642] using wordTrace_append hprefix tailTrace_3109642
  have hstable : (prefixWord ++ tailWord_3109642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109642).length < 2 ^ (prefixWord ++ tailWord_3109642).sum := by decide
  have hdescent : baseEnd_3109642 < baseStart_3109642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109678 : List Nat := [4, 1, 3, 2, 1, 1, 3, 2, 2, 3]
def baseStart_3109678 : Nat := 118140960795 + 3109678 * 2 ^ 59
def prefixEnd_3109678 : Nat := 4983230072969 + 3 ^ 40 * 3109678 * 2
def baseEnd_3109678 : Nat := 1064506329808126402815905

theorem tailTrace_3109678 : CollatzResearch.WordTrace tailWord_3109678 prefixEnd_3109678 1064506329808126402815905 := by
  unfold tailWord_3109678
  simp only [CollatzResearch.WordTrace]
  refine ⟨14177409303521896445652211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75612849618783447710145125 14177409303521896445652211)
  ·
    refine ⟨21266113955282844668478317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14177409303521896445652211 21266113955282844668478317)
    ·
      refine ⟨7974792733231066750679369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21266113955282844668478317 7974792733231066750679369)
      ·
        refine ⟨5981094549923300063009527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7974792733231066750679369 5981094549923300063009527)
        ·
          refine ⟨8971641824884950094514291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5981094549923300063009527 8971641824884950094514291)
          ·
            refine ⟨13457462737327425141771437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8971641824884950094514291 13457462737327425141771437)
            ·
              refine ⟨5046548526497784428164289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13457462737327425141771437 5046548526497784428164289)
              ·
                refine ⟨3784911394873338321123217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5046548526497784428164289 3784911394873338321123217)
                ·
                  refine ⟨2838683546155003740842413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3784911394873338321123217 2838683546155003740842413)
                  ·
                    refine ⟨1064506329808126402815905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2838683546155003740842413 1064506329808126402815905)
                    ·
                      rfl

theorem cell22_3109678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_3109678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109678 prefixEnd_3109678 := by exact prefixLift 3109678
  have htrace : WordTrace (prefixWord ++ tailWord_3109678) baseStart_3109678 baseEnd_3109678 := by
    simpa [prefixWord, tailWord_3109678, baseEnd_3109678] using wordTrace_append hprefix tailTrace_3109678
  have hstable : (prefixWord ++ tailWord_3109678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109678).length < 2 ^ (prefixWord ++ tailWord_3109678).sum := by decide
  have hdescent : baseEnd_3109678 < baseStart_3109678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109779 : List Nat := [1, 1, 1, 2, 1, 2, 1, 6, 4, 3]
def baseStart_3109779 : Nat := 118140960795 + 3109779 * 2 ^ 59
def prefixEnd_3109779 : Nat := 4983230072969 + 3 ^ 40 * 3109779 * 2
def baseEnd_3109779 : Nat := 1064540904172195806040595

theorem tailTrace_3109779 : CollatzResearch.WordTrace tailWord_3109779 prefixEnd_3109779 1064540904172195806040595 := by
  unfold tailWord_3109779
  simp only [CollatzResearch.WordTrace]
  refine ⟨113422958200809265814644391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75615305467206177209762927 113422958200809265814644391)
  ·
    refine ⟨170134437301213898721966587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113422958200809265814644391 170134437301213898721966587)
    ·
      refine ⟨255201655951820848082949881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170134437301213898721966587 255201655951820848082949881)
      ·
        refine ⟨191401241963865636062212411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255201655951820848082949881 191401241963865636062212411)
        ·
          refine ⟨287101862945798454093318617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191401241963865636062212411 287101862945798454093318617)
          ·
            refine ⟨215326397209348840569988963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287101862945798454093318617 215326397209348840569988963)
            ·
              refine ⟨322989595814023260854983445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215326397209348840569988963 322989595814023260854983445)
              ·
                refine ⟨15140137303782340352577349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 322989595814023260854983445 15140137303782340352577349)
                ·
                  refine ⟨2838775744459188816108253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15140137303782340352577349 2838775744459188816108253)
                  ·
                    refine ⟨1064540904172195806040595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2838775744459188816108253 1064540904172195806040595)
                    ·
                      rfl

theorem cell22_3109779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 4, 3].length) (baseStart_3109779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109779 prefixEnd_3109779 := by exact prefixLift 3109779
  have htrace : WordTrace (prefixWord ++ tailWord_3109779) baseStart_3109779 baseEnd_3109779 := by
    simpa [prefixWord, tailWord_3109779, baseEnd_3109779] using wordTrace_append hprefix tailTrace_3109779
  have hstable : (prefixWord ++ tailWord_3109779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109779).length < 2 ^ (prefixWord ++ tailWord_3109779).sum := by decide
  have hdescent : baseEnd_3109779 < baseStart_3109779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109828 : List Nat := [2, 3, 3, 3, 1, 1, 1, 1, 1, 6]
def baseStart_3109828 : Nat := 118140960795 + 3109828 * 2 ^ 59
def prefixEnd_3109828 : Nat := 4983230072969 + 3 ^ 40 * 3109828 * 2
def baseEnd_3109828 : Nat := 1064557677873576011565445

theorem tailTrace_3109828 : CollatzResearch.WordTrace tailWord_3109828 prefixEnd_3109828 1064557677873576011565445 := by
  unfold tailWord_3109828
  simp only [CollatzResearch.WordTrace]
  refine ⟨56712372688815873591589069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75616496918421164788785425 56712372688815873591589069)
  ·
    refine ⟨21267139758305952596845901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56712372688815873591589069 21267139758305952596845901)
    ·
      refine ⟨7975177409364732223817213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21267139758305952596845901 7975177409364732223817213)
      ·
        refine ⟨2990691528511774583931455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7975177409364732223817213 2990691528511774583931455)
        ·
          refine ⟨4486037292767661875897183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2990691528511774583931455 4486037292767661875897183)
          ·
            refine ⟨6729055939151492813845775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4486037292767661875897183 6729055939151492813845775)
            ·
              refine ⟨10093583908727239220768663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6729055939151492813845775 10093583908727239220768663)
              ·
                refine ⟨15140375863090858831152995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10093583908727239220768663 15140375863090858831152995)
                ·
                  refine ⟨22710563794636288246729493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15140375863090858831152995 22710563794636288246729493)
                  ·
                    refine ⟨1064557677873576011565445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22710563794636288246729493 1064557677873576011565445)
                    ·
                      rfl

theorem cell22_3109828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_3109828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109828 prefixEnd_3109828 := by exact prefixLift 3109828
  have htrace : WordTrace (prefixWord ++ tailWord_3109828) baseStart_3109828 baseEnd_3109828 := by
    simpa [prefixWord, tailWord_3109828, baseEnd_3109828] using wordTrace_append hprefix tailTrace_3109828
  have hstable : (prefixWord ++ tailWord_3109828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109828).length < 2 ^ (prefixWord ++ tailWord_3109828).sum := by decide
  have hdescent : baseEnd_3109828 < baseStart_3109828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109877 : List Nat := [1, 3, 5, 2, 2, 1, 2, 6]
def baseStart_3109877 : Nat := 118140960795 + 3109877 * 2 ^ 59
def prefixEnd_3109877 : Nat := 4983230072969 + 3 ^ 40 * 3109877 * 2
def baseEnd_3109877 : Nat := 118286050174995135232255

theorem tailTrace_3109877 : CollatzResearch.WordTrace tailWord_3109877 prefixEnd_3109877 118286050174995135232255 := by
  unfold tailWord_3109877
  simp only [CollatzResearch.WordTrace]
  refine ⟨113426532554454228551711885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75617688369636152367807923 113426532554454228551711885)
  ·
    refine ⟨42534949707920335706891957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113426532554454228551711885 42534949707920335706891957)
    ·
      refine ⟨3987651535117531472521121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42534949707920335706891957 3987651535117531472521121)
      ·
        refine ⟨2990738651338148604390841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3987651535117531472521121 2990738651338148604390841)
        ·
          refine ⟨2243053988503611453293131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2990738651338148604390841 2243053988503611453293131)
          ·
            refine ⟨3364580982755417179939697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2243053988503611453293131 3364580982755417179939697)
            ·
              refine ⟨2523435737066562884954773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3364580982755417179939697 2523435737066562884954773)
              ·
                refine ⟨118286050174995135232255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2523435737066562884954773 118286050174995135232255)
                ·
                  rfl

theorem cell22_3109877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 6].length) (baseStart_3109877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109877 prefixEnd_3109877 := by exact prefixLift 3109877
  have htrace : WordTrace (prefixWord ++ tailWord_3109877) baseStart_3109877 baseEnd_3109877 := by
    simpa [prefixWord, tailWord_3109877, baseEnd_3109877] using wordTrace_append hprefix tailTrace_3109877
  have hstable : (prefixWord ++ tailWord_3109877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109877).length < 2 ^ (prefixWord ++ tailWord_3109877).sum := by decide
  have hdescent : baseEnd_3109877 < baseStart_3109877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109946 : List Nat := [3, 1, 1, 1, 3, 1, 3, 3, 2, 4]
def baseStart_3109946 : Nat := 118140960795 + 3109946 * 2 ^ 59
def prefixEnd_3109946 : Nat := 4983230072969 + 3 ^ 40 * 3109946 * 2
def baseEnd_3109946 : Nat := 1064598071685063037115083

theorem tailTrace_3109946 : CollatzResearch.WordTrace tailWord_3109946 prefixEnd_3109946 1064598071685063037115083 := by
  unfold tailWord_3109946
  simp only [CollatzResearch.WordTrace]
  refine ⟨28357262297801063333993423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75619366127469502223982461 28357262297801063333993423)
  ·
    refine ⟨42535893446701595000990135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28357262297801063333993423 42535893446701595000990135)
    ·
      refine ⟨63803840170052392501485203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42535893446701595000990135 63803840170052392501485203)
      ·
        refine ⟨95705760255078588752227805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63803840170052392501485203 95705760255078588752227805)
        ·
          refine ⟨35889660095654470782085427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95705760255078588752227805 35889660095654470782085427)
          ·
            refine ⟨53834490143481706173128141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35889660095654470782085427 53834490143481706173128141)
            ·
              refine ⟨20187933803805639814923053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53834490143481706173128141 20187933803805639814923053)
              ·
                refine ⟨7570475176427114930596145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20187933803805639814923053 7570475176427114930596145)
                ·
                  refine ⟨5677856382320336197947109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7570475176427114930596145 5677856382320336197947109)
                  ·
                    refine ⟨1064598071685063037115083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5677856382320336197947109 1064598071685063037115083)
                    ·
                      rfl

theorem cell22_3109946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_3109946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109946 prefixEnd_3109946 := by exact prefixLift 3109946
  have htrace : WordTrace (prefixWord ++ tailWord_3109946) baseStart_3109946 baseEnd_3109946 := by
    simpa [prefixWord, tailWord_3109946, baseEnd_3109946] using wordTrace_append hprefix tailTrace_3109946
  have hstable : (prefixWord ++ tailWord_3109946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109946).length < 2 ^ (prefixWord ++ tailWord_3109946).sum := by decide
  have hdescent : baseEnd_3109946 < baseStart_3109946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109965 : List Nat := [1, 6, 1, 1, 1, 2, 1, 4, 2, 3]
def baseStart_3109965 : Nat := 118140960795 + 3109965 * 2 ^ 59
def prefixEnd_3109965 : Nat := 4983230072969 + 3 ^ 40 * 3109965 * 2
def baseEnd_3109965 : Nat := 1064604575773353320890025

theorem tailTrace_3109965 : CollatzResearch.WordTrace tailWord_3109965 prefixEnd_3109965 1064604575773353320890025 := by
  unfold tailWord_3109965
  simp only [CollatzResearch.WordTrace]
  refine ⟨113429742178135419580915349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75619828118756946387276899 113429742178135419580915349)
  ·
    refine ⟨5317019164600097792855407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 113429742178135419580915349 5317019164600097792855407)
    ·
      refine ⟨7975528746900146689283111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5317019164600097792855407 7975528746900146689283111)
      ·
        refine ⟨11963293120350220033924667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7975528746900146689283111 11963293120350220033924667)
        ·
          refine ⟨17944939680525330050887001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11963293120350220033924667 17944939680525330050887001)
          ·
            refine ⟨13458704760393997538165251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17944939680525330050887001 13458704760393997538165251)
            ·
              refine ⟨20188057140590996307247877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13458704760393997538165251 20188057140590996307247877)
              ·
                refine ⟨3785260713860811807608977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20188057140590996307247877 3785260713860811807608977)
                ·
                  refine ⟨2838945535395608855706733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3785260713860811807608977 2838945535395608855706733)
                  ·
                    refine ⟨1064604575773353320890025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2838945535395608855706733 1064604575773353320890025)
                    ·
                      rfl

theorem cell22_3109965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_3109965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109965 prefixEnd_3109965 := by exact prefixLift 3109965
  have htrace : WordTrace (prefixWord ++ tailWord_3109965) baseStart_3109965 baseEnd_3109965 := by
    simpa [prefixWord, tailWord_3109965, baseEnd_3109965] using wordTrace_append hprefix tailTrace_3109965
  have hstable : (prefixWord ++ tailWord_3109965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109965).length < 2 ^ (prefixWord ++ tailWord_3109965).sum := by decide
  have hdescent : baseEnd_3109965 < baseStart_3109965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109982 : List Nat := [4, 4, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_3109982 : Nat := 118140960795 + 3109982 * 2 ^ 59
def prefixEnd_3109982 : Nat := 4983230072969 + 3 ^ 40 * 3109982 * 2
def baseEnd_3109982 : Nat := 1064610395220770943214973

theorem tailTrace_3109982 : CollatzResearch.WordTrace tailWord_3109982 prefixEnd_3109982 1064610395220770943214973 := by
  unfold tailWord_3109982
  simp only [CollatzResearch.WordTrace]
  refine ⟨14178795277384228935535525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75620241479382554322856133 14178795277384228935535525)
  ·
    refine ⟨2658524114509542925412911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14178795277384228935535525 2658524114509542925412911)
    ·
      refine ⟨3987786171764314388119367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2658524114509542925412911 3987786171764314388119367)
      ·
        refine ⟨5981679257646471582179051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3987786171764314388119367 5981679257646471582179051)
        ·
          refine ⟨8972518886469707373268577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5981679257646471582179051 8972518886469707373268577)
          ·
            refine ⟨6729389164852280529951433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8972518886469707373268577 6729389164852280529951433)
            ·
              refine ⟨5047041873639210397463575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6729389164852280529951433 5047041873639210397463575)
              ·
                refine ⟨7570562810458815596195363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5047041873639210397463575 7570562810458815596195363)
                ·
                  refine ⟨11355844215688223394293045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7570562810458815596195363 11355844215688223394293045)
                  ·
                    refine ⟨1064610395220770943214973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11355844215688223394293045 1064610395220770943214973)
                    ·
                      rfl

theorem cell22_3109982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_3109982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109982 prefixEnd_3109982 := by exact prefixLift 3109982
  have htrace : WordTrace (prefixWord ++ tailWord_3109982) baseStart_3109982 baseEnd_3109982 := by
    simpa [prefixWord, tailWord_3109982, baseEnd_3109982] using wordTrace_append hprefix tailTrace_3109982
  have hstable : (prefixWord ++ tailWord_3109982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109982).length < 2 ^ (prefixWord ++ tailWord_3109982).sum := by decide
  have hdescent : baseEnd_3109982 < baseStart_3109982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3109993 : List Nat := [1, 2, 1, 1, 1, 7, 1, 2, 3, 3]
def baseStart_3109993 : Nat := 118140960795 + 3109993 * 2 ^ 59
def prefixEnd_3109993 : Nat := 4983230072969 + 3 ^ 40 * 3109993 * 2
def baseEnd_3109993 : Nat := 1064614160745570581189939

theorem tailTrace_3109993 : CollatzResearch.WordTrace tailWord_3109993 prefixEnd_3109993 1064614160745570581189939 := by
  unfold tailWord_3109993
  simp only [CollatzResearch.WordTrace]
  refine ⟨113430763422033980362934633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75620508948022653575289755 113430763422033980362934633)
  ·
    refine ⟨85073072566525485272200975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113430763422033980362934633 85073072566525485272200975)
    ·
      refine ⟨127609608849788227908301463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85073072566525485272200975 127609608849788227908301463)
      ·
        refine ⟨191414413274682341862452195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127609608849788227908301463 191414413274682341862452195)
        ·
          refine ⟨287121619912023512793678293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191414413274682341862452195 287121619912023512793678293)
          ·
            refine ⟨6729412966688051081101835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 287121619912023512793678293 6729412966688051081101835)
            ·
              refine ⟨10094119450032076621652753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6729412966688051081101835 10094119450032076621652753)
              ·
                refine ⟨7570589587524057466239565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10094119450032076621652753 7570589587524057466239565)
                ·
                  refine ⟨2838971095321521549839837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7570589587524057466239565 2838971095321521549839837)
                  ·
                    refine ⟨1064614160745570581189939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2838971095321521549839837 1064614160745570581189939)
                    ·
                      rfl

theorem cell22_3109993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 3, 3].length) (baseStart_3109993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3109993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3109993 prefixEnd_3109993 := by exact prefixLift 3109993
  have htrace : WordTrace (prefixWord ++ tailWord_3109993) baseStart_3109993 baseEnd_3109993 := by
    simpa [prefixWord, tailWord_3109993, baseEnd_3109993] using wordTrace_append hprefix tailTrace_3109993
  have hstable : (prefixWord ++ tailWord_3109993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3109993).length < 2 ^ (prefixWord ++ tailWord_3109993).sum := by decide
  have hdescent : baseEnd_3109993 < baseStart_3109993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3109993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110040 : List Nat := [2, 1, 2, 4, 2, 2, 3, 1, 5]
def baseStart_3110040 : Nat := 118140960795 + 3110040 * 2 ^ 59
def prefixEnd_3110040 : Nat := 4983230072969 + 3 ^ 40 * 3110040 * 2
def baseEnd_3110040 : Nat := 354876749935359375088265

theorem tailTrace_3110040 : CollatzResearch.WordTrace tailWord_3110040 prefixEnd_3110040 354876749935359375088265 := by
  unfold tailWord_3110040
  simp only [CollatzResearch.WordTrace]
  refine ⟨56716238826431853694947787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75621651768575804926597049 56716238826431853694947787)
  ·
    refine ⟨85074358239647780542421681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56716238826431853694947787 85074358239647780542421681)
    ·
      refine ⟨63805768679735835406816261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85074358239647780542421681 63805768679735835406816261)
      ·
        refine ⟨11963581627450469138778049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63805768679735835406816261 11963581627450469138778049)
        ·
          refine ⟨8972686220587851854083537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11963581627450469138778049 8972686220587851854083537)
          ·
            refine ⟨6729514665440888890562653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8972686220587851854083537 6729514665440888890562653)
            ·
              refine ⟨2523567999540333333960995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6729514665440888890562653 2523567999540333333960995)
              ·
                refine ⟨3785351999310500000941493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2523567999540333333960995 3785351999310500000941493)
                ·
                  refine ⟨354876749935359375088265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3785351999310500000941493 354876749935359375088265)
                  ·
                    rfl

theorem cell22_3110040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 5].length) (baseStart_3110040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3110040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3110040 prefixEnd_3110040 := by exact prefixLift 3110040
  have htrace : WordTrace (prefixWord ++ tailWord_3110040) baseStart_3110040 baseEnd_3110040 := by
    simpa [prefixWord, tailWord_3110040, baseEnd_3110040] using wordTrace_append hprefix tailTrace_3110040
  have hstable : (prefixWord ++ tailWord_3110040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110040).length < 2 ^ (prefixWord ++ tailWord_3110040).sum := by decide
  have hdescent : baseEnd_3110040 < baseStart_3110040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110053 : List Nat := [1, 3, 1, 2, 1, 4, 1, 4, 1, 4]
def baseStart_3110053 : Nat := 118140960795 + 3110053 * 2 ^ 59
def prefixEnd_3110053 : Nat := 4983230072969 + 3 ^ 40 * 3110053 * 2
def baseEnd_3110053 : Nat := 1064634699971750424689755

theorem tailTrace_3110053 : CollatzResearch.WordTrace tailWord_3110053 prefixEnd_3110053 1064634699971750424689755 := by
  unfold tailWord_3110053
  simp only [CollatzResearch.WordTrace]
  refine ⟨113432951801816610610118813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75621967867877740406745875 113432951801816610610118813)
  ·
    refine ⟨42537356925681228978794555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113432951801816610610118813 42537356925681228978794555)
    ·
      refine ⟨63806035388521843468191833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42537356925681228978794555 63806035388521843468191833)
      ·
        refine ⟨47854526541391382601143875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63806035388521843468191833 47854526541391382601143875)
        ·
          refine ⟨71781789812087073901715813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47854526541391382601143875 71781789812087073901715813)
          ·
            refine ⟨13459085589766326356571715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71781789812087073901715813 13459085589766326356571715)
            ·
              refine ⟨20188628384649489534857573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13459085589766326356571715 20188628384649489534857573)
              ·
                refine ⟨3785367822121779287785795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20188628384649489534857573 3785367822121779287785795)
                ·
                  refine ⟨5678051733182668931678693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3785367822121779287785795 5678051733182668931678693)
                  ·
                    refine ⟨1064634699971750424689755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5678051733182668931678693 1064634699971750424689755)
                    ·
                      rfl

theorem cell22_3110053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_3110053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3110053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3110053 prefixEnd_3110053 := by exact prefixLift 3110053
  have htrace : WordTrace (prefixWord ++ tailWord_3110053) baseStart_3110053 baseEnd_3110053 := by
    simpa [prefixWord, tailWord_3110053, baseEnd_3110053] using wordTrace_append hprefix tailTrace_3110053
  have hstable : (prefixWord ++ tailWord_3110053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110053).length < 2 ^ (prefixWord ++ tailWord_3110053).sum := by decide
  have hdescent : baseEnd_3110053 < baseStart_3110053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110061 : List Nat := [1, 5, 2, 1, 4, 1, 1, 3, 1, 3]
def baseStart_3110061 : Nat := 118140960795 + 3110061 * 2 ^ 59
def prefixEnd_3110061 : Nat := 4983230072969 + 3 ^ 40 * 3110061 * 2
def baseEnd_3110061 : Nat := 1064637438535241070489731

theorem tailTrace_3110061 : CollatzResearch.WordTrace tailWord_3110061 prefixEnd_3110061 1064637438535241070489731 := by
  unfold tailWord_3110061
  simp only [CollatzResearch.WordTrace]
  refine ⟨113433243585787627976410037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75622162390525085317606691 113433243585787627976410037)
  ·
    refine ⟨10634366586167590122788441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113433243585787627976410037 10634366586167590122788441)
    ·
      refine ⟨7975774939625692592091331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10634366586167590122788441 7975774939625692592091331)
      ·
        refine ⟨11963662409438538888136997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7975774939625692592091331 11963662409438538888136997)
        ·
          refine ⟨2243186701769726041525687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11963662409438538888136997 2243186701769726041525687)
          ·
            refine ⟨3364780052654589062288531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2243186701769726041525687 3364780052654589062288531)
            ·
              refine ⟨5047170078981883593432797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3364780052654589062288531 5047170078981883593432797)
              ·
                refine ⟨1892688779618206347537299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5047170078981883593432797 1892688779618206347537299)
                ·
                  refine ⟨2839033169427309521305949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1892688779618206347537299 2839033169427309521305949)
                  ·
                    refine ⟨1064637438535241070489731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2839033169427309521305949 1064637438535241070489731)
                    ·
                      rfl

theorem cell22_3110061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_3110061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3110061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3110061 prefixEnd_3110061 := by exact prefixLift 3110061
  have htrace : WordTrace (prefixWord ++ tailWord_3110061) baseStart_3110061 baseEnd_3110061 := by
    simpa [prefixWord, tailWord_3110061, baseEnd_3110061] using wordTrace_append hprefix tailTrace_3110061
  have hstable : (prefixWord ++ tailWord_3110061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110061).length < 2 ^ (prefixWord ++ tailWord_3110061).sum := by decide
  have hdescent : baseEnd_3110061 < baseStart_3110061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110098 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 4, 4]
def baseStart_3110098 : Nat := 118140960795 + 3110098 * 2 ^ 59
def prefixEnd_3110098 : Nat := 4983230072969 + 3 ^ 40 * 3110098 * 2
def baseEnd_3110098 : Nat := 1064650104391385307314617

theorem tailTrace_3110098 : CollatzResearch.WordTrace tailWord_3110098 prefixEnd_3110098 1064650104391385307314617 := by
  unfold tailWord_3110098
  simp only [CollatzResearch.WordTrace]
  refine ⟨28358648271663395823876737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75623062057769055530337965 28358648271663395823876737)
  ·
    refine ⟨21268986203747546867907553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28358648271663395823876737 21268986203747546867907553)
    ·
      refine ⟨15951739652810660150930665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21268986203747546867907553 15951739652810660150930665)
      ·
        refine ⟨11963804739607995113197999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15951739652810660150930665 11963804739607995113197999)
        ·
          refine ⟨17945707109411992669796999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11963804739607995113197999 17945707109411992669796999)
          ·
            refine ⟨26918560664117989004695499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17945707109411992669796999 26918560664117989004695499)
            ·
              refine ⟨40377840996176983507043249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26918560664117989004695499 40377840996176983507043249)
              ·
                refine ⟨30283380747132737630282437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40377840996176983507043249 30283380747132737630282437)
                ·
                  refine ⟨5678133890087388305677957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30283380747132737630282437 5678133890087388305677957)
                  ·
                    refine ⟨1064650104391385307314617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5678133890087388305677957 1064650104391385307314617)
                    ·
                      rfl

theorem cell22_3110098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_3110098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3110098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3110098 prefixEnd_3110098 := by exact prefixLift 3110098
  have htrace : WordTrace (prefixWord ++ tailWord_3110098) baseStart_3110098 baseEnd_3110098 := by
    simpa [prefixWord, tailWord_3110098, baseEnd_3110098] using wordTrace_append hprefix tailTrace_3110098
  have hstable : (prefixWord ++ tailWord_3110098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110098).length < 2 ^ (prefixWord ++ tailWord_3110098).sum := by decide
  have hdescent : baseEnd_3110098 < baseStart_3110098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110111 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 2, 7]
def baseStart_3110111 : Nat := 118140960795 + 3110111 * 2 ^ 59
def prefixEnd_3110111 : Nat := 4983230072969 + 3 ^ 40 * 3110111 * 2
def baseEnd_3110111 : Nat := 1064654554557057606739577

theorem tailTrace_3110111 : CollatzResearch.WordTrace tailWord_3110111 prefixEnd_3110111 1064654554557057606739577 := by
  unfold tailWord_3110111
  simp only [CollatzResearch.WordTrace]
  refine ⟨113435067235606486515730187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75623378157070991010486791 113435067235606486515730187)
  ·
    refine ⟨170152600853409729773595281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113435067235606486515730187 170152600853409729773595281)
    ·
      refine ⟨127614450640057297330196461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170152600853409729773595281 127614450640057297330196461)
      ·
        refine ⟨47855418990021486498823673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127614450640057297330196461 47855418990021486498823673)
        ·
          refine ⟨35891564242516114874117755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47855418990021486498823673 35891564242516114874117755)
          ·
            refine ⟨53837346363774172311176633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35891564242516114874117755 53837346363774172311176633)
            ·
              refine ⟨40378009772830629233382475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53837346363774172311176633 40378009772830629233382475)
              ·
                refine ⟨60567014659245943850073713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40378009772830629233382475 60567014659245943850073713)
                ·
                  refine ⟨45425260994434457887555285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60567014659245943850073713 45425260994434457887555285)
                  ·
                    refine ⟨1064654554557057606739577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45425260994434457887555285 1064654554557057606739577)
                    ·
                      rfl

theorem cell22_3110111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 7].length) (baseStart_3110111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3110111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3110111 prefixEnd_3110111 := by exact prefixLift 3110111
  have htrace : WordTrace (prefixWord ++ tailWord_3110111) baseStart_3110111 baseEnd_3110111 := by
    simpa [prefixWord, tailWord_3110111, baseEnd_3110111] using wordTrace_append hprefix tailTrace_3110111
  have hstable : (prefixWord ++ tailWord_3110111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110111).length < 2 ^ (prefixWord ++ tailWord_3110111).sum := by decide
  have hdescent : baseEnd_3110111 < baseStart_3110111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110233 : List Nat := [1, 2, 1, 2, 2, 2, 4, 1, 1, 6]
def baseStart_3110233 : Nat := 118140960795 + 3110233 * 2 ^ 59
def prefixEnd_3110233 : Nat := 4983230072969 + 3 ^ 40 * 3110233 * 2
def baseEnd_3110233 : Nat := 1064696317650289955189203

theorem tailTrace_3110233 : CollatzResearch.WordTrace tailWord_3110233 prefixEnd_3110233 1064696317650289955189203 := by
  unfold tailWord_3110233
  simp only [CollatzResearch.WordTrace]
  refine ⟨113439516941164501351671353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75626344627443000901114235 113439516941164501351671353)
  ·
    refine ⟨85079637705873376013753515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113439516941164501351671353 85079637705873376013753515)
    ·
      refine ⟨127619456558810064020630273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85079637705873376013753515 127619456558810064020630273)
      ·
        refine ⟨95714592419107548015472705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127619456558810064020630273 95714592419107548015472705)
        ·
          refine ⟨71785944314330661011604529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95714592419107548015472705 71785944314330661011604529)
          ·
            refine ⟨53839458235747995758703397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71785944314330661011604529 53839458235747995758703397)
            ·
              refine ⟨10094898419202749204756887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53839458235747995758703397 10094898419202749204756887)
              ·
                refine ⟨15142347628804123807135331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10094898419202749204756887 15142347628804123807135331)
                ·
                  refine ⟨22713521443206185710702997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15142347628804123807135331 22713521443206185710702997)
                  ·
                    refine ⟨1064696317650289955189203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22713521443206185710702997 1064696317650289955189203)
                    ·
                      rfl

theorem cell22_3110233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 6].length) (baseStart_3110233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3110233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3110233 prefixEnd_3110233 := by exact prefixLift 3110233
  have htrace : WordTrace (prefixWord ++ tailWord_3110233) baseStart_3110233 baseEnd_3110233 := by
    simpa [prefixWord, tailWord_3110233, baseEnd_3110233] using wordTrace_append hprefix tailTrace_3110233
  have hstable : (prefixWord ++ tailWord_3110233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110233).length < 2 ^ (prefixWord ++ tailWord_3110233).sum := by decide
  have hdescent : baseEnd_3110233 < baseStart_3110233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110254 : List Nat := [4, 1, 2, 4, 1, 2, 1, 1, 6]
def baseStart_3110254 : Nat := 118140960795 + 3110254 * 2 ^ 59
def prefixEnd_3110254 : Nat := 4983230072969 + 3 ^ 40 * 3110254 * 2
def baseEnd_3110254 : Nat := 354901168793150966804713

theorem tailTrace_3110254 : CollatzResearch.WordTrace tailWord_3110254 prefixEnd_3110254 354901168793150966804713 := by
  unfold tailWord_3110254
  simp only [CollatzResearch.WordTrace]
  refine ⟨14180035359261052742273227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75626855249392281292123877 14180035359261052742273227)
  ·
    refine ⟨21270053038891579113409841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14180035359261052742273227 21270053038891579113409841)
    ·
      refine ⟨15952539779168684335057381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21270053038891579113409841 15952539779168684335057381)
      ·
        refine ⟨2991101208594128312823259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15952539779168684335057381 2991101208594128312823259)
        ·
          refine ⟨4486651812891192469234889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2991101208594128312823259 4486651812891192469234889)
          ·
            refine ⟨3364988859668394351926167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4486651812891192469234889 3364988859668394351926167)
            ·
              refine ⟨5047483289502591527889251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3364988859668394351926167 5047483289502591527889251)
              ·
                refine ⟨7571224934253887291833877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5047483289502591527889251 7571224934253887291833877)
                ·
                  refine ⟨354901168793150966804713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7571224934253887291833877 354901168793150966804713)
                  ·
                    rfl

theorem cell22_3110254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_3110254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3110254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3110254 prefixEnd_3110254 := by exact prefixLift 3110254
  have htrace : WordTrace (prefixWord ++ tailWord_3110254) baseStart_3110254 baseEnd_3110254 := by
    simpa [prefixWord, tailWord_3110254, baseEnd_3110254] using wordTrace_append hprefix tailTrace_3110254
  have hstable : (prefixWord ++ tailWord_3110254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110254).length < 2 ^ (prefixWord ++ tailWord_3110254).sum := by decide
  have hdescent : baseEnd_3110254 < baseStart_3110254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110293 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 9]
def baseStart_3110293 : Nat := 118140960795 + 3110293 * 2 ^ 59
def prefixEnd_3110293 : Nat := 4983230072969 + 3 ^ 40 * 3110293 * 2
def baseEnd_3110293 : Nat := 354905618958823266229673

theorem tailTrace_3110293 : CollatzResearch.WordTrace tailWord_3110293 prefixEnd_3110293 354905618958823266229673 := by
  unfold tailWord_3110293
  simp only [CollatzResearch.WordTrace]
  refine ⟨113441705320947131598855533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75627803547298087732570355 113441705320947131598855533)
  ·
    refine ⟨42540639495355174349570825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113441705320947131598855533 42540639495355174349570825)
    ·
      refine ⟨31905479621516380762178119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42540639495355174349570825 31905479621516380762178119)
      ·
        refine ⟨47858219432274571143267179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31905479621516380762178119 47858219432274571143267179)
        ·
          refine ⟨71787329148411856714900769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47858219432274571143267179 71787329148411856714900769)
          ·
            refine ⟨53840496861308892536175577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71787329148411856714900769 53840496861308892536175577)
            ·
              refine ⟨40380372645981669402131683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53840496861308892536175577 40380372645981669402131683)
              ·
                refine ⟨60570558968972504103197525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40380372645981669402131683 60570558968972504103197525)
                ·
                  refine ⟨354905618958823266229673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60570558968972504103197525 354905618958823266229673)
                  ·
                    rfl

theorem cell22_3110293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 9].length) (baseStart_3110293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3110293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3110293 prefixEnd_3110293 := by exact prefixLift 3110293
  have htrace : WordTrace (prefixWord ++ tailWord_3110293) baseStart_3110293 baseEnd_3110293 := by
    simpa [prefixWord, tailWord_3110293, baseEnd_3110293] using wordTrace_append hprefix tailTrace_3110293
  have hstable : (prefixWord ++ tailWord_3110293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110293).length < 2 ^ (prefixWord ++ tailWord_3110293).sum := by decide
  have hdescent : baseEnd_3110293 < baseStart_3110293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110325 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 1, 7]
def baseStart_3110325 : Nat := 118140960795 + 3110325 * 2 ^ 59
def prefixEnd_3110325 : Nat := 4983230072969 + 3 ^ 40 * 3110325 * 2
def baseEnd_3110325 : Nat := 1064727811130432381888921

theorem tailTrace_3110325 : CollatzResearch.WordTrace tailWord_3110325 prefixEnd_3110325 1064727811130432381888921 := by
  unfold tailWord_3110325
  simp only [CollatzResearch.WordTrace]
  refine ⟨113442872456831201064020429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75628581637887467376013619 113442872456831201064020429)
  ·
    refine ⟨42541077171311700399007661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113442872456831201064020429 42541077171311700399007661)
    ·
      refine ⟨15952903939241887649627873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42541077171311700399007661 15952903939241887649627873)
      ·
        refine ⟨11964677954431415737220905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15952903939241887649627873 11964677954431415737220905)
        ·
          refine ⟨8973508465823561802915679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11964677954431415737220905 8973508465823561802915679)
          ·
            refine ⟨13460262698735342704373519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8973508465823561802915679 13460262698735342704373519)
            ·
              refine ⟨20190394048103014056560279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13460262698735342704373519 20190394048103014056560279)
              ·
                refine ⟨30285591072154521084840419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20190394048103014056560279 30285591072154521084840419)
                ·
                  refine ⟨45428386608231781627260629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30285591072154521084840419 45428386608231781627260629)
                  ·
                    refine ⟨1064727811130432381888921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45428386608231781627260629 1064727811130432381888921)
                    ·
                      rfl

theorem cell22_3110325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_3110325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3110325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3110325 prefixEnd_3110325 := by exact prefixLift 3110325
  have htrace : WordTrace (prefixWord ++ tailWord_3110325) baseStart_3110325 baseEnd_3110325 := by
    simpa [prefixWord, tailWord_3110325, baseEnd_3110325] using wordTrace_append hprefix tailTrace_3110325
  have hstable : (prefixWord ++ tailWord_3110325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110325).length < 2 ^ (prefixWord ++ tailWord_3110325).sum := by decide
  have hdescent : baseEnd_3110325 < baseStart_3110325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110357 : List Nat := [1, 3, 2, 3, 1, 1, 3, 3, 1, 4]
def baseStart_3110357 : Nat := 118140960795 + 3110357 * 2 ^ 59
def prefixEnd_3110357 : Nat := 4983230072969 + 3 ^ 40 * 3110357 * 2
def baseEnd_3110357 : Nat := 1064738765384394965088823

theorem tailTrace_3110357 : CollatzResearch.WordTrace tailWord_3110357 prefixEnd_3110357 1064738765384394965088823 := by
  unfold tailWord_3110357
  simp only [CollatzResearch.WordTrace]
  refine ⟨113444039592715270529185325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75629359728476847019456883 113444039592715270529185325)
  ·
    refine ⟨42541514847268226448444497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113444039592715270529185325 42541514847268226448444497)
    ·
      refine ⟨31906136135451169836333373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42541514847268226448444497 31906136135451169836333373)
      ·
        refine ⟨11964801050794188688625015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31906136135451169836333373 11964801050794188688625015)
        ·
          refine ⟨17947201576191283032937523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11964801050794188688625015 17947201576191283032937523)
          ·
            refine ⟨26920802364286924549406285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17947201576191283032937523 26920802364286924549406285)
            ·
              refine ⟨10095300886607596706027357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26920802364286924549406285 10095300886607596706027357)
              ·
                refine ⟨3785737832477848764760259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10095300886607596706027357 3785737832477848764760259)
                ·
                  refine ⟨5678606748716773147140389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3785737832477848764760259 5678606748716773147140389)
                  ·
                    refine ⟨1064738765384394965088823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5678606748716773147140389 1064738765384394965088823)
                    ·
                      rfl

theorem cell22_3110357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_3110357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3110357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3110357 prefixEnd_3110357 := by exact prefixLift 3110357
  have htrace : WordTrace (prefixWord ++ tailWord_3110357) baseStart_3110357 baseEnd_3110357 := by
    simpa [prefixWord, tailWord_3110357, baseEnd_3110357] using wordTrace_append hprefix tailTrace_3110357
  have hstable : (prefixWord ++ tailWord_3110357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110357).length < 2 ^ (prefixWord ++ tailWord_3110357).sum := by decide
  have hdescent : baseEnd_3110357 < baseStart_3110357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110385 : List Nat := [1, 2, 2, 2, 3, 2, 1, 2, 1, 6]
def baseStart_3110385 : Nat := 118140960795 + 3110385 * 2 ^ 59
def prefixEnd_3110385 : Nat := 4983230072969 + 3 ^ 40 * 3110385 * 2
def baseEnd_3110385 : Nat := 1064748350356612225388737

theorem tailTrace_3110385 : CollatzResearch.WordTrace tailWord_3110385 prefixEnd_3110385 1064748350356612225388737 := by
  unfold tailWord_3110385
  simp only [CollatzResearch.WordTrace]
  refine ⟨113445060836613831311204609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75630040557742554207469739 113445060836613831311204609)
  ·
    refine ⟨85083795627460373483403457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113445060836613831311204609 85083795627460373483403457)
    ·
      refine ⟨63812846720595280112552593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85083795627460373483403457 63812846720595280112552593)
      ·
        refine ⟨47859635040446460084414445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63812846720595280112552593 47859635040446460084414445)
        ·
          refine ⟨17947363140167422531655417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47859635040446460084414445 17947363140167422531655417)
          ·
            refine ⟨13460522355125566898741563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17947363140167422531655417 13460522355125566898741563)
            ·
              refine ⟨20190783532688350348112345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13460522355125566898741563 20190783532688350348112345)
              ·
                refine ⟨15143087649516262761084259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20190783532688350348112345 15143087649516262761084259)
                ·
                  refine ⟨22714631474274394141626389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15143087649516262761084259 22714631474274394141626389)
                  ·
                    refine ⟨1064748350356612225388737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22714631474274394141626389 1064748350356612225388737)
                    ·
                      rfl

theorem cell22_3110385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_3110385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3110385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3110385 prefixEnd_3110385 := by exact prefixLift 3110385
  have htrace : WordTrace (prefixWord ++ tailWord_3110385) baseStart_3110385 baseEnd_3110385 := by
    simpa [prefixWord, tailWord_3110385, baseEnd_3110385] using wordTrace_append hprefix tailTrace_3110385
  have hstable : (prefixWord ++ tailWord_3110385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110385).length < 2 ^ (prefixWord ++ tailWord_3110385).sum := by decide
  have hdescent : baseEnd_3110385 < baseStart_3110385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110490 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 10]
def baseStart_3110490 : Nat := 118140960795 + 3110490 * 2 ^ 59
def prefixEnd_3110490 : Nat := 4983230072969 + 3 ^ 40 * 3110490 * 2
def baseEnd_3110490 : Nat := 354928098000808983837805

theorem tailTrace_3110490 : CollatzResearch.WordTrace tailWord_3110490 prefixEnd_3110490 354928098000808983837805 := by
  unfold tailWord_3110490
  simp only [CollatzResearch.WordTrace]
  refine ⟨28362222625308358560944231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75632593667488956162517949 28362222625308358560944231)
  ·
    refine ⟨42543333937962537841416347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28362222625308358560944231 42543333937962537841416347)
    ·
      refine ⟨63815000906943806762124521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42543333937962537841416347 63815000906943806762124521)
      ·
        refine ⟨47861250680207855071593391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63815000906943806762124521 47861250680207855071593391)
        ·
          refine ⟨71791876020311782607390087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47861250680207855071593391 71791876020311782607390087)
          ·
            refine ⟨107687814030467673911085131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71791876020311782607390087 107687814030467673911085131)
            ·
              refine ⟨161531721045701510866627697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107687814030467673911085131 161531721045701510866627697)
              ·
                refine ⟨121148790784276133149970773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161531721045701510866627697 121148790784276133149970773)
                ·
                  refine ⟨354928098000808983837805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 121148790784276133149970773 354928098000808983837805)
                  ·
                    rfl

theorem cell22_3110490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 10].length) (baseStart_3110490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3110490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3110490 prefixEnd_3110490 := by exact prefixLift 3110490
  have htrace : WordTrace (prefixWord ++ tailWord_3110490) baseStart_3110490 baseEnd_3110490 := by
    simpa [prefixWord, tailWord_3110490, baseEnd_3110490] using wordTrace_append hprefix tailTrace_3110490
  have hstable : (prefixWord ++ tailWord_3110490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110490).length < 2 ^ (prefixWord ++ tailWord_3110490).sum := by decide
  have hdescent : baseEnd_3110490 < baseStart_3110490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110537 : List Nat := [1, 2, 1, 1, 4, 1, 2, 4, 2, 4]
def baseStart_3110537 : Nat := 118140960795 + 3110537 * 2 ^ 59
def prefixEnd_3110537 : Nat := 4983230072969 + 3 ^ 40 * 3110537 * 2
def baseEnd_3110537 : Nat := 1064800383062934495588271

theorem tailTrace_3110537 : CollatzResearch.WordTrace tailWord_3110537 prefixEnd_3110537 1064800383062934495588271 := by
  unfold tailWord_3110537
  simp only [CollatzResearch.WordTrace]
  refine ⟨113450604732063161270737865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75633736488042107513825243 113450604732063161270737865)
  ·
    refine ⟨85087953549047370953053399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113450604732063161270737865 85087953549047370953053399)
    ·
      refine ⟨127631930323571056429580099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85087953549047370953053399 127631930323571056429580099)
      ·
        refine ⟨191447895485356584644370149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127631930323571056429580099 191447895485356584644370149)
        ·
          refine ⟨35896480403504359620819403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191447895485356584644370149 35896480403504359620819403)
          ·
            refine ⟨53844720605256539431229105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35896480403504359620819403 53844720605256539431229105)
            ·
              refine ⟨40383540453942404573421829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53844720605256539431229105 40383540453942404573421829)
              ·
                refine ⟨7571913835114200857516593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40383540453942404573421829 7571913835114200857516593)
                ·
                  refine ⟨5678935376335650643137445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7571913835114200857516593 5678935376335650643137445)
                  ·
                    refine ⟨1064800383062934495588271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5678935376335650643137445 1064800383062934495588271)
                    ·
                      rfl

theorem cell22_3110537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 4].length) (baseStart_3110537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3110537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3110537 prefixEnd_3110537 := by exact prefixLift 3110537
  have htrace : WordTrace (prefixWord ++ tailWord_3110537) baseStart_3110537 baseEnd_3110537 := by
    simpa [prefixWord, tailWord_3110537, baseEnd_3110537] using wordTrace_append hprefix tailTrace_3110537
  have hstable : (prefixWord ++ tailWord_3110537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110537).length < 2 ^ (prefixWord ++ tailWord_3110537).sum := by decide
  have hdescent : baseEnd_3110537 < baseStart_3110537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110556 : List Nat := [2, 2, 3, 2, 3, 2, 1, 1, 1, 5]
def baseStart_3110556 : Nat := 118140960795 + 3110556 * 2 ^ 59
def prefixEnd_3110556 : Nat := 4983230072969 + 3 ^ 40 * 3110556 * 2
def baseEnd_3110556 : Nat := 1064806887151224779363213

theorem tailTrace_3110556 : CollatzResearch.WordTrace tailWord_3110556 prefixEnd_3110556 1064806887151224779363213 := by
  unfold tailWord_3110556
  simp only [CollatzResearch.WordTrace]
  refine ⟨56725648859497163757839761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75634198479329551677119681 56725648859497163757839761)
  ·
    refine ⟨42544236644622872818379821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56725648859497163757839761 42544236644622872818379821)
    ·
      refine ⟨15954088741733577306892433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42544236644622872818379821 15954088741733577306892433)
      ·
        refine ⟨11965566556300182980169325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15954088741733577306892433 11965566556300182980169325)
        ·
          refine ⟨4487087458612568617563497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11965566556300182980169325 4487087458612568617563497)
          ·
            refine ⟨3365315593959426463172623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4487087458612568617563497 3365315593959426463172623)
            ·
              refine ⟨5047973390939139694758935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3365315593959426463172623 5047973390939139694758935)
              ·
                refine ⟨7571960086408709542138403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5047973390939139694758935 7571960086408709542138403)
                ·
                  refine ⟨11357940129613064313207605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7571960086408709542138403 11357940129613064313207605)
                  ·
                    refine ⟨1064806887151224779363213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11357940129613064313207605 1064806887151224779363213)
                    ·
                      rfl

theorem cell22_3110556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_3110556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3110556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3110556 prefixEnd_3110556 := by exact prefixLift 3110556
  have htrace : WordTrace (prefixWord ++ tailWord_3110556) baseStart_3110556 baseEnd_3110556 := by
    simpa [prefixWord, tailWord_3110556, baseEnd_3110556] using wordTrace_append hprefix tailTrace_3110556
  have hstable : (prefixWord ++ tailWord_3110556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110556).length < 2 ^ (prefixWord ++ tailWord_3110556).sum := by decide
  have hdescent : baseEnd_3110556 < baseStart_3110556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110689 : List Nat := [1, 2, 3, 2, 1, 4, 1, 1, 1, 6]
def baseStart_3110689 : Nat := 118140960795 + 3110689 * 2 ^ 59
def prefixEnd_3110689 : Nat := 4983230072969 + 3 ^ 40 * 3110689 * 2
def baseEnd_3110689 : Nat := 1064852415769256765787805

theorem tailTrace_3110689 : CollatzResearch.WordTrace tailWord_3110689 prefixEnd_3110689 1064852415769256765787805 := by
  unfold tailWord_3110689
  simp only [CollatzResearch.WordTrace]
  refine ⟨113456148627512491230271121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75637432418341660820180747 113456148627512491230271121)
  ·
    refine ⟨85092111470634368422703341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113456148627512491230271121 85092111470634368422703341)
    ·
      refine ⟨31909541801487888158513753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85092111470634368422703341 31909541801487888158513753)
      ·
        refine ⟨23932156351115916118885315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31909541801487888158513753 23932156351115916118885315)
        ·
          refine ⟨35898234526673874178327973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23932156351115916118885315 35898234526673874178327973)
          ·
            refine ⟨6730918973751351408436495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35898234526673874178327973 6730918973751351408436495)
            ·
              refine ⟨10096378460627027112654743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6730918973751351408436495 10096378460627027112654743)
              ·
                refine ⟨15144567690940540668982115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10096378460627027112654743 15144567690940540668982115)
                ·
                  refine ⟨22716851536410811003473173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15144567690940540668982115 22716851536410811003473173)
                  ·
                    refine ⟨1064852415769256765787805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22716851536410811003473173 1064852415769256765787805)
                    ·
                      rfl

theorem cell22_3110689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_3110689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3110689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3110689 prefixEnd_3110689 := by exact prefixLift 3110689
  have htrace : WordTrace (prefixWord ++ tailWord_3110689) baseStart_3110689 baseEnd_3110689 := by
    simpa [prefixWord, tailWord_3110689, baseEnd_3110689] using wordTrace_append hprefix tailTrace_3110689
  have hstable : (prefixWord ++ tailWord_3110689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110689).length < 2 ^ (prefixWord ++ tailWord_3110689).sum := by decide
  have hdescent : baseEnd_3110689 < baseStart_3110689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110708 : List Nat := [2, 5, 1, 1, 2, 2, 1, 1, 4, 3]
def baseStart_3110708 : Nat := 118140960795 + 3110708 * 2 ^ 59
def prefixEnd_3110708 : Nat := 4983230072969 + 3 ^ 40 * 3110708 * 2
def baseEnd_3110708 : Nat := 1064858919857547049562747

theorem tailTrace_3110708 : CollatzResearch.WordTrace tailWord_3110708 prefixEnd_3110708 1064858919857547049562747 := by
  unfold tailWord_3110708
  simp only [CollatzResearch.WordTrace]
  refine ⟨56728420807221828737606389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75637894409629104983475185 56728420807221828737606389)
  ·
    refine ⟨5318289450677046444150599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56728420807221828737606389 5318289450677046444150599)
    ·
      refine ⟨7977434176015569666225899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5318289450677046444150599 7977434176015569666225899)
      ·
        refine ⟨11966151264023354499338849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7977434176015569666225899 11966151264023354499338849)
        ·
          refine ⟨8974613448017515874504137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11966151264023354499338849 8974613448017515874504137)
          ·
            refine ⟨6730960086013136905878103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8974613448017515874504137 6730960086013136905878103)
            ·
              refine ⟨10096440129019705358817155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6730960086013136905878103 10096440129019705358817155)
              ·
                refine ⟨15144660193529558038225733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10096440129019705358817155 15144660193529558038225733)
                ·
                  refine ⟨2839623786286792132167325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15144660193529558038225733 2839623786286792132167325)
                  ·
                    refine ⟨1064858919857547049562747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2839623786286792132167325 1064858919857547049562747)
                    ·
                      rfl

theorem cell22_3110708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_3110708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3110708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3110708 prefixEnd_3110708 := by exact prefixLift 3110708
  have htrace : WordTrace (prefixWord ++ tailWord_3110708) baseStart_3110708 baseEnd_3110708 := by
    simpa [prefixWord, tailWord_3110708, baseEnd_3110708] using wordTrace_append hprefix tailTrace_3110708
  have hstable : (prefixWord ++ tailWord_3110708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110708).length < 2 ^ (prefixWord ++ tailWord_3110708).sum := by decide
  have hdescent : baseEnd_3110708 < baseStart_3110708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110766 : List Nat := [4, 1, 2, 3, 1, 1, 2, 1, 7]
def baseStart_3110766 : Nat := 118140960795 + 3110766 * 2 ^ 59
def prefixEnd_3110766 : Nat := 4983230072969 + 3 ^ 40 * 3110766 * 2
def baseEnd_3110766 : Nat := 354959591480951410537523

theorem tailTrace_3110766 : CollatzResearch.WordTrace tailWord_3110766 prefixEnd_3110766 354959591480951410537523 := by
  unfold tailWord_3110766
  simp only [CollatzResearch.WordTrace]
  refine ⟨14182369631029191672603019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75639304698822355587216101 14182369631029191672603019)
  ·
    refine ⟨21273554446543787508904529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14182369631029191672603019 21273554446543787508904529)
    ·
      refine ⟨15955165834907840631678397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21273554446543787508904529 15955165834907840631678397)
      ·
        refine ⟨5983187188090440236879399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15955165834907840631678397 5983187188090440236879399)
        ·
          refine ⟨8974780782135660355319099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5983187188090440236879399 8974780782135660355319099)
          ·
            refine ⟨13462171173203490532978649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8974780782135660355319099 13462171173203490532978649)
            ·
              refine ⟨10096628379902617899733987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13462171173203490532978649 10096628379902617899733987)
              ·
                refine ⟨15144942569853926849600981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10096628379902617899733987 15144942569853926849600981)
                ·
                  refine ⟨354959591480951410537523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15144942569853926849600981 354959591480951410537523)
                  ·
                    rfl

theorem cell22_3110766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_3110766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3110766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3110766 prefixEnd_3110766 := by exact prefixLift 3110766
  have htrace : WordTrace (prefixWord ++ tailWord_3110766) baseStart_3110766 baseEnd_3110766 := by
    simpa [prefixWord, tailWord_3110766, baseEnd_3110766] using wordTrace_append hprefix tailTrace_3110766
  have hstable : (prefixWord ++ tailWord_3110766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110766).length < 2 ^ (prefixWord ++ tailWord_3110766).sum := by decide
  have hdescent : baseEnd_3110766 < baseStart_3110766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110779 : List Nat := [1, 1, 1, 1, 1, 5, 1, 4, 3, 4]
def baseStart_3110779 : Nat := 118140960795 + 3110779 * 2 ^ 59
def prefixEnd_3110779 : Nat := 4983230072969 + 3 ^ 40 * 3110779 * 2
def baseEnd_3110779 : Nat := 1064883224608526531037529

theorem tailTrace_3110779 : CollatzResearch.WordTrace tailWord_3110779 prefixEnd_3110779 1064883224608526531037529 := by
  unfold tailWord_3110779
  simp only [CollatzResearch.WordTrace]
  refine ⟨113459431197186436601047391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75639620798124291067364927 113459431197186436601047391)
  ·
    refine ⟨170189146795779654901571087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113459431197186436601047391 170189146795779654901571087)
    ·
      refine ⟨255283720193669482352356631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170189146795779654901571087 255283720193669482352356631)
      ·
        refine ⟨382925580290504223528534947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255283720193669482352356631 382925580290504223528534947)
        ·
          refine ⟨574388370435756335292802421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382925580290504223528534947 574388370435756335292802421)
          ·
            refine ⟨53848909728352156433700227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 574388370435756335292802421 53848909728352156433700227)
            ·
              refine ⟨80773364592528234650550341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53848909728352156433700227 80773364592528234650550341)
              ·
                refine ⟨15145005861099043996978189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80773364592528234650550341 15145005861099043996978189)
                ·
                  refine ⟨5679377197912141498866821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15145005861099043996978189 5679377197912141498866821)
                  ·
                    refine ⟨1064883224608526531037529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5679377197912141498866821 1064883224608526531037529)
                    ·
                      rfl

theorem cell22_3110779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 4].length) (baseStart_3110779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3110779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3110779 prefixEnd_3110779 := by exact prefixLift 3110779
  have htrace : WordTrace (prefixWord ++ tailWord_3110779) baseStart_3110779 baseEnd_3110779 := by
    simpa [prefixWord, tailWord_3110779, baseEnd_3110779] using wordTrace_append hprefix tailTrace_3110779
  have hstable : (prefixWord ++ tailWord_3110779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110779).length < 2 ^ (prefixWord ++ tailWord_3110779).sum := by decide
  have hdescent : baseEnd_3110779 < baseStart_3110779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110809 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 3, 5]
def baseStart_3110809 : Nat := 118140960795 + 3110809 * 2 ^ 59
def prefixEnd_3110809 : Nat := 4983230072969 + 3 ^ 40 * 3110809 * 2
def baseEnd_3110809 : Nat := 1064893494221616452787437

theorem tailTrace_3110809 : CollatzResearch.WordTrace tailWord_3110809 prefixEnd_3110809 1064893494221616452787437 := by
  unfold tailWord_3110809
  simp only [CollatzResearch.WordTrace]
  refine ⟨113460525387077751724639481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75640350258051834483092987 113460525387077751724639481)
  ·
    refine ⟨85095394040308313793479611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113460525387077751724639481 85095394040308313793479611)
    ·
      refine ⟨127643091060462470690219417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85095394040308313793479611 127643091060462470690219417)
      ·
        refine ⟨95732318295346853017664563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127643091060462470690219417 95732318295346853017664563)
        ·
          refine ⟨143598477443020279526496845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95732318295346853017664563 143598477443020279526496845)
          ·
            refine ⟨53849429041132604822436317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143598477443020279526496845 53849429041132604822436317)
            ·
              refine ⟨20193535890424726808413619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53849429041132604822436317 20193535890424726808413619)
              ·
                refine ⟨30290303835637090212620429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20193535890424726808413619 30290303835637090212620429)
                ·
                  refine ⟨11358863938363908829732661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30290303835637090212620429 11358863938363908829732661)
                  ·
                    refine ⟨1064893494221616452787437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11358863938363908829732661 1064893494221616452787437)
                    ·
                      rfl

theorem cell22_3110809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 5].length) (baseStart_3110809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3110809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3110809 prefixEnd_3110809 := by exact prefixLift 3110809
  have htrace : WordTrace (prefixWord ++ tailWord_3110809) baseStart_3110809 baseEnd_3110809 := by
    simpa [prefixWord, tailWord_3110809, baseEnd_3110809] using wordTrace_append hprefix tailTrace_3110809
  have hstable : (prefixWord ++ tailWord_3110809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110809).length < 2 ^ (prefixWord ++ tailWord_3110809).sum := by decide
  have hdescent : baseEnd_3110809 < baseStart_3110809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110871 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 5, 3]
def baseStart_3110871 : Nat := 118140960795 + 3110871 * 2 ^ 59
def prefixEnd_3110871 : Nat := 4983230072969 + 3 ^ 40 * 3110871 * 2
def baseEnd_3110871 : Nat := 1064914718088668957737247

theorem tailTrace_3110871 : CollatzResearch.WordTrace tailWord_3110871 prefixEnd_3110871 1064914718088668957737247 := by
  unfold tailWord_3110871
  simp only [CollatzResearch.WordTrace]
  refine ⟨113462786712853136313396467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75641857808568757542264311 113462786712853136313396467)
  ·
    refine ⟨170194180069279704470094701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113462786712853136313396467 170194180069279704470094701)
    ·
      refine ⟨63822817525979889176285513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170194180069279704470094701 63822817525979889176285513)
      ·
        refine ⟨47867113144484916882214135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63822817525979889176285513 47867113144484916882214135)
        ·
          refine ⟨71800669716727375323321203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47867113144484916882214135 71800669716727375323321203)
          ·
            refine ⟨107701004575091062984981805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71800669716727375323321203 107701004575091062984981805)
            ·
              refine ⟨40387876715659148619368177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107701004575091062984981805 40387876715659148619368177)
              ·
                refine ⟨30290907536744361464526133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40387876715659148619368177 30290907536744361464526133)
                ·
                  refine ⟨2839772581569783887299325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30290907536744361464526133 2839772581569783887299325)
                  ·
                    refine ⟨1064914718088668957737247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2839772581569783887299325 1064914718088668957737247)
                    ·
                      rfl

theorem cell22_3110871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 5, 3].length) (baseStart_3110871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3110871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3110871 prefixEnd_3110871 := by exact prefixLift 3110871
  have htrace : WordTrace (prefixWord ++ tailWord_3110871) baseStart_3110871 baseEnd_3110871 := by
    simpa [prefixWord, tailWord_3110871, baseEnd_3110871] using wordTrace_append hprefix tailTrace_3110871
  have hstable : (prefixWord ++ tailWord_3110871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110871).length < 2 ^ (prefixWord ++ tailWord_3110871).sum := by decide
  have hdescent : baseEnd_3110871 < baseStart_3110871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110877 : List Nat := [1, 4, 3, 1, 3, 2, 1, 2, 2, 3]
def baseStart_3110877 : Nat := 118140960795 + 3110877 * 2 ^ 59
def prefixEnd_3110877 : Nat := 4983230072969 + 3 ^ 40 * 3110877 * 2
def baseEnd_3110877 : Nat := 1064916772011286942087229

theorem tailTrace_3110877 : CollatzResearch.WordTrace tailWord_3110877 prefixEnd_3110877 1064916772011286942087229 := by
  unfold tailWord_3110877
  simp only [CollatzResearch.WordTrace]
  refine ⟨113463005550831399338114885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75642003700554266225409923 113463005550831399338114885)
  ·
    refine ⟨21274313540780887375896541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113463005550831399338114885 21274313540780887375896541)
    ·
      refine ⟨7977867577792832765961203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21274313540780887375896541 7977867577792832765961203)
      ·
        refine ⟨11966801366689249148941805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7977867577792832765961203 11966801366689249148941805)
        ·
          refine ⟨4487550512508468430853177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11966801366689249148941805 4487550512508468430853177)
          ·
            refine ⟨3365662884381351323139883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4487550512508468430853177 3365662884381351323139883)
            ·
              refine ⟨5048494326572026984709825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3365662884381351323139883 5048494326572026984709825)
              ·
                refine ⟨3786370744929020238532369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5048494326572026984709825 3786370744929020238532369)
                ·
                  refine ⟨2839778058696765178899277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3786370744929020238532369 2839778058696765178899277)
                  ·
                    refine ⟨1064916772011286942087229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2839778058696765178899277 1064916772011286942087229)
                    ·
                      rfl

theorem cell22_3110877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_3110877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3110877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3110877 prefixEnd_3110877 := by exact prefixLift 3110877
  have htrace : WordTrace (prefixWord ++ tailWord_3110877) baseStart_3110877 baseEnd_3110877 := by
    simpa [prefixWord, tailWord_3110877, baseEnd_3110877] using wordTrace_append hprefix tailTrace_3110877
  have hstable : (prefixWord ++ tailWord_3110877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110877).length < 2 ^ (prefixWord ++ tailWord_3110877).sum := by decide
  have hdescent : baseEnd_3110877 < baseStart_3110877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110997 : List Nat := [1, 3, 2, 2, 1, 5, 2, 2, 4]
def baseStart_3110997 : Nat := 118140960795 + 3110997 * 2 ^ 59
def prefixEnd_3110997 : Nat := 4983230072969 + 3 ^ 40 * 3110997 * 2
def baseEnd_3110997 : Nat := 354985950154548876362287

theorem tailTrace_3110997 : CollatzResearch.WordTrace tailWord_3110997 prefixEnd_3110997 354985950154548876362287 := by
  unfold tailWord_3110997
  simp only [CollatzResearch.WordTrace]
  refine ⟨113467382310396659832483245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75644921540264439888322163 113467382310396659832483245)
  ·
    refine ⟨42550268366398747437181217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113467382310396659832483245 42550268366398747437181217)
    ·
      refine ⟨31912701274799060577885913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42550268366398747437181217 31912701274799060577885913)
      ·
        refine ⟨23934525956099295433414435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31912701274799060577885913 23934525956099295433414435)
        ·
          refine ⟨35901788934148943150121653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23934525956099295433414435 35901788934148943150121653)
          ·
            refine ⟨3365792712576463420323905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35901788934148943150121653 3365792712576463420323905)
            ·
              refine ⟨2524344534432347565242929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3365792712576463420323905 2524344534432347565242929)
              ·
                refine ⟨1893258400824260673932197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2524344534432347565242929 1893258400824260673932197)
                ·
                  refine ⟨354985950154548876362287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1893258400824260673932197 354985950154548876362287)
                  ·
                    rfl

theorem cell22_3110997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 2, 4].length) (baseStart_3110997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3110997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3110997 prefixEnd_3110997 := by exact prefixLift 3110997
  have htrace : WordTrace (prefixWord ++ tailWord_3110997) baseStart_3110997 baseEnd_3110997 := by
    simpa [prefixWord, tailWord_3110997, baseEnd_3110997] using wordTrace_append hprefix tailTrace_3110997
  have hstable : (prefixWord ++ tailWord_3110997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110997).length < 2 ^ (prefixWord ++ tailWord_3110997).sum := by decide
  have hdescent : baseEnd_3110997 < baseStart_3110997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111008 : List Nat := [2, 1, 1, 3, 2, 5, 1, 7]
def baseStart_3111008 : Nat := 118140960795 + 3111008 * 2 ^ 59
def prefixEnd_3111008 : Nat := 4983230072969 + 3 ^ 40 * 3111008 * 2
def baseEnd_3111008 : Nat := 118329068443160696340203

theorem tailTrace_3111008 : CollatzResearch.WordTrace tailWord_3111008 prefixEnd_3111008 118329068443160696340203 := by
  unfold tailWord_3111008
  simp only [CollatzResearch.WordTrace]
  refine ⟨56733891756678404355566839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75645189008904539140755785 56733891756678404355566839)
  ·
    refine ⟨85100837635017606533350259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56733891756678404355566839 85100837635017606533350259)
    ·
      refine ⟨127651256452526409800025389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85100837635017606533350259 127651256452526409800025389)
      ·
        refine ⟨47869221169697403675009521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127651256452526409800025389 47869221169697403675009521)
        ·
          refine ⟨35901915877273052756257141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47869221169697403675009521 35901915877273052756257141)
          ·
            refine ⟨3365804613494348695899107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35901915877273052756257141 3365804613494348695899107)
            ·
              refine ⟨5048706920241523043848661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3365804613494348695899107 5048706920241523043848661)
              ·
                refine ⟨118329068443160696340203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5048706920241523043848661 118329068443160696340203)
                ·
                  rfl

theorem cell22_3111008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 7].length) (baseStart_3111008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3111008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3111008 prefixEnd_3111008 := by exact prefixLift 3111008
  have htrace : WordTrace (prefixWord ++ tailWord_3111008) baseStart_3111008 baseEnd_3111008 := by
    simpa [prefixWord, tailWord_3111008, baseEnd_3111008] using wordTrace_append hprefix tailTrace_3111008
  have hstable : (prefixWord ++ tailWord_3111008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111008).length < 2 ^ (prefixWord ++ tailWord_3111008).sum := by decide
  have hdescent : baseEnd_3111008 < baseStart_3111008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111023 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 5, 3]
def baseStart_3111023 : Nat := 118140960795 + 3111023 * 2 ^ 59
def prefixEnd_3111023 : Nat := 4983230072969 + 3 ^ 40 * 3111023 * 2
def baseEnd_3111023 : Nat := 1064966750794991227936781

theorem tailTrace_3111023 : CollatzResearch.WordTrace tailWord_3111023 prefixEnd_3111023 1064966750794991227936781 := by
  unfold tailWord_3111023
  simp only [CollatzResearch.WordTrace]
  refine ⟨113468330608302466272929723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75645553738868310848619815 113468330608302466272929723)
  ·
    refine ⟨170202495912453699409394585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113468330608302466272929723 170202495912453699409394585)
    ·
      refine ⟨127651871934340274557045939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170202495912453699409394585 127651871934340274557045939)
      ·
        refine ⟨191477807901510411835568909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127651871934340274557045939 191477807901510411835568909)
        ·
          refine ⟨71804177963066404438338341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191477807901510411835568909 71804177963066404438338341)
          ·
            refine ⟨13463283368074950832188439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71804177963066404438338341 13463283368074950832188439)
            ·
              refine ⟨20194925052112426248282659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13463283368074950832188439 20194925052112426248282659)
              ·
                refine ⟨30292387578168639372423989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20194925052112426248282659 30292387578168639372423989)
                ·
                  refine ⟨2839911335453309941164749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30292387578168639372423989 2839911335453309941164749)
                  ·
                    refine ⟨1064966750794991227936781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2839911335453309941164749 1064966750794991227936781)
                    ·
                      rfl

theorem cell22_3111023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 5, 3].length) (baseStart_3111023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3111023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3111023 prefixEnd_3111023 := by exact prefixLift 3111023
  have htrace : WordTrace (prefixWord ++ tailWord_3111023) baseStart_3111023 baseEnd_3111023 := by
    simpa [prefixWord, tailWord_3111023, baseEnd_3111023] using wordTrace_append hprefix tailTrace_3111023
  have hstable : (prefixWord ++ tailWord_3111023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111023).length < 2 ^ (prefixWord ++ tailWord_3111023).sum := by decide
  have hdescent : baseEnd_3111023 < baseStart_3111023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111068 : List Nat := [2, 2, 3, 2, 1, 1, 1, 3, 2, 5]
def baseStart_3111068 : Nat := 118140960795 + 3111068 * 2 ^ 59
def prefixEnd_3111068 : Nat := 4983230072969 + 3 ^ 40 * 3111068 * 2
def baseEnd_3111068 : Nat := 1064982155214626110561643

theorem tailTrace_3111068 : CollatzResearch.WordTrace tailWord_3111068 prefixEnd_3111068 1064982155214626110561643 := by
  unfold tailWord_3111068
  simp only [CollatzResearch.WordTrace]
  refine ⟨56734985946569719479158929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75646647928759625972211905 56734985946569719479158929)
  ·
    refine ⟨42551239459927289609369197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56734985946569719479158929 42551239459927289609369197)
    ·
      refine ⟨15956714797472733603513449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42551239459927289609369197 15956714797472733603513449)
      ·
        refine ⟨11967536098104550202635087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15956714797472733603513449 11967536098104550202635087)
        ·
          refine ⟨17951304147156825303952631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11967536098104550202635087 17951304147156825303952631)
          ·
            refine ⟨26926956220735237955928947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17951304147156825303952631 26926956220735237955928947)
            ·
              refine ⟨40390434331102856933893421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26926956220735237955928947 40390434331102856933893421)
              ·
                refine ⟨15146412874163571350210033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40390434331102856933893421 15146412874163571350210033)
                ·
                  refine ⟨11359809655622678512657525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15146412874163571350210033 11359809655622678512657525)
                  ·
                    refine ⟨1064982155214626110561643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11359809655622678512657525 1064982155214626110561643)
                    ·
                      rfl

theorem cell22_3111068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_3111068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3111068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3111068 prefixEnd_3111068 := by exact prefixLift 3111068
  have htrace : WordTrace (prefixWord ++ tailWord_3111068) baseStart_3111068 baseEnd_3111068 := by
    simpa [prefixWord, tailWord_3111068, baseEnd_3111068] using wordTrace_append hprefix tailTrace_3111068
  have hstable : (prefixWord ++ tailWord_3111068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111068).length < 2 ^ (prefixWord ++ tailWord_3111068).sum := by decide
  have hdescent : baseEnd_3111068 < baseStart_3111068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111203 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 1, 7]
def baseStart_3111203 : Nat := 118140960795 + 3111203 * 2 ^ 59
def prefixEnd_3111203 : Nat := 4983230072969 + 3 ^ 40 * 3111203 * 2
def baseEnd_3111203 : Nat := 1065028368473530758436229

theorem tailTrace_3111203 : CollatzResearch.WordTrace tailWord_3111203 prefixEnd_3111203 1065028368473530758436229 := by
  unfold tailWord_3111203
  simp only [CollatzResearch.WordTrace]
  refine ⟨113474895747650357014482263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75649930498433571342988175 113474895747650357014482263)
  ·
    refine ⟨170212343621475535521723395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113474895747650357014482263 170212343621475535521723395)
    ·
      refine ⟨255318515432213303282585093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170212343621475535521723395 255318515432213303282585093)
      ·
        refine ⟨47872221643539994365484705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 255318515432213303282585093 47872221643539994365484705)
        ·
          refine ⟨35904166232654995774113529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47872221643539994365484705 35904166232654995774113529)
          ·
            refine ⟨26928124674491246830585147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35904166232654995774113529 26928124674491246830585147)
            ·
              refine ⟨40392187011736870245877721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26928124674491246830585147 40392187011736870245877721)
              ·
                refine ⟨30294140258802652684408291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40392187011736870245877721 30294140258802652684408291)
                ·
                  refine ⟨45441210388203979026612437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30294140258802652684408291 45441210388203979026612437)
                  ·
                    refine ⟨1065028368473530758436229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45441210388203979026612437 1065028368473530758436229)
                    ·
                      rfl

theorem cell22_3111203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 7].length) (baseStart_3111203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3111203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3111203 prefixEnd_3111203 := by exact prefixLift 3111203
  have htrace : WordTrace (prefixWord ++ tailWord_3111203) baseStart_3111203 baseEnd_3111203 := by
    simpa [prefixWord, tailWord_3111203, baseEnd_3111203] using wordTrace_append hprefix tailTrace_3111203
  have hstable : (prefixWord ++ tailWord_3111203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111203).length < 2 ^ (prefixWord ++ tailWord_3111203).sum := by decide
  have hdescent : baseEnd_3111203 < baseStart_3111203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111250 : List Nat := [3, 2, 2, 1, 1, 1, 4, 2, 6]
def baseStart_3111250 : Nat := 118140960795 + 3111250 * 2 ^ 59
def prefixEnd_3111250 : Nat := 4983230072969 + 3 ^ 40 * 3111250 * 2
def baseEnd_3111250 : Nat := 355014819178012767503695

theorem tailTrace_3111250 : CollatzResearch.WordTrace tailWord_3111250 prefixEnd_3111250 355014819178012767503695 := by
  unfold tailWord_3111250
  simp only [CollatzResearch.WordTrace]
  refine ⟨28369152494620021010360801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75651073318986722694295469 28369152494620021010360801)
  ·
    refine ⟨21276864370965015757770601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28369152494620021010360801 21276864370965015757770601)
    ·
      refine ⟨15957648278223761818327951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21276864370965015757770601 15957648278223761818327951)
      ·
        refine ⟨23936472417335642727491927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15957648278223761818327951 23936472417335642727491927)
        ·
          refine ⟨35904708626003464091237891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23936472417335642727491927 35904708626003464091237891)
          ·
            refine ⟨53857062939005196136856837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35904708626003464091237891 53857062939005196136856837)
            ·
              refine ⟨10098199301063474275660657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53857062939005196136856837 10098199301063474275660657)
              ·
                refine ⟨7573649475797605706745493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10098199301063474275660657 7573649475797605706745493)
                ·
                  refine ⟨355014819178012767503695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7573649475797605706745493 355014819178012767503695)
                  ·
                    rfl

theorem cell22_3111250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_3111250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3111250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3111250 prefixEnd_3111250 := by exact prefixLift 3111250
  have htrace : WordTrace (prefixWord ++ tailWord_3111250) baseStart_3111250 baseEnd_3111250 := by
    simpa [prefixWord, tailWord_3111250, baseEnd_3111250] using wordTrace_append hprefix tailTrace_3111250
  have hstable : (prefixWord ++ tailWord_3111250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111250).length < 2 ^ (prefixWord ++ tailWord_3111250).sum := by decide
  have hdescent : baseEnd_3111250 < baseStart_3111250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111252 : List Nat := [2, 4, 1, 1, 2, 2, 1, 4, 1, 4]
def baseStart_3111252 : Nat := 118140960795 + 3111252 * 2 ^ 59
def prefixEnd_3111252 : Nat := 4983230072969 + 3 ^ 40 * 3111252 * 2
def baseEnd_3111252 : Nat := 1065045142174910963961079

theorem tailTrace_3111252 : CollatzResearch.WordTrace tailWord_3111252 prefixEnd_3111252 1065045142174910963961079 := by
  unfold tailWord_3111252
  simp only [CollatzResearch.WordTrace]
  refine ⟨56738341462236419191508005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75651121949648558922010673 56738341462236419191508005)
  ·
    refine ⟨10638439024169328598407751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56738341462236419191508005 10638439024169328598407751)
    ·
      refine ⟨15957658536253992897611627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10638439024169328598407751 15957658536253992897611627)
      ·
        refine ⟨23936487804380989346417441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15957658536253992897611627 23936487804380989346417441)
        ·
          refine ⟨17952365853285742009813081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23936487804380989346417441 17952365853285742009813081)
          ·
            refine ⟨13464274389964306507359811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17952365853285742009813081 13464274389964306507359811)
            ·
              refine ⟨20196411584946459761039717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13464274389964306507359811 20196411584946459761039717)
              ·
                refine ⟨3786827172177461205194947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20196411584946459761039717 3786827172177461205194947)
                ·
                  refine ⟨5680240758266191807792421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3786827172177461205194947 5680240758266191807792421)
                  ·
                    refine ⟨1065045142174910963961079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5680240758266191807792421 1065045142174910963961079)
                    ·
                      rfl

theorem cell22_3111252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_3111252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3111252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3111252 prefixEnd_3111252 := by exact prefixLift 3111252
  have htrace : WordTrace (prefixWord ++ tailWord_3111252) baseStart_3111252 baseEnd_3111252 := by
    simpa [prefixWord, tailWord_3111252, baseEnd_3111252] using wordTrace_append hprefix tailTrace_3111252
  have hstable : (prefixWord ++ tailWord_3111252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111252).length < 2 ^ (prefixWord ++ tailWord_3111252).sum := by decide
  have hdescent : baseEnd_3111252 < baseStart_3111252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111260 : List Nat := [2, 2, 4, 3, 2, 1, 1, 3, 1, 3]
def baseStart_3111260 : Nat := 118140960795 + 3111260 * 2 ^ 59
def prefixEnd_3111260 : Nat := 4983230072969 + 3 ^ 40 * 3111260 * 2
def baseEnd_3111260 : Nat := 1065047880738401609761055

theorem tailTrace_3111260 : CollatzResearch.WordTrace tailWord_3111260 prefixEnd_3111260 1065047880738401609761055 := by
  unfold tailWord_3111260
  simp only [CollatzResearch.WordTrace]
  refine ⟨56738487354221927874653617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75651316472295903832871489 56738487354221927874653617)
  ·
    refine ⟨42553865515666445905990213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56738487354221927874653617 42553865515666445905990213)
    ·
      refine ⟨7978849784187458607373165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42553865515666445905990213 7978849784187458607373165)
      ·
        refine ⟨2992068669070296977764937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7978849784187458607373165 2992068669070296977764937)
        ·
          refine ⟨2244051501802722733323703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2992068669070296977764937 2244051501802722733323703)
          ·
            refine ⟨3366077252704084099985555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2244051501802722733323703 3366077252704084099985555)
            ·
              refine ⟨5049115879056126149978333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3366077252704084099985555 5049115879056126149978333)
              ·
                refine ⟨1893418454646047306241875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5049115879056126149978333 1893418454646047306241875)
                ·
                  refine ⟨2840127681969070959362813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1893418454646047306241875 2840127681969070959362813)
                  ·
                    refine ⟨1065047880738401609761055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2840127681969070959362813 1065047880738401609761055)
                    ·
                      rfl

theorem cell22_3111260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_3111260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3111260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3111260 prefixEnd_3111260 := by exact prefixLift 3111260
  have htrace : WordTrace (prefixWord ++ tailWord_3111260) baseStart_3111260 baseEnd_3111260 := by
    simpa [prefixWord, tailWord_3111260, baseEnd_3111260] using wordTrace_append hprefix tailTrace_3111260
  have hstable : (prefixWord ++ tailWord_3111260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111260).length < 2 ^ (prefixWord ++ tailWord_3111260).sum := by decide
  have hdescent : baseEnd_3111260 < baseStart_3111260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111280 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 4, 4]
def baseStart_3111280 : Nat := 118140960795 + 3111280 * 2 ^ 59
def prefixEnd_3111280 : Nat := 4983230072969 + 3 ^ 40 * 3111280 * 2
def baseEnd_3111280 : Nat := 1065054727147128224260993

theorem tailTrace_3111280 : CollatzResearch.WordTrace tailWord_3111280 prefixEnd_3111280 1065054727147128224260993 := by
  unfold tailWord_3111280
  simp only [CollatzResearch.WordTrace]
  refine ⟨56738852084185699582517647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75651802778914266110023529 56738852084185699582517647)
  ·
    refine ⟨85108278126278549373776471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56738852084185699582517647 85108278126278549373776471)
    ·
      refine ⟨127662417189417824060664707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85108278126278549373776471 127662417189417824060664707)
      ·
        refine ⟨191493625784126736090997061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127662417189417824060664707 191493625784126736090997061)
        ·
          refine ⟨35905054834523763017061949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191493625784126736090997061 35905054834523763017061949)
          ·
            refine ⟨13464395562946411131398231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35905054834523763017061949 13464395562946411131398231)
            ·
              refine ⟨20196593344419616697097347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13464395562946411131398231 20196593344419616697097347)
              ·
                refine ⟨30294890016629425045646021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20196593344419616697097347 30294890016629425045646021)
                ·
                  refine ⟨5680291878118017196058629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30294890016629425045646021 5680291878118017196058629)
                  ·
                    refine ⟨1065054727147128224260993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5680291878118017196058629 1065054727147128224260993)
                    ·
                      rfl

theorem cell22_3111280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 4, 4].length) (baseStart_3111280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3111280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3111280 prefixEnd_3111280 := by exact prefixLift 3111280
  have htrace : WordTrace (prefixWord ++ tailWord_3111280) baseStart_3111280 baseEnd_3111280 := by
    simpa [prefixWord, tailWord_3111280, baseEnd_3111280] using wordTrace_append hprefix tailTrace_3111280
  have hstable : (prefixWord ++ tailWord_3111280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111280).length < 2 ^ (prefixWord ++ tailWord_3111280).sum := by decide
  have hdescent : baseEnd_3111280 < baseStart_3111280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111282 : List Nat := [3, 2, 1, 2, 1, 3, 2, 1, 4, 3]
def baseStart_3111282 : Nat := 118140960795 + 3111282 * 2 ^ 59
def prefixEnd_3111282 : Nat := 4983230072969 + 3 ^ 40 * 3111282 * 2
def baseEnd_3111282 : Nat := 1065055411788000885710987

theorem tailTrace_3111282 : CollatzResearch.WordTrace tailWord_3111282 prefixEnd_3111282 1065055411788000885710987 := by
  unfold tailWord_3111282
  simp only [CollatzResearch.WordTrace]
  refine ⟨28369444278591038376652025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75651851409576102337738733 28369444278591038376652025)
  ·
    refine ⟨21277083208943278782489019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28369444278591038376652025 21277083208943278782489019)
    ·
      refine ⟨31915624813414918173733529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21277083208943278782489019 31915624813414918173733529)
      ·
        refine ⟨23936718610061188630300147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31915624813414918173733529 23936718610061188630300147)
        ·
          refine ⟨35905077915091782945450221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23936718610061188630300147 35905077915091782945450221)
          ·
            refine ⟨13464404218159418604543833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35905077915091782945450221 13464404218159418604543833)
            ·
              refine ⟨10098303163619563953407875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13464404218159418604543833 10098303163619563953407875)
              ·
                refine ⟨15147454745429345930111813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10098303163619563953407875 15147454745429345930111813)
                ·
                  refine ⟨2840147764768002361895965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15147454745429345930111813 2840147764768002361895965)
                  ·
                    refine ⟨1065055411788000885710987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2840147764768002361895965 1065055411788000885710987)
                    ·
                      rfl

theorem cell22_3111282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_3111282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3111282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3111282 prefixEnd_3111282 := by exact prefixLift 3111282
  have htrace : WordTrace (prefixWord ++ tailWord_3111282) baseStart_3111282 baseEnd_3111282 := by
    simpa [prefixWord, tailWord_3111282, baseEnd_3111282] using wordTrace_append hprefix tailTrace_3111282
  have hstable : (prefixWord ++ tailWord_3111282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111282).length < 2 ^ (prefixWord ++ tailWord_3111282).sum := by decide
  have hdescent : baseEnd_3111282 < baseStart_3111282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111299 : List Nat := [1, 1, 1, 3, 6, 1, 1, 3, 2, 3]
def baseStart_3111299 : Nat := 118140960795 + 3111299 * 2 ^ 59
def prefixEnd_3111299 : Nat := 4983230072969 + 3 ^ 40 * 3111299 * 2
def baseEnd_3111299 : Nat := 1065061231235418508035935

theorem tailTrace_3111299 : CollatzResearch.WordTrace tailWord_3111299 prefixEnd_3111299 1065061231235418508035935 := by
  unfold tailWord_3111299
  simp only [CollatzResearch.WordTrace]
  refine ⟨113478397155302565409976951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75652264770201710273317967 113478397155302565409976951)
  ·
    refine ⟨170217595732953848114965427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113478397155302565409976951 170217595732953848114965427)
    ·
      refine ⟨255326393599430772172448141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170217595732953848114965427 255326393599430772172448141)
      ·
        refine ⟨95747397599786539564668053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255326393599430772172448141 95747397599786539564668053)
        ·
          refine ⟨4488159262489994042093815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 95747397599786539564668053 4488159262489994042093815)
          ·
            refine ⟨6732238893734991063140723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4488159262489994042093815 6732238893734991063140723)
            ·
              refine ⟨10098358340602486594711085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6732238893734991063140723 10098358340602486594711085)
              ·
                refine ⟨3786884377725932473016657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10098358340602486594711085 3786884377725932473016657)
                ·
                  refine ⟨2840163283294449354762493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3786884377725932473016657 2840163283294449354762493)
                  ·
                    refine ⟨1065061231235418508035935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2840163283294449354762493 1065061231235418508035935)
                    ·
                      rfl

theorem cell22_3111299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 2, 3].length) (baseStart_3111299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3111299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3111299 prefixEnd_3111299 := by exact prefixLift 3111299
  have htrace : WordTrace (prefixWord ++ tailWord_3111299) baseStart_3111299 baseEnd_3111299 := by
    simpa [prefixWord, tailWord_3111299, baseEnd_3111299] using wordTrace_append hprefix tailTrace_3111299
  have hstable : (prefixWord ++ tailWord_3111299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111299).length < 2 ^ (prefixWord ++ tailWord_3111299).sum := by decide
  have hdescent : baseEnd_3111299 < baseStart_3111299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111357 : List Nat := [1, 4, 1, 2, 2, 2, 2, 3, 5]
def baseStart_3111357 : Nat := 118140960795 + 3111357 * 2 ^ 59
def prefixEnd_3111357 : Nat := 4983230072969 + 3 ^ 40 * 3111357 * 2
def baseEnd_3111357 : Nat := 355027028606908563361919

theorem tailTrace_3111357 : CollatzResearch.WordTrace tailWord_3111357 prefixEnd_3111357 355027028606908563361919 := by
  unfold tailWord_3111357
  simp only [CollatzResearch.WordTrace]
  refine ⟨113480512589092441315588325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75653675059394960877058883 113480512589092441315588325)
  ·
    refine ⟨21277596110454832746672811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113480512589092441315588325 21277596110454832746672811)
    ·
      refine ⟨31916394165682249120009217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21277596110454832746672811 31916394165682249120009217)
      ·
        refine ⟨23937295624261686840006913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31916394165682249120009217 23937295624261686840006913)
        ·
          refine ⟨17952971718196265130005185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23937295624261686840006913 17952971718196265130005185)
          ·
            refine ⟨13464728788647198847503889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17952971718196265130005185 13464728788647198847503889)
            ·
              refine ⟨10098546591485399135627917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13464728788647198847503889 10098546591485399135627917)
              ·
                refine ⟨3786954971807024675860469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10098546591485399135627917 3786954971807024675860469)
                ·
                  refine ⟨355027028606908563361919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3786954971807024675860469 355027028606908563361919)
                  ·
                    rfl

theorem cell22_3111357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_3111357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3111357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3111357 prefixEnd_3111357 := by exact prefixLift 3111357
  have htrace : WordTrace (prefixWord ++ tailWord_3111357) baseStart_3111357 baseEnd_3111357 := by
    simpa [prefixWord, tailWord_3111357, baseEnd_3111357] using wordTrace_append hprefix tailTrace_3111357
  have hstable : (prefixWord ++ tailWord_3111357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111357).length < 2 ^ (prefixWord ++ tailWord_3111357).sum := by decide
  have hdescent : baseEnd_3111357 < baseStart_3111357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111385 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 8]
def baseStart_3111385 : Nat := 118140960795 + 3111385 * 2 ^ 59
def prefixEnd_3111385 : Nat := 4983230072969 + 3 ^ 40 * 3111385 * 2
def baseEnd_3111385 : Nat := 355030223597647650128557

theorem tailTrace_3111385 : CollatzResearch.WordTrace tailWord_3111385 prefixEnd_3111385 355030223597647650128557 := by
  unfold tailWord_3111385
  simp only [CollatzResearch.WordTrace]
  refine ⟨113481533832991002097607609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75654355888660668065071739 113481533832991002097607609)
  ·
    refine ⟨85111150374743251573205707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113481533832991002097607609 85111150374743251573205707)
    ·
      refine ⟨127666725562114877359808561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85111150374743251573205707 127666725562114877359808561)
      ·
        refine ⟨95750044171586158019856421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127666725562114877359808561 95750044171586158019856421)
        ·
          refine ⟨17953133282172404628723079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95750044171586158019856421 17953133282172404628723079)
          ·
            refine ⟨26929699923258606943084619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17953133282172404628723079 26929699923258606943084619)
            ·
              refine ⟨40394549884887910414626929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26929699923258606943084619 40394549884887910414626929)
              ·
                refine ⟨30295912413665932810970197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40394549884887910414626929 30295912413665932810970197)
                ·
                  refine ⟨355030223597647650128557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30295912413665932810970197 355030223597647650128557)
                  ·
                    rfl

theorem cell22_3111385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 8].length) (baseStart_3111385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3111385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3111385 prefixEnd_3111385 := by exact prefixLift 3111385
  have htrace : WordTrace (prefixWord ++ tailWord_3111385) baseStart_3111385 baseEnd_3111385 := by
    simpa [prefixWord, tailWord_3111385, baseEnd_3111385] using wordTrace_append hprefix tailTrace_3111385
  have hstable : (prefixWord ++ tailWord_3111385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111385).length < 2 ^ (prefixWord ++ tailWord_3111385).sum := by decide
  have hdescent : baseEnd_3111385 < baseStart_3111385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111402 : List Nat := [3, 1, 3, 1, 3, 1, 1, 3, 6]
def baseStart_3111402 : Nat := 118140960795 + 3111402 * 2 ^ 59
def prefixEnd_3111402 : Nat := 4983230072969 + 3 ^ 40 * 3111402 * 2
def baseEnd_3111402 : Nat := 355032163413453524236873

theorem tailTrace_3111402 : CollatzResearch.WordTrace tailWord_3111402 prefixEnd_3111402 355032163413453524236873 := by
  unfold tailWord_3111402
  simp only [CollatzResearch.WordTrace]
  refine ⟨28370538468482353500244115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75654769249286276000650973 28370538468482353500244115)
  ·
    refine ⟨42555807702723530250366173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28370538468482353500244115 42555807702723530250366173)
    ·
      refine ⟨15958427888521323843887315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42555807702723530250366173 15958427888521323843887315)
      ·
        refine ⟨23937641832781985765830973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15958427888521323843887315 23937641832781985765830973)
        ·
          refine ⟨8976615687293244662186615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23937641832781985765830973 8976615687293244662186615)
          ·
            refine ⟨13464923530939866993279923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8976615687293244662186615 13464923530939866993279923)
            ·
              refine ⟨20197385296409800489919885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13464923530939866993279923 20197385296409800489919885)
              ·
                refine ⟨7574019486153675183719957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20197385296409800489919885 7574019486153675183719957)
                ·
                  refine ⟨355032163413453524236873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7574019486153675183719957 355032163413453524236873)
                  ·
                    rfl

theorem cell22_3111402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 6].length) (baseStart_3111402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3111402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3111402 prefixEnd_3111402 := by exact prefixLift 3111402
  have htrace : WordTrace (prefixWord ++ tailWord_3111402) baseStart_3111402 baseEnd_3111402 := by
    simpa [prefixWord, tailWord_3111402, baseEnd_3111402] using wordTrace_append hprefix tailTrace_3111402
  have hstable : (prefixWord ++ tailWord_3111402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111402).length < 2 ^ (prefixWord ++ tailWord_3111402).sum := by decide
  have hdescent : baseEnd_3111402 < baseStart_3111402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111417 : List Nat := [1, 2, 1, 3, 1, 2, 5, 1, 1, 5]
def baseStart_3111417 : Nat := 118140960795 + 3111417 * 2 ^ 59
def prefixEnd_3111417 : Nat := 4983230072969 + 3 ^ 40 * 3111417 * 2
def baseEnd_3111417 : Nat := 1065101625046905533585573

theorem tailTrace_3111417 : CollatzResearch.WordTrace tailWord_3111417 prefixEnd_3111417 1065101625046905533585573 := by
  unfold tailWord_3111417
  simp only [CollatzResearch.WordTrace]
  refine ⟨113482700968875071562772505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75655133979250047708515003 113482700968875071562772505)
  ·
    refine ⟨85112025726656303672079379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113482700968875071562772505 85112025726656303672079379)
    ·
      refine ⟨127668038589984455508119069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85112025726656303672079379 127668038589984455508119069)
      ·
        refine ⟨47875514471244170815544651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127668038589984455508119069 47875514471244170815544651)
        ·
          refine ⟨71813271706866256223316977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47875514471244170815544651 71813271706866256223316977)
          ·
            refine ⟨53859953780149692167487733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71813271706866256223316977 53859953780149692167487733)
            ·
              refine ⟨5049370666889033640701975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53859953780149692167487733 5049370666889033640701975)
              ·
                refine ⟨7574056000333550461052963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5049370666889033640701975 7574056000333550461052963)
                ·
                  refine ⟨11361084000500325691579445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7574056000333550461052963 11361084000500325691579445)
                  ·
                    refine ⟨1065101625046905533585573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11361084000500325691579445 1065101625046905533585573)
                    ·
                      rfl

theorem cell22_3111417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 5].length) (baseStart_3111417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3111417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3111417 prefixEnd_3111417 := by exact prefixLift 3111417
  have htrace : WordTrace (prefixWord ++ tailWord_3111417) baseStart_3111417 baseEnd_3111417 := by
    simpa [prefixWord, tailWord_3111417, baseEnd_3111417] using wordTrace_append hprefix tailTrace_3111417
  have hstable : (prefixWord ++ tailWord_3111417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111417).length < 2 ^ (prefixWord ++ tailWord_3111417).sum := by decide
  have hdescent : baseEnd_3111417 < baseStart_3111417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111432 : List Nat := [2, 1, 3, 2, 1, 1, 1, 5, 2, 4]
def baseStart_3111432 : Nat := 118140960795 + 3111432 * 2 ^ 59
def prefixEnd_3111432 : Nat := 4983230072969 + 3 ^ 40 * 3111432 * 2
def baseEnd_3111432 : Nat := 1065106759853450494460527

theorem tailTrace_3111432 : CollatzResearch.WordTrace tailWord_3111432 prefixEnd_3111432 1065106759853450494460527 := by
  unfold tailWord_3111432
  simp only [CollatzResearch.WordTrace]
  refine ⟨56741624031910364562284275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75655498709213819416379033 56741624031910364562284275)
  ·
    refine ⟨85112436047865546843426413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56741624031910364562284275 85112436047865546843426413)
    ·
      refine ⟨31917163517949580066284905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85112436047865546843426413 31917163517949580066284905)
      ·
        refine ⟨23937872638462185049713679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31917163517949580066284905 23937872638462185049713679)
        ·
          refine ⟨35906808957693277574570519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23937872638462185049713679 35906808957693277574570519)
          ·
            refine ⟨53860213436539916361855779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35906808957693277574570519 53860213436539916361855779)
            ·
              refine ⟨80790320154809874542783669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53860213436539916361855779 80790320154809874542783669)
              ·
                refine ⟨7574092514513425738385969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80790320154809874542783669 7574092514513425738385969)
                ·
                  refine ⟨5680569385885069303789477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7574092514513425738385969 5680569385885069303789477)
                  ·
                    refine ⟨1065106759853450494460527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5680569385885069303789477 1065106759853450494460527)
                    ·
                      rfl

theorem cell22_3111432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_3111432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3111432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3111432 prefixEnd_3111432 := by exact prefixLift 3111432
  have htrace : WordTrace (prefixWord ++ tailWord_3111432) baseStart_3111432 baseEnd_3111432 := by
    simpa [prefixWord, tailWord_3111432, baseEnd_3111432] using wordTrace_append hprefix tailTrace_3111432
  have hstable : (prefixWord ++ tailWord_3111432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111432).length < 2 ^ (prefixWord ++ tailWord_3111432).sum := by decide
  have hdescent : baseEnd_3111432 < baseStart_3111432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111436 : List Nat := [2, 2, 1, 2, 4, 3, 1, 3, 4]
def baseStart_3111436 : Nat := 118140960795 + 3111436 * 2 ^ 59
def prefixEnd_3111436 : Nat := 4983230072969 + 3 ^ 40 * 3111436 * 2
def baseEnd_3111436 : Nat := 355036043045065272453505

theorem tailTrace_3111436 : CollatzResearch.WordTrace tailWord_3111436 prefixEnd_3111436 355036043045065272453505 := by
  unfold tailWord_3111436
  simp only [CollatzResearch.WordTrace]
  refine ⟨56741696977903118903857081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75655595970537491871809441 56741696977903118903857081)
  ·
    refine ⟨42556272733427339177892811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56741696977903118903857081 42556272733427339177892811)
    ·
      refine ⟨63834409100141008766839217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42556272733427339177892811 63834409100141008766839217)
      ·
        refine ⟨47875806825105756575129413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63834409100141008766839217 47875806825105756575129413)
        ·
          refine ⟨8976713779707329357836765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47875806825105756575129413 8976713779707329357836765)
          ·
            refine ⟨3366267667390248509188787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8976713779707329357836765 3366267667390248509188787)
            ·
              refine ⟨5049401501085372763783181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3366267667390248509188787 5049401501085372763783181)
              ·
                refine ⟨1893525562907014786418693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5049401501085372763783181 1893525562907014786418693)
                ·
                  refine ⟨355036043045065272453505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1893525562907014786418693 355036043045065272453505)
                  ·
                    rfl

theorem cell22_3111436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 3, 4].length) (baseStart_3111436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3111436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3111436 prefixEnd_3111436 := by exact prefixLift 3111436
  have htrace : WordTrace (prefixWord ++ tailWord_3111436) baseStart_3111436 baseEnd_3111436 := by
    simpa [prefixWord, tailWord_3111436, baseEnd_3111436] using wordTrace_append hprefix tailTrace_3111436
  have hstable : (prefixWord ++ tailWord_3111436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111436).length < 2 ^ (prefixWord ++ tailWord_3111436).sum := by decide
  have hdescent : baseEnd_3111436 < baseStart_3111436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111464 : List Nat := [2, 1, 5, 2, 1, 2, 2, 7]
def baseStart_3111464 : Nat := 118140960795 + 3111464 * 2 ^ 59
def prefixEnd_3111464 : Nat := 4983230072969 + 3 ^ 40 * 3111464 * 2
def baseEnd_3111464 : Nat := 118346412678601453073381

theorem tailTrace_3111464 : CollatzResearch.WordTrace tailWord_3111464 prefixEnd_3111464 118346412678601453073381 := by
  unfold tailWord_3111464
  simp only [CollatzResearch.WordTrace]
  refine ⟨56742207599852399294866723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75656276799803199059822297 56742207599852399294866723)
  ·
    refine ⟨85113311399778598942300085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56742207599852399294866723 85113311399778598942300085)
    ·
      refine ⟨7979372943729243650840633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85113311399778598942300085 7979372943729243650840633)
      ·
        refine ⟨5984529707796932738130475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7979372943729243650840633 5984529707796932738130475)
        ·
          refine ⟨8976794561695399107195713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5984529707796932738130475 8976794561695399107195713)
          ·
            refine ⟨6732595921271549330396785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8976794561695399107195713 6732595921271549330396785)
            ·
              refine ⟨5049446940953661997797589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6732595921271549330396785 5049446940953661997797589)
              ·
                refine ⟨118346412678601453073381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5049446940953661997797589 118346412678601453073381)
                ·
                  rfl

theorem cell22_3111464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 7].length) (baseStart_3111464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3111464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3111464 prefixEnd_3111464 := by exact prefixLift 3111464
  have htrace : WordTrace (prefixWord ++ tailWord_3111464) baseStart_3111464 baseEnd_3111464 := by
    simpa [prefixWord, tailWord_3111464, baseEnd_3111464] using wordTrace_append hprefix tailTrace_3111464
  have hstable : (prefixWord ++ tailWord_3111464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111464).length < 2 ^ (prefixWord ++ tailWord_3111464).sum := by decide
  have hdescent : baseEnd_3111464 < baseStart_3111464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111556 : List Nat := [2, 3, 2, 1, 3, 2, 1, 3, 1, 4]
def baseStart_3111556 : Nat := 118140960795 + 3111556 * 2 ^ 59
def prefixEnd_3111556 : Nat := 4983230072969 + 3 ^ 40 * 3111556 * 2
def baseEnd_3111556 : Nat := 1065149207587555504360147

theorem tailTrace_3111556 : CollatzResearch.WordTrace tailWord_3111556 prefixEnd_3111556 1065149207587555504360147 := by
  unfold tailWord_3111556
  simp only [CollatzResearch.WordTrace]
  refine ⟨56743885357685749151041261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75658513810247665534721681 56743885357685749151041261)
  ·
    refine ⟨21278957009132155931640473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56743885357685749151041261 21278957009132155931640473)
    ·
      refine ⟨15959217756849116948730355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21278957009132155931640473 15959217756849116948730355)
      ·
        refine ⟨23938826635273675423095533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15959217756849116948730355 23938826635273675423095533)
        ·
          refine ⟨8977059988227628283660825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23938826635273675423095533 8977059988227628283660825)
          ·
            refine ⟨6732794991170721212745619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8977059988227628283660825 6732794991170721212745619)
            ·
              refine ⟨10099192486756081819118429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6732794991170721212745619 10099192486756081819118429)
              ·
                refine ⟨3787197182533530682169411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10099192486756081819118429 3787197182533530682169411)
                ·
                  refine ⟨5680795773800296023254117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3787197182533530682169411 5680795773800296023254117)
                  ·
                    refine ⟨1065149207587555504360147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5680795773800296023254117 1065149207587555504360147)
                    ·
                      rfl

theorem cell22_3111556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_3111556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3111556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3111556 prefixEnd_3111556 := by exact prefixLift 3111556
  have htrace : WordTrace (prefixWord ++ tailWord_3111556) baseStart_3111556 baseEnd_3111556 := by
    simpa [prefixWord, tailWord_3111556, baseEnd_3111556] using wordTrace_append hprefix tailTrace_3111556
  have hstable : (prefixWord ++ tailWord_3111556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111556).length < 2 ^ (prefixWord ++ tailWord_3111556).sum := by decide
  have hdescent : baseEnd_3111556 < baseStart_3111556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111599 : List Nat := [1, 1, 2, 1, 2, 5, 4, 6]
def baseStart_3111599 : Nat := 118140960795 + 3111599 * 2 ^ 59
def prefixEnd_3111599 : Nat := 4983230072969 + 3 ^ 40 * 3111599 * 2
def baseEnd_3111599 : Nat := 118351547485146413948335

theorem tailTrace_3111599 : CollatzResearch.WordTrace tailWord_3111599 prefixEnd_3111599 118351547485146413948335 := by
  unfold tailWord_3111599
  simp only [CollatzResearch.WordTrace]
  refine ⟨113489339054215716645897851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75659559369477144430598567 113489339054215716645897851)
  ·
    refine ⟨170234008581323574968846777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113489339054215716645897851 170234008581323574968846777)
    ·
      refine ⟨127675506435992681226635083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170234008581323574968846777 127675506435992681226635083)
      ·
        refine ⟨191513259653989021839952625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127675506435992681226635083 191513259653989021839952625)
        ·
          refine ⟨143634944740491766379964469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191513259653989021839952625 143634944740491766379964469)
          ·
            refine ⟨13465776069421103098121669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 143634944740491766379964469 13465776069421103098121669)
            ·
              refine ⟨2524833013016456830897813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13465776069421103098121669 2524833013016456830897813)
              ·
                refine ⟨118351547485146413948335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2524833013016456830897813 118351547485146413948335)
                ·
                  rfl

theorem cell22_3111599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 6].length) (baseStart_3111599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3111599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3111599 prefixEnd_3111599 := by exact prefixLift 3111599
  have htrace : WordTrace (prefixWord ++ tailWord_3111599) baseStart_3111599 baseEnd_3111599 := by
    simpa [prefixWord, tailWord_3111599, baseEnd_3111599] using wordTrace_append hprefix tailTrace_3111599
  have hstable : (prefixWord ++ tailWord_3111599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111599).length < 2 ^ (prefixWord ++ tailWord_3111599).sum := by decide
  have hdescent : baseEnd_3111599 < baseStart_3111599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111622 : List Nat := [6, 1, 2, 1, 3, 1, 1, 1, 6]
def baseStart_3111622 : Nat := 118140960795 + 3111622 * 2 ^ 59
def prefixEnd_3111622 : Nat := 4983230072969 + 3 ^ 40 * 3111622 * 2
def baseEnd_3111622 : Nat := 355057266912117777403315

theorem tailTrace_3111622 : CollatzResearch.WordTrace tailWord_3111622 prefixEnd_3111622 355057266912117777403315 := by
  unfold tailWord_3111622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3546568060410387236687035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 75660118622088261049323413 3546568060410387236687035)
  ·
    refine ⟨5319852090615580855030553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3546568060410387236687035 5319852090615580855030553)
    ·
      refine ⟨3989889067961685641272915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5319852090615580855030553 3989889067961685641272915)
      ·
        refine ⟨5984833601942528461909373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3989889067961685641272915 5984833601942528461909373)
        ·
          refine ⟨2244312600728448173216015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5984833601942528461909373 2244312600728448173216015)
          ·
            refine ⟨3366468901092672259824023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2244312600728448173216015 3366468901092672259824023)
            ·
              refine ⟨5049703351639008389736035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3366468901092672259824023 5049703351639008389736035)
              ·
                refine ⟨7574555027458512584604053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5049703351639008389736035 7574555027458512584604053)
                ·
                  refine ⟨355057266912117777403315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7574555027458512584604053 355057266912117777403315)
                  ·
                    rfl

theorem cell22_3111622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_3111622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3111622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3111622 prefixEnd_3111622 := by exact prefixLift 3111622
  have htrace : WordTrace (prefixWord ++ tailWord_3111622) baseStart_3111622 baseEnd_3111622 := by
    simpa [prefixWord, tailWord_3111622, baseEnd_3111622] using wordTrace_append hprefix tailTrace_3111622
  have hstable : (prefixWord ++ tailWord_3111622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111622).length < 2 ^ (prefixWord ++ tailWord_3111622).sum := by decide
  have hdescent : baseEnd_3111622 < baseStart_3111622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111637 : List Nat := [1, 3, 2, 5, 1, 2, 2, 1, 2, 3]
def baseStart_3111637 : Nat := 118140960795 + 3111637 * 2 ^ 59
def prefixEnd_3111637 : Nat := 4983230072969 + 3 ^ 40 * 3111637 * 2
def baseEnd_3111637 : Nat := 1065176935542898293084899

theorem tailTrace_3111637 : CollatzResearch.WordTrace tailWord_3111637 prefixEnd_3111637 1065176935542898293084899 := by
  unfold tailWord_3111637
  simp only [CollatzResearch.WordTrace]
  refine ⟨113490725028078049135781165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75660483352052032757187443 113490725028078049135781165)
  ·
    refine ⟨42559021885529268425917937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113490725028078049135781165 42559021885529268425917937)
    ·
      refine ⟨31919266414146951319438453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42559021885529268425917937 31919266414146951319438453)
      ·
        refine ⟨2992431226326276686197355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31919266414146951319438453 2992431226326276686197355)
        ·
          refine ⟨4488646839489415029296033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2992431226326276686197355 4488646839489415029296033)
          ·
            refine ⟨3366485129617061271972025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4488646839489415029296033 3366485129617061271972025)
            ·
              refine ⟨2524863847212795953979019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3366485129617061271972025 2524863847212795953979019)
              ·
                refine ⟨3787295770819193930968529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2524863847212795953979019 3787295770819193930968529)
                ·
                  refine ⟨2840471828114395448226397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3787295770819193930968529 2840471828114395448226397)
                  ·
                    refine ⟨1065176935542898293084899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2840471828114395448226397 1065176935542898293084899)
                    ·
                      rfl

theorem cell22_3111637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_3111637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3111637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3111637 prefixEnd_3111637 := by exact prefixLift 3111637
  have htrace : WordTrace (prefixWord ++ tailWord_3111637) baseStart_3111637 baseEnd_3111637 := by
    simpa [prefixWord, tailWord_3111637, baseEnd_3111637] using wordTrace_append hprefix tailTrace_3111637
  have hstable : (prefixWord ++ tailWord_3111637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111637).length < 2 ^ (prefixWord ++ tailWord_3111637).sum := by decide
  have hdescent : baseEnd_3111637 < baseStart_3111637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111678 : List Nat := [4, 2, 2, 1, 2, 2, 2, 2, 5]
def baseStart_3111678 : Nat := 118140960795 + 3111678 * 2 ^ 59
def prefixEnd_3111678 : Nat := 4983230072969 + 3 ^ 40 * 3111678 * 2
def baseEnd_3111678 : Nat := 355063656893595950936591

theorem tailTrace_3111678 : CollatzResearch.WordTrace tailWord_3111678 prefixEnd_3111678 355063656893595950936591 := by
  unfold tailWord_3111678
  simp only [CollatzResearch.WordTrace]
  refine ⟨14186527552616189142252961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75661480280619675425349125 14186527552616189142252961)
  ·
    refine ⟨10639895664462141856689721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14186527552616189142252961 10639895664462141856689721)
    ·
      refine ⟨7979921748346606392517291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10639895664462141856689721 7979921748346606392517291)
      ·
        refine ⟨11969882622519909588775937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7979921748346606392517291 11969882622519909588775937)
        ·
          refine ⟨8977411966889932191581953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11969882622519909588775937 8977411966889932191581953)
          ·
            refine ⟨6733058975167449143686465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8977411966889932191581953 6733058975167449143686465)
            ·
              refine ⟨5049794231375586857764849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6733058975167449143686465 5049794231375586857764849)
              ·
                refine ⟨3787345673531690143323637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5049794231375586857764849 3787345673531690143323637)
                ·
                  refine ⟨355063656893595950936591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3787345673531690143323637 355063656893595950936591)
                  ·
                    rfl

theorem cell22_3111678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_3111678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3111678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3111678 prefixEnd_3111678 := by exact prefixLift 3111678
  have htrace : WordTrace (prefixWord ++ tailWord_3111678) baseStart_3111678 baseEnd_3111678 := by
    simpa [prefixWord, tailWord_3111678, baseEnd_3111678] using wordTrace_append hprefix tailTrace_3111678
  have hstable : (prefixWord ++ tailWord_3111678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111678).length < 2 ^ (prefixWord ++ tailWord_3111678).sum := by decide
  have hdescent : baseEnd_3111678 < baseStart_3111678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111682 : List Nat := [3, 4, 1, 1, 1, 2, 4, 2, 1, 3]
def baseStart_3111682 : Nat := 118140960795 + 3111682 * 2 ^ 59
def prefixEnd_3111682 : Nat := 4983230072969 + 3 ^ 40 * 3111682 * 2
def baseEnd_3111682 : Nat := 1065192339962533175709761

theorem tailTrace_3111682 : CollatzResearch.WordTrace tailWord_3111682 prefixEnd_3111682 1065192339962533175709761 := by
  unfold tailWord_3111682
  simp only [CollatzResearch.WordTrace]
  refine ⟨28373091578228755455292325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75661577541943347880779533 28373091578228755455292325)
  ·
    refine ⟨5319954670917891647867311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28373091578228755455292325 5319954670917891647867311)
    ·
      refine ⟨7979932006376837471800967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5319954670917891647867311 7979932006376837471800967)
      ·
        refine ⟨11969898009565256207701451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7979932006376837471800967 11969898009565256207701451)
        ·
          refine ⟨17954847014347884311552177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11969898009565256207701451 17954847014347884311552177)
          ·
            refine ⟨13466135260760913233664133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17954847014347884311552177 13466135260760913233664133)
            ·
              refine ⟨2524900361392671231312025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13466135260760913233664133 2524900361392671231312025)
              ·
                refine ⟨1893675271044503423484019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2524900361392671231312025 1893675271044503423484019)
                ·
                  refine ⟨2840512906566755135226029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1893675271044503423484019 2840512906566755135226029)
                  ·
                    refine ⟨1065192339962533175709761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2840512906566755135226029 1065192339962533175709761)
                    ·
                      rfl

theorem cell22_3111682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_3111682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3111682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3111682 prefixEnd_3111682 := by exact prefixLift 3111682
  have htrace : WordTrace (prefixWord ++ tailWord_3111682) baseStart_3111682 baseEnd_3111682 := by
    simpa [prefixWord, tailWord_3111682, baseEnd_3111682] using wordTrace_append hprefix tailTrace_3111682
  have hstable : (prefixWord ++ tailWord_3111682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111682).length < 2 ^ (prefixWord ++ tailWord_3111682).sum := by decide
  have hdescent : baseEnd_3111682 < baseStart_3111682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111738 : List Nat := [3, 1, 1, 1, 6, 1, 1, 1, 4, 3]
def baseStart_3111738 : Nat := 118140960795 + 3111738 * 2 ^ 59
def prefixEnd_3111738 : Nat := 4983230072969 + 3 ^ 40 * 3111738 * 2
def baseEnd_3111738 : Nat := 1065211509906967696309589

theorem tailTrace_3111738 : CollatzResearch.WordTrace tailWord_3111738 prefixEnd_3111738 1065211509906967696309589 := by
  unfold tailWord_3111738
  simp only [CollatzResearch.WordTrace]
  refine ⟨28373602200178035846301967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75662939200474762256805245 28373602200178035846301967)
  ·
    refine ⟨42560403300267053769452951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28373602200178035846301967 42560403300267053769452951)
    ·
      refine ⟨63840604950400580654179427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42560403300267053769452951 63840604950400580654179427)
      ·
        refine ⟨95760907425600870981269141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63840604950400580654179427 95760907425600870981269141)
        ·
          refine ⟨4488792535575040827246991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 95760907425600870981269141 4488792535575040827246991)
          ·
            refine ⟨6733188803362561240870487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4488792535575040827246991 6733188803362561240870487)
            ·
              refine ⟨10099783205043841861305731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6733188803362561240870487 10099783205043841861305731)
              ·
                refine ⟨15149674807565762791958597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10099783205043841861305731 15149674807565762791958597)
                ·
                  refine ⟨2840564026418580523492237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15149674807565762791958597 2840564026418580523492237)
                  ·
                    refine ⟨1065211509906967696309589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2840564026418580523492237 1065211509906967696309589)
                    ·
                      rfl

theorem cell22_3111738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 4, 3].length) (baseStart_3111738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3111738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3111738 prefixEnd_3111738 := by exact prefixLift 3111738
  have htrace : WordTrace (prefixWord ++ tailWord_3111738) baseStart_3111738 baseEnd_3111738 := by
    simpa [prefixWord, tailWord_3111738, baseEnd_3111738] using wordTrace_append hprefix tailTrace_3111738
  have hstable : (prefixWord ++ tailWord_3111738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111738).length < 2 ^ (prefixWord ++ tailWord_3111738).sum := by decide
  have hdescent : baseEnd_3111738 < baseStart_3111738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111806 : List Nat := [4, 2, 3, 1, 3, 1, 2, 1, 2, 3]
def baseStart_3111806 : Nat := 118140960795 + 3111806 * 2 ^ 59
def prefixEnd_3111806 : Nat := 4983230072969 + 3 ^ 40 * 3111806 * 2
def baseEnd_3111806 : Nat := 1065234787696638185609381

theorem tailTrace_3111806 : CollatzResearch.WordTrace tailWord_3111806 prefixEnd_3111806 1065234787696638185609381 := by
  unfold tailWord_3111806
  simp only [CollatzResearch.WordTrace]
  refine ⟨14187111120558223874835409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75664592642977193999122181 14187111120558223874835409)
  ·
    refine ⟨10640333340418667906126557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14187111120558223874835409 10640333340418667906126557)
    ·
      refine ⟨3990125002657000464797459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10640333340418667906126557 3990125002657000464797459)
      ·
        refine ⟨5985187503985500697196189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3990125002657000464797459 5985187503985500697196189)
        ·
          refine ⟨2244445313994562761448571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5985187503985500697196189 2244445313994562761448571)
          ·
            refine ⟨3366667970991844142172857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2244445313994562761448571 3366667970991844142172857)
            ·
              refine ⟨2525000978243883106629643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3366667970991844142172857 2525000978243883106629643)
              ·
                refine ⟨3787501467365824659944465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2525000978243883106629643 3787501467365824659944465)
                ·
                  refine ⟨2840626100524368494958349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3787501467365824659944465 2840626100524368494958349)
                  ·
                    refine ⟨1065234787696638185609381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2840626100524368494958349 1065234787696638185609381)
                    ·
                      rfl

theorem cell22_3111806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_3111806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3111806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3111806 prefixEnd_3111806 := by exact prefixLift 3111806
  have htrace : WordTrace (prefixWord ++ tailWord_3111806) baseStart_3111806 baseEnd_3111806 := by
    simpa [prefixWord, tailWord_3111806, baseEnd_3111806] using wordTrace_append hprefix tailTrace_3111806
  have hstable : (prefixWord ++ tailWord_3111806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111806).length < 2 ^ (prefixWord ++ tailWord_3111806).sum := by decide
  have hdescent : baseEnd_3111806 < baseStart_3111806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111813 : List Nat := [1, 3, 1, 1, 3, 3, 4, 1, 5]
def baseStart_3111813 : Nat := 118140960795 + 3111813 * 2 ^ 59
def prefixEnd_3111813 : Nat := 4983230072969 + 3 ^ 40 * 3111813 * 2
def baseEnd_3111813 : Nat := 355079061313230833561453

theorem tailTrace_3111813 : CollatzResearch.WordTrace tailWord_3111813 prefixEnd_3111813 355079061313230833561453 := by
  unfold tailWord_3111813
  simp only [CollatzResearch.WordTrace]
  refine ⟨113497144275440431194188093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75664762850293620796125395 113497144275440431194188093)
  ·
    refine ⟨42561429103290161697820535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113497144275440431194188093 42561429103290161697820535)
    ·
      refine ⟨63842143654935242546730803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42561429103290161697820535 63842143654935242546730803)
      ·
        refine ⟨95763215482402863820096205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63842143654935242546730803 95763215482402863820096205)
        ·
          refine ⟨35911205805901073932536077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95763215482402863820096205 35911205805901073932536077)
          ·
            refine ⟨13466702177212902724701029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35911205805901073932536077 13466702177212902724701029)
            ·
              refine ⟨2525006658227419260881443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13466702177212902724701029 2525006658227419260881443)
              ·
                refine ⟨3787509987341128891322165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2525006658227419260881443 3787509987341128891322165)
                ·
                  refine ⟨355079061313230833561453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3787509987341128891322165 355079061313230833561453)
                  ·
                    rfl

theorem cell22_3111813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 5].length) (baseStart_3111813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3111813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3111813 prefixEnd_3111813 := by exact prefixLift 3111813
  have htrace : WordTrace (prefixWord ++ tailWord_3111813) baseStart_3111813 baseEnd_3111813 := by
    simpa [prefixWord, tailWord_3111813, baseEnd_3111813] using wordTrace_append hprefix tailTrace_3111813
  have hstable : (prefixWord ++ tailWord_3111813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111813).length < 2 ^ (prefixWord ++ tailWord_3111813).sum := by decide
  have hdescent : baseEnd_3111813 < baseStart_3111813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111860 : List Nat := [2, 5, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_3111860 : Nat := 118140960795 + 3111860 * 2 ^ 59
def prefixEnd_3111860 : Nat := 4983230072969 + 3 ^ 40 * 3111860 * 2
def baseEnd_3111860 : Nat := 1065253273000200044759215

theorem tailTrace_3111860 : CollatzResearch.WordTrace tailWord_3111860 prefixEnd_3111860 1065253273000200044759215 := by
  unfold tailWord_3111860
  simp only [CollatzResearch.WordTrace]
  refine ⟨56749429253135079110574517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75665905670846772147432689 56749429253135079110574517)
  ·
    refine ⟨5320258992481413666616361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56749429253135079110574517 5320258992481413666616361)
    ·
      refine ⟨3990194244361060249962271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5320258992481413666616361 3990194244361060249962271)
      ·
        refine ⟨5985291366541590374943407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3990194244361060249962271 5985291366541590374943407)
        ·
          refine ⟨8977937049812385562415111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5985291366541590374943407 8977937049812385562415111)
          ·
            refine ⟨13466905574718578343622667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8977937049812385562415111 13466905574718578343622667)
            ·
              refine ⟨20200358362077867515434001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13466905574718578343622667 20200358362077867515434001)
              ·
                refine ⟨15150268771558400636575501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20200358362077867515434001 15150268771558400636575501)
                ·
                  refine ⟨5681350789334400238715813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15150268771558400636575501 5681350789334400238715813)
                  ·
                    refine ⟨1065253273000200044759215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5681350789334400238715813 1065253273000200044759215)
                    ·
                      rfl

theorem cell22_3111860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_3111860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3111860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3111860 prefixEnd_3111860 := by exact prefixLift 3111860
  have htrace : WordTrace (prefixWord ++ tailWord_3111860) baseStart_3111860 baseEnd_3111860 := by
    simpa [prefixWord, tailWord_3111860, baseEnd_3111860] using wordTrace_append hprefix tailTrace_3111860
  have hstable : (prefixWord ++ tailWord_3111860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111860).length < 2 ^ (prefixWord ++ tailWord_3111860).sum := by decide
  have hdescent : baseEnd_3111860 < baseStart_3111860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111894 : List Nat := [5, 2, 1, 1, 2, 3, 2, 1, 1, 4]
def baseStart_3111894 : Nat := 118140960795 + 3111894 * 2 ^ 59
def prefixEnd_3111894 : Nat := 4983230072969 + 3 ^ 40 * 3111894 * 2
def baseEnd_3111894 : Nat := 1065264911895035289409111

theorem tailTrace_3111894 : CollatzResearch.WordTrace tailWord_3111894 prefixEnd_3111894 1065264911895035289409111 := by
  unfold tailWord_3111894
  simp only [CollatzResearch.WordTrace]
  refine ⟨7093756161759186376742921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75666732392097988018591157 7093756161759186376742921)
  ·
    refine ⟨5320317121319389782557191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7093756161759186376742921 5320317121319389782557191)
    ·
      refine ⟨7980475681979084673835787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5320317121319389782557191 7980475681979084673835787)
      ·
        refine ⟨11970713522968627010753681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7980475681979084673835787 11970713522968627010753681)
        ·
          refine ⟨8978035142226470258065261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11970713522968627010753681 8978035142226470258065261)
          ·
            refine ⟨3366763178334926346774473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8978035142226470258065261 3366763178334926346774473)
            ·
              refine ⟨2525072383751194760080855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3366763178334926346774473 2525072383751194760080855)
              ·
                refine ⟨3787608575626792140121283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2525072383751194760080855 3787608575626792140121283)
                ·
                  refine ⟨5681412863440188210181925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3787608575626792140121283 5681412863440188210181925)
                  ·
                    refine ⟨1065264911895035289409111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5681412863440188210181925 1065264911895035289409111)
                    ·
                      rfl

theorem cell22_3111894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_3111894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3111894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3111894 prefixEnd_3111894 := by exact prefixLift 3111894
  have htrace : WordTrace (prefixWord ++ tailWord_3111894) baseStart_3111894 baseEnd_3111894 := by
    simpa [prefixWord, tailWord_3111894, baseEnd_3111894] using wordTrace_append hprefix tailTrace_3111894
  have hstable : (prefixWord ++ tailWord_3111894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111894).length < 2 ^ (prefixWord ++ tailWord_3111894).sum := by decide
  have hdescent : baseEnd_3111894 < baseStart_3111894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111954 : List Nat := [3, 2, 5, 1, 2, 1, 8]
def baseStart_3111954 : Nat := 118140960795 + 3111954 * 2 ^ 59
def prefixEnd_3111954 : Nat := 4983230072969 + 3 ^ 40 * 3111954 * 2
def baseEnd_3111954 : Nat := 39455016708193153070701

theorem tailTrace_3111954 : CollatzResearch.WordTrace tailWord_3111954 prefixEnd_3111954 39455016708193153070701 := by
  unfold tailWord_3111954
  simp only [CollatzResearch.WordTrace]
  refine ⟨28375571741982403068767729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75668191311953074850047277 28375571741982403068767729)
  ·
    refine ⟨21281678806486802301575797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28375571741982403068767729 21281678806486802301575797)
    ·
      refine ⟨1995157388108137715772731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21281678806486802301575797 1995157388108137715772731)
      ·
        refine ⟨2992736082162206573659097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1995157388108137715772731 2992736082162206573659097)
        ·
          refine ⟨2244552061621654930244323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2992736082162206573659097 2244552061621654930244323)
          ·
            refine ⟨3366828092432482395366485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2244552061621654930244323 3366828092432482395366485)
            ·
              refine ⟨39455016708193153070701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3366828092432482395366485 39455016708193153070701)
              ·
                rfl

theorem cell22_3111954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 8].length) (baseStart_3111954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3111954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3111954 prefixEnd_3111954 := by exact prefixLift 3111954
  have htrace : WordTrace (prefixWord ++ tailWord_3111954) baseStart_3111954 baseEnd_3111954 := by
    simpa [prefixWord, tailWord_3111954, baseEnd_3111954] using wordTrace_append hprefix tailTrace_3111954
  have hstable : (prefixWord ++ tailWord_3111954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111954).length < 2 ^ (prefixWord ++ tailWord_3111954).sum := by decide
  have hdescent : baseEnd_3111954 < baseStart_3111954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111969 : List Nat := [1, 2, 3, 2, 3, 2, 3, 2, 1, 3]
def baseStart_3111969 : Nat := 118140960795 + 3111969 * 2 ^ 59
def prefixEnd_3111969 : Nat := 4983230072969 + 3 ^ 40 * 3111969 * 2
def baseEnd_3111969 : Nat := 1065290585927760093783881

theorem tailTrace_3111969 : CollatzResearch.WordTrace tailWord_3111969 prefixEnd_3111969 1065290585927760093783881 := by
  unfold tailWord_3111969
  simp only [CollatzResearch.WordTrace]
  refine ⟨113502834062875269836866961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75668556041916846557911307 113502834062875269836866961)
  ·
    refine ⟨85127125547156452377650221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113502834062875269836866961 85127125547156452377650221)
    ·
      refine ⟨31922672080183669641618833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85127125547156452377650221 31922672080183669641618833)
      ·
        refine ⟨23942004060137752231214125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31922672080183669641618833 23942004060137752231214125)
        ·
          refine ⟨8978251522551657086705297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23942004060137752231214125 8978251522551657086705297)
          ·
            refine ⟨6733688641913742815028973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8978251522551657086705297 6733688641913742815028973)
            ·
              refine ⟨2525133240717653555635865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6733688641913742815028973 2525133240717653555635865)
              ·
                refine ⟨1893849930538240166726899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2525133240717653555635865 1893849930538240166726899)
                ·
                  refine ⟨2840774895807360250090349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1893849930538240166726899 2840774895807360250090349)
                  ·
                    refine ⟨1065290585927760093783881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2840774895807360250090349 1065290585927760093783881)
                    ·
                      rfl

theorem cell22_3111969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_3111969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3111969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3111969 prefixEnd_3111969 := by exact prefixLift 3111969
  have htrace : WordTrace (prefixWord ++ tailWord_3111969) baseStart_3111969 baseEnd_3111969 := by
    simpa [prefixWord, tailWord_3111969, baseEnd_3111969] using wordTrace_append hprefix tailTrace_3111969
  have hstable : (prefixWord ++ tailWord_3111969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111969).length < 2 ^ (prefixWord ++ tailWord_3111969).sum := by decide
  have hdescent : baseEnd_3111969 < baseStart_3111969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112008 : List Nat := [2, 1, 3, 1, 1, 1, 5, 2, 1, 5]
def baseStart_3112008 : Nat := 118140960795 + 3112008 * 2 ^ 59
def prefixEnd_3112008 : Nat := 4983230072969 + 3 ^ 40 * 3112008 * 2
def baseEnd_3112008 : Nat := 1065303936424776992058761

theorem tailTrace_3112008 : CollatzResearch.WordTrace tailWord_3112008 prefixEnd_3112008 1065303936424776992058761 := by
  unfold tailWord_3112008
  simp only [CollatzResearch.WordTrace]
  refine ⟨56752128254866989748768339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75669504339822652998357785 56752128254866989748768339)
  ·
    refine ⟨85128192382300484623152509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56752128254866989748768339 85128192382300484623152509)
    ·
      refine ⟨31923072143362681733682191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85128192382300484623152509 31923072143362681733682191)
      ·
        refine ⟨47884608215044022600523287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31923072143362681733682191 47884608215044022600523287)
        ·
          refine ⟨71826912322566033900784931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47884608215044022600523287 71826912322566033900784931)
          ·
            refine ⟨107740368483849050851177397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71826912322566033900784931 107740368483849050851177397)
            ·
              refine ⟨10100659545360848517297881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107740368483849050851177397 10100659545360848517297881)
              ·
                refine ⟨7575494659020636387973411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10100659545360848517297881 7575494659020636387973411)
                ·
                  refine ⟨11363241988530954581960117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7575494659020636387973411 11363241988530954581960117)
                  ·
                    refine ⟨1065303936424776992058761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11363241988530954581960117 1065303936424776992058761)
                    ·
                      rfl

theorem cell22_3112008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_3112008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112008 prefixEnd_3112008 := by exact prefixLift 3112008
  have htrace : WordTrace (prefixWord ++ tailWord_3112008) baseStart_3112008 baseEnd_3112008 := by
    simpa [prefixWord, tailWord_3112008, baseEnd_3112008] using wordTrace_append hprefix tailTrace_3112008
  have hstable : (prefixWord ++ tailWord_3112008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112008).length < 2 ^ (prefixWord ++ tailWord_3112008).sum := by decide
  have hdescent : baseEnd_3112008 < baseStart_3112008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112042 : List Nat := [3, 1, 3, 2, 2, 1, 2, 3, 2, 3]
def baseStart_3112042 : Nat := 118140960795 + 3112042 * 2 ^ 59
def prefixEnd_3112042 : Nat := 4983230072969 + 3 ^ 40 * 3112042 * 2
def baseEnd_3112042 : Nat := 1065315575319612236708657

theorem tailTrace_3112042 : CollatzResearch.WordTrace tailWord_3112042 prefixEnd_3112042 1065315575319612236708657 := by
  unfold tailWord_3112042
  simp only [CollatzResearch.WordTrace]
  refine ⟨28376374147902700826068595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75670331061073868869516253 28376374147902700826068595)
  ·
    refine ⟨42564561221854051239102893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28376374147902700826068595 42564561221854051239102893)
    ·
      refine ⟨15961710458195269214663585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42564561221854051239102893 15961710458195269214663585)
      ·
        refine ⟨11971282843646451910997689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15961710458195269214663585 11971282843646451910997689)
        ·
          refine ⟨8978462132734838933248267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11971282843646451910997689 8978462132734838933248267)
          ·
            refine ⟨13467693199102258399872401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8978462132734838933248267 13467693199102258399872401)
            ·
              refine ⟨10100769899326693799904301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13467693199102258399872401 10100769899326693799904301)
              ·
                refine ⟨3787788712247510174964113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10100769899326693799904301 3787788712247510174964113)
                ·
                  refine ⟨2840841534185632631223085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3787788712247510174964113 2840841534185632631223085)
                  ·
                    refine ⟨1065315575319612236708657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2840841534185632631223085 1065315575319612236708657)
                    ·
                      rfl

theorem cell22_3112042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_3112042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112042 prefixEnd_3112042 := by exact prefixLift 3112042
  have htrace : WordTrace (prefixWord ++ tailWord_3112042) baseStart_3112042 baseEnd_3112042 := by
    simpa [prefixWord, tailWord_3112042, baseEnd_3112042] using wordTrace_append hprefix tailTrace_3112042
  have hstable : (prefixWord ++ tailWord_3112042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112042).length < 2 ^ (prefixWord ++ tailWord_3112042).sum := by decide
  have hdescent : baseEnd_3112042 < baseStart_3112042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112057 : List Nat := [1, 2, 1, 3, 5, 2, 1, 1, 2, 4]
def baseStart_3112057 : Nat := 118140960795 + 3112057 * 2 ^ 59
def prefixEnd_3112057 : Nat := 4983230072969 + 3 ^ 40 * 3112057 * 2
def baseEnd_3112057 : Nat := 1065320710126157197583611

theorem tailTrace_3112057 : CollatzResearch.WordTrace tailWord_3112057 prefixEnd_3112057 1065320710126157197583611 := by
  unfold tailWord_3112057
  simp only [CollatzResearch.WordTrace]
  refine ⟨113506043686556460866070425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75670695791037640577380283 113506043686556460866070425)
  ·
    refine ⟨85129532764917345649552819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113506043686556460866070425 85129532764917345649552819)
    ·
      refine ⟨127694299147376018474329229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85129532764917345649552819 127694299147376018474329229)
      ·
        refine ⟨47885362180266006927873461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127694299147376018474329229 47885362180266006927873461)
        ·
          refine ⟨4489252704399938149488137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47885362180266006927873461 4489252704399938149488137)
          ·
            refine ⟨3366939528299953612116103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4489252704399938149488137 3366939528299953612116103)
            ·
              refine ⟨5050409292449930418174155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3366939528299953612116103 5050409292449930418174155)
              ·
                refine ⟨7575613938674895627261233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5050409292449930418174155 7575613938674895627261233)
                ·
                  refine ⟨5681710454006171720445925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7575613938674895627261233 5681710454006171720445925)
                  ·
                    refine ⟨1065320710126157197583611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5681710454006171720445925 1065320710126157197583611)
                    ·
                      rfl

theorem cell22_3112057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 4].length) (baseStart_3112057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112057 prefixEnd_3112057 := by exact prefixLift 3112057
  have htrace : WordTrace (prefixWord ++ tailWord_3112057) baseStart_3112057 baseEnd_3112057 := by
    simpa [prefixWord, tailWord_3112057, baseEnd_3112057] using wordTrace_append hprefix tailTrace_3112057
  have hstable : (prefixWord ++ tailWord_3112057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112057).length < 2 ^ (prefixWord ++ tailWord_3112057).sum := by decide
  have hdescent : baseEnd_3112057 < baseStart_3112057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112087 : List Nat := [1, 1, 3, 3, 3, 2, 2, 1, 3, 3]
def baseStart_3112087 : Nat := 118140960795 + 3112087 * 2 ^ 59
def prefixEnd_3112087 : Nat := 4983230072969 + 3 ^ 40 * 3112087 * 2
def baseEnd_3112087 : Nat := 1065330979739247119333519

theorem tailTrace_3112087 : CollatzResearch.WordTrace tailWord_3112087 prefixEnd_3112087 1065330979739247119333519 := by
  unfold tailWord_3112087
  simp only [CollatzResearch.WordTrace]
  refine ⟨113507137876447775989662515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75671425250965183993108343 113507137876447775989662515)
  ·
    refine ⟨170260706814671663984493773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113507137876447775989662515 170260706814671663984493773)
    ·
      refine ⟨63847765055501873994185165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170260706814671663984493773 63847765055501873994185165)
      ·
        refine ⟨23942911895813202747819437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63847765055501873994185165 23942911895813202747819437)
        ·
          refine ⟨8978591960929951030432289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23942911895813202747819437 8978591960929951030432289)
          ·
            refine ⟨6733943970697463272824217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8978591960929951030432289 6733943970697463272824217)
            ·
              refine ⟨5050457978023097454618163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6733943970697463272824217 5050457978023097454618163)
              ·
                refine ⟨7575686967034646181927245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5050457978023097454618163 7575686967034646181927245)
                ·
                  refine ⟨2840882612637992318222717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7575686967034646181927245 2840882612637992318222717)
                  ·
                    refine ⟨1065330979739247119333519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2840882612637992318222717 1065330979739247119333519)
                    ·
                      rfl

theorem cell22_3112087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3, 3].length) (baseStart_3112087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112087 prefixEnd_3112087 := by exact prefixLift 3112087
  have htrace : WordTrace (prefixWord ++ tailWord_3112087) baseStart_3112087 baseEnd_3112087 := by
    simpa [prefixWord, tailWord_3112087, baseEnd_3112087] using wordTrace_append hprefix tailTrace_3112087
  have hstable : (prefixWord ++ tailWord_3112087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112087).length < 2 ^ (prefixWord ++ tailWord_3112087).sum := by decide
  have hdescent : baseEnd_3112087 < baseStart_3112087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112143 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 5, 5]
def baseStart_3112143 : Nat := 118140960795 + 3112143 * 2 ^ 59
def prefixEnd_3112143 : Nat := 4983230072969 + 3 ^ 40 * 3112143 * 2
def baseEnd_3112143 : Nat := 1065350149683681639933347

theorem tailTrace_3112143 : CollatzResearch.WordTrace tailWord_3112143 prefixEnd_3112143 1065350149683681639933347 := by
  unfold tailWord_3112143
  simp only [CollatzResearch.WordTrace]
  refine ⟨113509180364244897553701083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75672786909496598369134055 113509180364244897553701083)
  ·
    refine ⟨170263770546367346330551625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113509180364244897553701083 170263770546367346330551625)
    ·
      refine ⟨127697827909775509747913719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170263770546367346330551625 127697827909775509747913719)
      ·
        refine ⟨191546741864663264621870579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127697827909775509747913719 191546741864663264621870579)
        ·
          refine ⟨287320112796994896932805869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191546741864663264621870579 287320112796994896932805869)
          ·
            refine ⟨107745042298873086349802201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 287320112796994896932805869 107745042298873086349802201)
            ·
              refine ⟨80808781724154814762351651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107745042298873086349802201 80808781724154814762351651)
              ·
                refine ⟨121213172586232222143527477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80808781724154814762351651 121213172586232222143527477)
                ·
                  refine ⟨11363734929959270825955701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 121213172586232222143527477 11363734929959270825955701)
                  ·
                    refine ⟨1065350149683681639933347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11363734929959270825955701 1065350149683681639933347)
                    ·
                      rfl

theorem cell22_3112143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 5].length) (baseStart_3112143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112143 prefixEnd_3112143 := by exact prefixLift 3112143
  have htrace : WordTrace (prefixWord ++ tailWord_3112143) baseStart_3112143 baseEnd_3112143 := by
    simpa [prefixWord, tailWord_3112143, baseEnd_3112143] using wordTrace_append hprefix tailTrace_3112143
  have hstable : (prefixWord ++ tailWord_3112143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112143).length < 2 ^ (prefixWord ++ tailWord_3112143).sum := by decide
  have hdescent : baseEnd_3112143 < baseStart_3112143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112190 : List Nat := [4, 2, 2, 1, 1, 12]
def baseStart_3112190 : Nat := 118140960795 + 3112190 * 2 ^ 59
def prefixEnd_3112190 : Nat := 4983230072969 + 3 ^ 40 * 3112190 * 2
def baseEnd_3112190 : Nat := 13152669614125792395163

theorem tailTrace_3112190 : CollatzResearch.WordTrace tailWord_3112190 prefixEnd_3112190 13152669614125792395163 := by
  unfold tailWord_3112190
  simp only [CollatzResearch.WordTrace]
  refine ⟨14188861824384328072582753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75673929730049749720441349 14188861824384328072582753)
  ·
    refine ⟨10641646368288246054437065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14188861824384328072582753 10641646368288246054437065)
    ·
      refine ⟨7981234776216184540827799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10641646368288246054437065 7981234776216184540827799)
      ·
        refine ⟨11971852164324276811241699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7981234776216184540827799 11971852164324276811241699)
        ·
          refine ⟨17957778246486415216862549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11971852164324276811241699 17957778246486415216862549)
          ·
            refine ⟨13152669614125792395163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 17957778246486415216862549 13152669614125792395163)
            ·
              rfl

theorem cell22_3112190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 12].length) (baseStart_3112190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112190 prefixEnd_3112190 := by exact prefixLift 3112190
  have htrace : WordTrace (prefixWord ++ tailWord_3112190) baseStart_3112190 baseEnd_3112190 := by
    simpa [prefixWord, tailWord_3112190, baseEnd_3112190] using wordTrace_append hprefix tailTrace_3112190
  have hstable : (prefixWord ++ tailWord_3112190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112190).length < 2 ^ (prefixWord ++ tailWord_3112190).sum := by decide
  have hdescent : baseEnd_3112190 < baseStart_3112190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112196 : List Nat := [2, 3, 2, 2, 2, 3, 2, 2, 4]
def baseStart_3112196 : Nat := 118140960795 + 3112196 * 2 ^ 59
def prefixEnd_3112196 : Nat := 4983230072969 + 3 ^ 40 * 3112196 * 2
def baseEnd_3112196 : Nat := 355122764222269056119395

theorem tailTrace_3112196 : CollatzResearch.WordTrace tailWord_3112196 prefixEnd_3112196 355122764222269056119395 := by
  unfold tailWord_3112196
  simp only [CollatzResearch.WordTrace]
  refine ⟨56755556716526443802690221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75674075622035258403586961 56755556716526443802690221)
  ·
    refine ⟨21283333768697416426008833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56755556716526443802690221 21283333768697416426008833)
    ·
      refine ⟨15962500326523062319506625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21283333768697416426008833 15962500326523062319506625)
      ·
        refine ⟨11971875244892296739629969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15962500326523062319506625 11971875244892296739629969)
        ·
          refine ⟨8978906433669222554722477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11971875244892296739629969 8978906433669222554722477)
          ·
            refine ⟨3367089912625958458020929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8978906433669222554722477 3367089912625958458020929)
            ·
              refine ⟨2525317434469468843515697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3367089912625958458020929 2525317434469468843515697)
              ·
                refine ⟨1893988075852101632636773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2525317434469468843515697 1893988075852101632636773)
                ·
                  refine ⟨355122764222269056119395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1893988075852101632636773 355122764222269056119395)
                  ·
                    rfl

theorem cell22_3112196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_3112196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112196 prefixEnd_3112196 := by exact prefixLift 3112196
  have htrace : WordTrace (prefixWord ++ tailWord_3112196) baseStart_3112196 baseEnd_3112196 := by
    simpa [prefixWord, tailWord_3112196, baseEnd_3112196] using wordTrace_append hprefix tailTrace_3112196
  have hstable : (prefixWord ++ tailWord_3112196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112196).length < 2 ^ (prefixWord ++ tailWord_3112196).sum := by decide
  have hdescent : baseEnd_3112196 < baseStart_3112196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112226 : List Nat := [3, 3, 1, 1, 5, 1, 1, 1, 2, 4]
def baseStart_3112226 : Nat := 118140960795 + 3112226 * 2 ^ 59
def prefixEnd_3112226 : Nat := 4983230072969 + 3 ^ 40 * 3112226 * 2
def baseEnd_3112226 : Nat := 1065378562279897090108093

theorem tailTrace_3112226 : CollatzResearch.WordTrace tailWord_3112226 prefixEnd_3112226 1065378562279897090108093 := by
  unfold tailWord_3112226
  simp only [CollatzResearch.WordTrace]
  refine ⟨28378051905736050682243133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75674805081962801819315021 28378051905736050682243133)
  ·
    refine ⟨10641769464651019005841175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28378051905736050682243133 10641769464651019005841175)
    ·
      refine ⟨15962654196976528508761763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10641769464651019005841175 15962654196976528508761763)
      ·
        refine ⟨23943981295464792763142645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15962654196976528508761763 23943981295464792763142645)
        ·
          refine ⟨2244748246449824321544623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23943981295464792763142645 2244748246449824321544623)
          ·
            refine ⟨3367122369674736482316935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2244748246449824321544623 3367122369674736482316935)
            ·
              refine ⟨5050683554512104723475403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3367122369674736482316935 5050683554512104723475403)
              ·
                refine ⟨7576025331768157085213105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5050683554512104723475403 7576025331768157085213105)
                ·
                  refine ⟨5682018998826117813909829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7576025331768157085213105 5682018998826117813909829)
                  ·
                    refine ⟨1065378562279897090108093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5682018998826117813909829 1065378562279897090108093)
                    ·
                      rfl

theorem cell22_3112226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_3112226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112226 prefixEnd_3112226 := by exact prefixLift 3112226
  have htrace : WordTrace (prefixWord ++ tailWord_3112226) baseStart_3112226 baseEnd_3112226 := by
    simpa [prefixWord, tailWord_3112226, baseEnd_3112226] using wordTrace_append hprefix tailTrace_3112226
  have hstable : (prefixWord ++ tailWord_3112226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112226).length < 2 ^ (prefixWord ++ tailWord_3112226).sum := by decide
  have hdescent : baseEnd_3112226 < baseStart_3112226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112250 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 4, 5]
def baseStart_3112250 : Nat := 118140960795 + 3112250 * 2 ^ 59
def prefixEnd_3112250 : Nat := 4983230072969 + 3 ^ 40 * 3112250 * 2
def baseEnd_3112250 : Nat := 1065386777970369027508019

theorem tailTrace_3112250 : CollatzResearch.WordTrace tailWord_3112250 prefixEnd_3112250 1065386777970369027508019 := by
  unfold tailWord_3112250
  simp only [CollatzResearch.WordTrace]
  refine ⟨28378270743714313706961551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75675388649904836551897469 28378270743714313706961551)
  ·
    refine ⟨42567406115571470560442327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28378270743714313706961551 42567406115571470560442327)
    ·
      refine ⟨63851109173357205840663491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42567406115571470560442327 63851109173357205840663491)
      ·
        refine ⟨95776663760035808760995237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63851109173357205840663491 95776663760035808760995237)
        ·
          refine ⟨17958124455006714142686607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95776663760035808760995237 17958124455006714142686607)
          ·
            refine ⟨26937186682510071214029911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17958124455006714142686607 26937186682510071214029911)
            ·
              refine ⟨40405780023765106821044867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26937186682510071214029911 40405780023765106821044867)
              ·
                refine ⟨60608670035647660231567301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40405780023765106821044867 60608670035647660231567301)
                ·
                  refine ⟨11364125631683936293418869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60608670035647660231567301 11364125631683936293418869)
                  ·
                    refine ⟨1065386777970369027508019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11364125631683936293418869 1065386777970369027508019)
                    ·
                      rfl

theorem cell22_3112250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_3112250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112250 prefixEnd_3112250 := by exact prefixLift 3112250
  have htrace : WordTrace (prefixWord ++ tailWord_3112250) baseStart_3112250 baseEnd_3112250 := by
    simpa [prefixWord, tailWord_3112250, baseEnd_3112250] using wordTrace_append hprefix tailTrace_3112250
  have hstable : (prefixWord ++ tailWord_3112250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112250).length < 2 ^ (prefixWord ++ tailWord_3112250).sum := by decide
  have hdescent : baseEnd_3112250 < baseStart_3112250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112252 : List Nat := [2, 2, 2, 2, 1, 3, 3, 2, 5]
def baseStart_3112252 : Nat := 118140960795 + 3112252 * 2 ^ 59
def prefixEnd_3112252 : Nat := 4983230072969 + 3 ^ 40 * 3112252 * 2
def baseEnd_3112252 : Nat := 355129154203747229652671

theorem tailTrace_3112252 : CollatzResearch.WordTrace tailWord_3112252 prefixEnd_3112252 355129154203747229652671 := by
  unfold tailWord_3112252
  simp only [CollatzResearch.WordTrace]
  refine ⟨56756577960425004584709505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75675437280566672779612673 56756577960425004584709505)
  ·
    refine ⟨42567433470318753438532129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56756577960425004584709505 42567433470318753438532129)
    ·
      refine ⟨31925575102739065078899097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42567433470318753438532129 31925575102739065078899097)
      ·
        refine ⟨23944181327054298809174323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31925575102739065078899097 23944181327054298809174323)
        ·
          refine ⟨35916271990581448213761485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23944181327054298809174323 35916271990581448213761485)
          ·
            refine ⟨13468601996468043080160557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35916271990581448213761485 13468601996468043080160557)
            ·
              refine ⟨5050725748675516155060209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13468601996468043080160557 5050725748675516155060209)
              ·
                refine ⟨3788044311506637116295157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5050725748675516155060209 3788044311506637116295157)
                ·
                  refine ⟨355129154203747229652671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3788044311506637116295157 355129154203747229652671)
                  ·
                    rfl

theorem cell22_3112252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 5].length) (baseStart_3112252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112252 prefixEnd_3112252 := by exact prefixLift 3112252
  have htrace : WordTrace (prefixWord ++ tailWord_3112252) baseStart_3112252 baseEnd_3112252 := by
    simpa [prefixWord, tailWord_3112252, baseEnd_3112252] using wordTrace_append hprefix tailTrace_3112252
  have hstable : (prefixWord ++ tailWord_3112252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112252).length < 2 ^ (prefixWord ++ tailWord_3112252).sum := by decide
  have hdescent : baseEnd_3112252 < baseStart_3112252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112265 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 5, 4]
def baseStart_3112265 : Nat := 118140960795 + 3112265 * 2 ^ 59
def prefixEnd_3112265 : Nat := 4983230072969 + 3 ^ 40 * 3112265 * 2
def baseEnd_3112265 : Nat := 1065391912776913988382973

theorem tailTrace_3112265 : CollatzResearch.WordTrace tailWord_3112265 prefixEnd_3112265 1065391912776913988382973 := by
  unfold tailWord_3112265
  simp only [CollatzResearch.WordTrace]
  refine ⟨113513630069802912389642249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75675753379868608259761499 113513630069802912389642249)
  ·
    refine ⟨85135222552352184292231687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113513630069802912389642249 85135222552352184292231687)
    ·
      refine ⟨127702833828528276438347531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85135222552352184292231687 127702833828528276438347531)
      ·
        refine ⟨191554250742792414657521297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127702833828528276438347531 191554250742792414657521297)
        ·
          refine ⟨143665688057094310993140973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191554250742792414657521297 143665688057094310993140973)
          ·
            refine ⟨53874633021410366622427865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143665688057094310993140973 53874633021410366622427865)
            ·
              refine ⟨40405974766057774966820899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53874633021410366622427865 40405974766057774966820899)
              ·
                refine ⟨60608962149086662450231349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40405974766057774966820899 60608962149086662450231349)
                ·
                  refine ⟨5682090201476874604709189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60608962149086662450231349 5682090201476874604709189)
                  ·
                    refine ⟨1065391912776913988382973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5682090201476874604709189 1065391912776913988382973)
                    ·
                      rfl

theorem cell22_3112265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 4].length) (baseStart_3112265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112265 prefixEnd_3112265 := by exact prefixLift 3112265
  have htrace : WordTrace (prefixWord ++ tailWord_3112265) baseStart_3112265 baseEnd_3112265 := by
    simpa [prefixWord, tailWord_3112265, baseEnd_3112265] using wordTrace_append hprefix tailTrace_3112265
  have hstable : (prefixWord ++ tailWord_3112265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112265).length < 2 ^ (prefixWord ++ tailWord_3112265).sum := by decide
  have hdescent : baseEnd_3112265 < baseStart_3112265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112280 : List Nat := [2, 1, 2, 2, 1, 1, 3, 4, 6]
def baseStart_3112280 : Nat := 118140960795 + 3112280 * 2 ^ 59
def prefixEnd_3112280 : Nat := 4983230072969 + 3 ^ 40 * 3112280 * 2
def baseEnd_3112280 : Nat := 355132349194486316419309

theorem tailTrace_3112280 : CollatzResearch.WordTrace tailWord_3112280 prefixEnd_3112280 355132349194486316419309 := by
  unfold tailWord_3112280
  simp only [CollatzResearch.WordTrace]
  refine ⟨56757088582374284975719147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75676118109832379967625529 56757088582374284975719147)
  ·
    refine ⟨85135632873561427463578721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56757088582374284975719147 85135632873561427463578721)
    ·
      refine ⟨63851724655171070597684041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85135632873561427463578721 63851724655171070597684041)
      ·
        refine ⟨47888793491378302948263031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63851724655171070597684041 47888793491378302948263031)
        ·
          refine ⟨71833190237067454422394547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47888793491378302948263031 71833190237067454422394547)
          ·
            refine ⟨107749785355601181633591821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71833190237067454422394547 107749785355601181633591821)
            ·
              refine ⟨40406169508350443112596933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107749785355601181633591821 40406169508350443112596933)
              ·
                refine ⟨7576156782815708083611925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40406169508350443112596933 7576156782815708083611925)
                ·
                  refine ⟨355132349194486316419309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7576156782815708083611925 355132349194486316419309)
                  ·
                    rfl

theorem cell22_3112280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 6].length) (baseStart_3112280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112280 prefixEnd_3112280 := by exact prefixLift 3112280
  have htrace : WordTrace (prefixWord ++ tailWord_3112280) baseStart_3112280 baseEnd_3112280 := by
    simpa [prefixWord, tailWord_3112280, baseEnd_3112280] using wordTrace_append hprefix tailTrace_3112280
  have hstable : (prefixWord ++ tailWord_3112280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112280).length < 2 ^ (prefixWord ++ tailWord_3112280).sum := by decide
  have hdescent : baseEnd_3112280 < baseStart_3112280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112282 : List Nat := [3, 1, 1, 2, 1, 2, 3, 4, 1, 4]
def baseStart_3112282 : Nat := 118140960795 + 3112282 * 2 ^ 59
def prefixEnd_3112282 : Nat := 4983230072969 + 3 ^ 40 * 3112282 * 2
def baseEnd_3112282 : Nat := 1065397732224331610707921

theorem tailTrace_3112282 : CollatzResearch.WordTrace tailWord_3112282 prefixEnd_3112282 1065397732224331610707921 := by
  unfold tailWord_3112282
  simp only [CollatzResearch.WordTrace]
  refine ⟨28378562527685331073252775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75676166740494216195340733 28378562527685331073252775)
  ·
    refine ⟨42567843791527996609879163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28378562527685331073252775 42567843791527996609879163)
    ·
      refine ⟨63851765687291994914818745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42567843791527996609879163 63851765687291994914818745)
      ·
        refine ⟨47888824265468996186114059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63851765687291994914818745 47888824265468996186114059)
        ·
          refine ⟨71833236398203494279171089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47888824265468996186114059 71833236398203494279171089)
          ·
            refine ⟨53874927298652620709378317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71833236398203494279171089 53874927298652620709378317)
            ·
              refine ⟨20203097736994732766016869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53874927298652620709378317 20203097736994732766016869)
              ·
                refine ⟨3788080825686512393628163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20203097736994732766016869 3788080825686512393628163)
                ·
                  refine ⟨5682121238529768590442245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3788080825686512393628163 5682121238529768590442245)
                  ·
                    refine ⟨1065397732224331610707921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5682121238529768590442245 1065397732224331610707921)
                    ·
                      rfl

theorem cell22_3112282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_3112282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112282 prefixEnd_3112282 := by exact prefixLift 3112282
  have htrace : WordTrace (prefixWord ++ tailWord_3112282) baseStart_3112282 baseEnd_3112282 := by
    simpa [prefixWord, tailWord_3112282, baseEnd_3112282] using wordTrace_append hprefix tailTrace_3112282
  have hstable : (prefixWord ++ tailWord_3112282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112282).length < 2 ^ (prefixWord ++ tailWord_3112282).sum := by decide
  have hdescent : baseEnd_3112282 < baseStart_3112282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112297 : List Nat := [1, 2, 1, 1, 1, 3, 2, 7, 4]
def baseStart_3112297 : Nat := 118140960795 + 3112297 * 2 ^ 59
def prefixEnd_3112297 : Nat := 4983230072969 + 3 ^ 40 * 3112297 * 2
def baseEnd_3112297 : Nat := 355134289010292190527625

theorem tailTrace_3112297 : CollatzResearch.WordTrace tailWord_3112297 prefixEnd_3112297 355134289010292190527625 := by
  unfold tailWord_3112297
  simp only [CollatzResearch.WordTrace]
  refine ⟨113514797205686981854807145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75676531470457987903204763 113514797205686981854807145)
  ·
    refine ⟨85136097904265236391105359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113514797205686981854807145 85136097904265236391105359)
    ·
      refine ⟨127704146856397854586658039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85136097904265236391105359 127704146856397854586658039)
      ·
        refine ⟨191556220284596781879987059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127704146856397854586658039 191556220284596781879987059)
        ·
          refine ⟨287334330426895172819980589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191556220284596781879987059 287334330426895172819980589)
          ·
            refine ⟨107750373910085689807492721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 287334330426895172819980589 107750373910085689807492721)
            ·
              refine ⟨80812780432564267355619541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107750373910085689807492721 80812780432564267355619541)
              ·
                refine ⟨1894049541388225016147333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 80812780432564267355619541 1894049541388225016147333)
                ·
                  refine ⟨355134289010292190527625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1894049541388225016147333 355134289010292190527625)
                  ·
                    rfl

theorem cell22_3112297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 7, 4].length) (baseStart_3112297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112297 prefixEnd_3112297 := by exact prefixLift 3112297
  have htrace : WordTrace (prefixWord ++ tailWord_3112297) baseStart_3112297 baseEnd_3112297 := by
    simpa [prefixWord, tailWord_3112297, baseEnd_3112297] using wordTrace_append hprefix tailTrace_3112297
  have hstable : (prefixWord ++ tailWord_3112297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112297).length < 2 ^ (prefixWord ++ tailWord_3112297).sum := by decide
  have hdescent : baseEnd_3112297 < baseStart_3112297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112325 : List Nat := [1, 3, 1, 1, 3, 1, 3, 9]
def baseStart_3112325 : Nat := 118140960795 + 3112325 * 2 ^ 59
def prefixEnd_3112325 : Nat := 4983230072969 + 3 ^ 40 * 3112325 * 2
def baseEnd_3112325 : Nat := 118379161333677092431421

theorem tailTrace_3112325 : CollatzResearch.WordTrace tailWord_3112325 prefixEnd_3112325 118379161333677092431421 := by
  unfold tailWord_3112325
  simp only [CollatzResearch.WordTrace]
  refine ⟨113515818449585542636826429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75677212299723695091217619 113515818449585542636826429)
  ·
    refine ⟨42568431918594578488809911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113515818449585542636826429 42568431918594578488809911)
    ·
      refine ⟨63852647877891867733214867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42568431918594578488809911 63852647877891867733214867)
      ·
        refine ⟨95778971816837801599822301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63852647877891867733214867 95778971816837801599822301)
        ·
          refine ⟨35917114431314175599933363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95778971816837801599822301 35917114431314175599933363)
          ·
            refine ⟨53875671646971263399900045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35917114431314175599933363 53875671646971263399900045)
            ·
              refine ⟨20203376867614223774962517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53875671646971263399900045 20203376867614223774962517)
              ·
                refine ⟨118379161333677092431421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20203376867614223774962517 118379161333677092431421)
                ·
                  rfl

theorem cell22_3112325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 9].length) (baseStart_3112325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112325 prefixEnd_3112325 := by exact prefixLift 3112325
  have htrace : WordTrace (prefixWord ++ tailWord_3112325) baseStart_3112325 baseEnd_3112325 := by
    simpa [prefixWord, tailWord_3112325, baseEnd_3112325] using wordTrace_append hprefix tailTrace_3112325
  have hstable : (prefixWord ++ tailWord_3112325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112325).length < 2 ^ (prefixWord ++ tailWord_3112325).sum := by decide
  have hdescent : baseEnd_3112325 < baseStart_3112325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112357 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 7, 3]
def baseStart_3112357 : Nat := 118140960795 + 3112357 * 2 ^ 59
def prefixEnd_3112357 : Nat := 4983230072969 + 3 ^ 40 * 3112357 * 2
def baseEnd_3112357 : Nat := 1065423406257056415082691

theorem tailTrace_3112357 : CollatzResearch.WordTrace tailWord_3112357 prefixEnd_3112357 1065423406257056415082691 := by
  unfold tailWord_3112357
  simp only [CollatzResearch.WordTrace]
  refine ⟨113516985585469612101991325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75677990390313074734660883 113516985585469612101991325)
  ·
    refine ⟨42568869594551104538246747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113516985585469612101991325 42568869594551104538246747)
    ·
      refine ⟨63853304391826656807370121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42568869594551104538246747 63853304391826656807370121)
      ·
        refine ⟨47889978293869992605527591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63853304391826656807370121 47889978293869992605527591)
        ·
          refine ⟨71834967440804988908291387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47889978293869992605527591 71834967440804988908291387)
          ·
            refine ⟨107752451161207483362437081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71834967440804988908291387 107752451161207483362437081)
            ·
              refine ⟨80814338370905612521827811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107752451161207483362437081 80814338370905612521827811)
              ·
                refine ⟨121221507556358418782741717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80814338370905612521827811 121221507556358418782741717)
                ·
                  refine ⟨2841129083352150440220509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 121221507556358418782741717 2841129083352150440220509)
                  ·
                    refine ⟨1065423406257056415082691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2841129083352150440220509 1065423406257056415082691)
                    ·
                      rfl

theorem cell22_3112357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 7, 3].length) (baseStart_3112357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112357 prefixEnd_3112357 := by exact prefixLift 3112357
  have htrace : WordTrace (prefixWord ++ tailWord_3112357) baseStart_3112357 baseEnd_3112357 := by
    simpa [prefixWord, tailWord_3112357, baseEnd_3112357] using wordTrace_append hprefix tailTrace_3112357
  have hstable : (prefixWord ++ tailWord_3112357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112357).length < 2 ^ (prefixWord ++ tailWord_3112357).sum := by decide
  have hdescent : baseEnd_3112357 < baseStart_3112357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112387 : List Nat := [1, 1, 1, 3, 1, 1, 6, 3, 5]
def baseStart_3112387 : Nat := 118140960795 + 3112387 * 2 ^ 59
def prefixEnd_3112387 : Nat := 4983230072969 + 3 ^ 40 * 3112387 * 2
def baseEnd_3112387 : Nat := 355144558623382112277533

theorem tailTrace_3112387 : CollatzResearch.WordTrace tailWord_3112387 prefixEnd_3112387 355144558623382112277533 := by
  unfold tailWord_3112387
  simp only [CollatzResearch.WordTrace]
  refine ⟨113518079775360927225583415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75678719850240618150388943 113518079775360927225583415)
  ·
    refine ⟨170277119663041390838375123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113518079775360927225583415 170277119663041390838375123)
    ·
      refine ⟨255415679494562086257562685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170277119663041390838375123 255415679494562086257562685)
      ·
        refine ⟨95780879810460782346586007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255415679494562086257562685 95780879810460782346586007)
        ·
          refine ⟨143671319715691173519879011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95780879810460782346586007 143671319715691173519879011)
          ·
            refine ⟨215506979573536760279818517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143671319715691173519879011 215506979573536760279818517)
            ·
              refine ⟨10101889667509535638116493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 215506979573536760279818517 10101889667509535638116493)
              ·
                refine ⟨3788208625316075864293685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10101889667509535638116493 3788208625316075864293685)
                ·
                  refine ⟨355144558623382112277533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3788208625316075864293685 355144558623382112277533)
                  ·
                    rfl

theorem cell22_3112387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 5].length) (baseStart_3112387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112387 prefixEnd_3112387 := by exact prefixLift 3112387
  have htrace : WordTrace (prefixWord ++ tailWord_3112387) baseStart_3112387 baseEnd_3112387 := by
    simpa [prefixWord, tailWord_3112387, baseEnd_3112387] using wordTrace_append hprefix tailTrace_3112387
  have hstable : (prefixWord ++ tailWord_3112387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112387).length < 2 ^ (prefixWord ++ tailWord_3112387).sum := by decide
  have hdescent : baseEnd_3112387 < baseStart_3112387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112421 : List Nat := [1, 3, 1, 5, 1, 3, 1, 2, 5]
def baseStart_3112421 : Nat := 118140960795 + 3112421 * 2 ^ 59
def prefixEnd_3112421 : Nat := 4983230072969 + 3 ^ 40 * 3112421 * 2
def baseEnd_3112421 : Nat := 355148438254993860494165

theorem tailTrace_3112421 : CollatzResearch.WordTrace tailWord_3112421 prefixEnd_3112421 355148438254993860494165 := by
  unfold tailWord_3112421
  simp only [CollatzResearch.WordTrace]
  refine ⟨113519319857237751032321117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75679546571491834021547411 113519319857237751032321117)
  ·
    refine ⟨42569744946464156637120419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113519319857237751032321117 42569744946464156637120419)
    ·
      refine ⟨63854617419696234955680629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42569744946464156637120419 63854617419696234955680629)
      ·
        refine ⟨5986370383096522027095059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63854617419696234955680629 5986370383096522027095059)
        ·
          refine ⟨8979555574644783040642589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5986370383096522027095059 8979555574644783040642589)
          ·
            refine ⟨3367333340491793640240971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8979555574644783040642589 3367333340491793640240971)
            ·
              refine ⟨5051000010737690460361457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3367333340491793640240971 5051000010737690460361457)
              ·
                refine ⟨3788250008053267845271093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5051000010737690460361457 3788250008053267845271093)
                ·
                  refine ⟨355148438254993860494165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3788250008053267845271093 355148438254993860494165)
                  ·
                    rfl

theorem cell22_3112421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 5].length) (baseStart_3112421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112421 prefixEnd_3112421 := by exact prefixLift 3112421
  have htrace : WordTrace (prefixWord ++ tailWord_3112421) baseStart_3112421 baseEnd_3112421 := by
    simpa [prefixWord, tailWord_3112421, baseEnd_3112421] using wordTrace_append hprefix tailTrace_3112421
  have hstable : (prefixWord ++ tailWord_3112421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112421).length < 2 ^ (prefixWord ++ tailWord_3112421).sum := by decide
  have hdescent : baseEnd_3112421 < baseStart_3112421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112432 : List Nat := [2, 1, 1, 1, 3, 4, 1, 3, 6]
def baseStart_3112432 : Nat := 118140960795 + 3112432 * 2 ^ 59
def prefixEnd_3112432 : Nat := 4983230072969 + 3 ^ 40 * 3112432 * 2
def baseEnd_3112432 : Nat := 355149693429927073152487

theorem tailTrace_3112432 : CollatzResearch.WordTrace tailWord_3112432 prefixEnd_3112432 355149693429927073152487 := by
  unfold tailWord_3112432
  simp only [CollatzResearch.WordTrace]
  refine ⟨56759860530098949955485775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75679814040131933273981033 56759860530098949955485775)
  ·
    refine ⟨85139790795148424933228663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56759860530098949955485775 85139790795148424933228663)
    ·
      refine ⟨127709686192722637399842995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85139790795148424933228663 127709686192722637399842995)
      ·
        refine ⟨191564529289083956099764493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127709686192722637399842995 191564529289083956099764493)
        ·
          refine ⟨71836698483406483537411685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191564529289083956099764493 71836698483406483537411685)
          ·
            refine ⟨13469380965638715663264691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71836698483406483537411685 13469380965638715663264691)
            ·
              refine ⟨20204071448458073494897037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13469380965638715663264691 20204071448458073494897037)
              ·
                refine ⟨7576526793171777560586389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20204071448458073494897037 7576526793171777560586389)
                ·
                  refine ⟨355149693429927073152487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7576526793171777560586389 355149693429927073152487)
                  ·
                    rfl

theorem cell22_3112432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 6].length) (baseStart_3112432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112432 prefixEnd_3112432 := by exact prefixLift 3112432
  have htrace : WordTrace (prefixWord ++ tailWord_3112432) baseStart_3112432 baseEnd_3112432 := by
    simpa [prefixWord, tailWord_3112432, baseEnd_3112432] using wordTrace_append hprefix tailTrace_3112432
  have hstable : (prefixWord ++ tailWord_3112432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112432).length < 2 ^ (prefixWord ++ tailWord_3112432).sum := by decide
  have hdescent : baseEnd_3112432 < baseStart_3112432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112447 : List Nat := [1, 1, 2, 2, 1, 2, 2, 5, 1, 5]
def baseStart_3112447 : Nat := 118140960795 + 3112447 * 2 ^ 59
def prefixEnd_3112447 : Nat := 4983230072969 + 3 ^ 40 * 3112447 * 2
def baseEnd_3112447 : Nat := 1065454215096326180332415

theorem tailTrace_3112447 : CollatzResearch.WordTrace tailWord_3112447 prefixEnd_3112447 1065454215096326180332415 := by
  unfold tailWord_3112447
  simp only [CollatzResearch.WordTrace]
  refine ⟨113520268155143557472767595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75680178770095704981845063 113520268155143557472767595)
  ·
    refine ⟨170280402232715336209151393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113520268155143557472767595 170280402232715336209151393)
    ·
      refine ⟨127710301674536502156863545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170280402232715336209151393 127710301674536502156863545)
      ·
        refine ⟨95782726255902376617647659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127710301674536502156863545 95782726255902376617647659)
        ·
          refine ⟨143674089383853564926471489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95782726255902376617647659 143674089383853564926471489)
          ·
            refine ⟨107755567037890173694853617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143674089383853564926471489 107755567037890173694853617)
            ·
              refine ⟨80816675278417630271140213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107755567037890173694853617 80816675278417630271140213)
              ·
                refine ⟨7576563307351652837919395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80816675278417630271140213 7576563307351652837919395)
                ·
                  refine ⟨11364844961027479256879093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7576563307351652837919395 11364844961027479256879093)
                  ·
                    refine ⟨1065454215096326180332415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11364844961027479256879093 1065454215096326180332415)
                    ·
                      rfl

theorem cell22_3112447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 5].length) (baseStart_3112447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112447 prefixEnd_3112447 := by exact prefixLift 3112447
  have htrace : WordTrace (prefixWord ++ tailWord_3112447) baseStart_3112447 baseEnd_3112447 := by
    simpa [prefixWord, tailWord_3112447, baseEnd_3112447] using wordTrace_append hprefix tailTrace_3112447
  have hstable : (prefixWord ++ tailWord_3112447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112447).length < 2 ^ (prefixWord ++ tailWord_3112447).sum := by decide
  have hdescent : baseEnd_3112447 < baseStart_3112447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112483 : List Nat := [1, 1, 1, 4, 5, 1, 3, 2, 4]
def baseStart_3112483 : Nat := 118140960795 + 3112483 * 2 ^ 59
def prefixEnd_3112483 : Nat := 4983230072969 + 3 ^ 40 * 3112483 * 2
def baseEnd_3112483 : Nat := 355155512877344695477435

theorem tailTrace_3112483 : CollatzResearch.WordTrace tailWord_3112483 prefixEnd_3112483 355155512877344695477435 := by
  unfold tailWord_3112483
  simp only [CollatzResearch.WordTrace]
  refine ⟨113521581183013135621078103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75681054122008757080718735 113521581183013135621078103)
  ·
    refine ⟨170282371774519703431617155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113521581183013135621078103 170282371774519703431617155)
    ·
      refine ⟨255423557661779555147425733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170282371774519703431617155 255423557661779555147425733)
      ·
        refine ⟨47891917061583666590142325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 255423557661779555147425733 47891917061583666590142325)
        ·
          refine ⟨4489867224523468742825843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47891917061583666590142325 4489867224523468742825843)
          ·
            refine ⟨6734800836785203114238765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4489867224523468742825843 6734800836785203114238765)
            ·
              refine ⟨2525550313794451167839537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6734800836785203114238765 2525550313794451167839537)
              ·
                refine ⟨1894162735345838375879653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2525550313794451167839537 1894162735345838375879653)
                ·
                  refine ⟨355155512877344695477435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1894162735345838375879653 355155512877344695477435)
                  ·
                    rfl

theorem cell22_3112483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 2, 4].length) (baseStart_3112483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112483 prefixEnd_3112483 := by exact prefixLift 3112483
  have htrace : WordTrace (prefixWord ++ tailWord_3112483) baseStart_3112483 baseEnd_3112483 := by
    simpa [prefixWord, tailWord_3112483, baseEnd_3112483] using wordTrace_append hprefix tailTrace_3112483
  have hstable : (prefixWord ++ tailWord_3112483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112483).length < 2 ^ (prefixWord ++ tailWord_3112483).sum := by decide
  have hdescent : baseEnd_3112483 < baseStart_3112483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112494 : List Nat := [4, 1, 3, 1, 2, 1, 1, 9]
def baseStart_3112494 : Nat := 118140960795 + 3112494 * 2 ^ 59
def prefixEnd_3112494 : Nat := 4983230072969 + 3 ^ 40 * 3112494 * 2
def baseEnd_3112494 : Nat := 118385589350759302711919

theorem tailTrace_3112494 : CollatzResearch.WordTrace tailWord_3112494 prefixEnd_3112494 118385589350759302711919 := by
  unfold tailWord_3112494
  simp only [CollatzResearch.WordTrace]
  refine ⟨14190247798246660562466067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75681321590648856333152357 14190247798246660562466067)
  ·
    refine ⟨21285371697369990843699101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14190247798246660562466067 21285371697369990843699101)
    ·
      refine ⟨7982014386513746566387163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21285371697369990843699101 7982014386513746566387163)
      ·
        refine ⟨11973021579770619849580745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7982014386513746566387163 11973021579770619849580745)
        ·
          refine ⟨8979766184827964887185559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11973021579770619849580745 8979766184827964887185559)
          ·
            refine ⟨13469649277241947330778339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8979766184827964887185559 13469649277241947330778339)
            ·
              refine ⟨20204473915862920996167509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13469649277241947330778339 20204473915862920996167509)
              ·
                refine ⟨118385589350759302711919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20204473915862920996167509 118385589350759302711919)
                ·
                  rfl

theorem cell22_3112494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 9].length) (baseStart_3112494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112494 prefixEnd_3112494 := by exact prefixLift 3112494
  have htrace : WordTrace (prefixWord ++ tailWord_3112494) baseStart_3112494 baseEnd_3112494 := by
    simpa [prefixWord, tailWord_3112494, baseEnd_3112494] using wordTrace_append hprefix tailTrace_3112494
  have hstable : (prefixWord ++ tailWord_3112494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112494).length < 2 ^ (prefixWord ++ tailWord_3112494).sum := by decide
  have hdescent : baseEnd_3112494 < baseStart_3112494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112534 : List Nat := [5, 2, 2, 2, 1, 2, 2, 2, 4]
def baseStart_3112534 : Nat := 118140960795 + 3112534 * 2 ^ 59
def prefixEnd_3112534 : Nat := 4983230072969 + 3 ^ 40 * 3112534 * 2
def baseEnd_3112534 : Nat := 355161332324762317802383

theorem tailTrace_3112534 : CollatzResearch.WordTrace tailWord_3112534 prefixEnd_3112534 355161332324762317802383 := by
  unfold tailWord_3112534
  simp only [CollatzResearch.WordTrace]
  refine ⟨7095215081614273208199041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75682294203885580887456437 7095215081614273208199041)
  ·
    refine ⟨5321411311210704906149281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7095215081614273208199041 5321411311210704906149281)
    ·
      refine ⟨3991058483408028679611961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5321411311210704906149281 3991058483408028679611961)
      ·
        refine ⟨2993293862556021509708971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3991058483408028679611961 2993293862556021509708971)
        ·
          refine ⟨4489940793834032264563457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2993293862556021509708971 4489940793834032264563457)
          ·
            refine ⟨3367455595375524198422593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4489940793834032264563457 3367455595375524198422593)
            ·
              refine ⟨2525591696531643148816945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3367455595375524198422593 2525591696531643148816945)
              ·
                refine ⟨1894193772398732361612709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2525591696531643148816945 1894193772398732361612709)
                ·
                  refine ⟨355161332324762317802383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1894193772398732361612709 355161332324762317802383)
                  ·
                    rfl

theorem cell22_3112534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_3112534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112534 prefixEnd_3112534 := by exact prefixLift 3112534
  have htrace : WordTrace (prefixWord ++ tailWord_3112534) baseStart_3112534 baseEnd_3112534 := by
    simpa [prefixWord, tailWord_3112534, baseEnd_3112534] using wordTrace_append hprefix tailTrace_3112534
  have hstable : (prefixWord ++ tailWord_3112534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112534).length < 2 ^ (prefixWord ++ tailWord_3112534).sum := by decide
  have hdescent : baseEnd_3112534 < baseStart_3112534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112537 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 3, 7]
def baseStart_3112537 : Nat := 118140960795 + 3112537 * 2 ^ 59
def prefixEnd_3112537 : Nat := 4983230072969 + 3 ^ 40 * 3112537 * 2
def baseEnd_3112537 : Nat := 1065485023935595945582139

theorem tailTrace_3112537 : CollatzResearch.WordTrace tailWord_3112537 prefixEnd_3112537 1065485023935595945582139 := by
  unfold tailWord_3112537
  simp only [CollatzResearch.WordTrace]
  refine ⟨113523550724817502843543865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75682367149878335229029243 113523550724817502843543865)
  ·
    refine ⟨85142663043613127132657899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113523550724817502843543865 85142663043613127132657899)
    ·
      refine ⟨127713994565419690698986849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85142663043613127132657899 127713994565419690698986849)
      ·
        refine ⟨95785495924064768024240137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127713994565419690698986849 95785495924064768024240137)
        ·
          refine ⟨71839121943048576018180103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95785495924064768024240137 71839121943048576018180103)
          ·
            refine ⟨107758682914572864027270155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71839121943048576018180103 107758682914572864027270155)
            ·
              refine ⟨161638024371859296040905233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107758682914572864027270155 161638024371859296040905233)
              ·
                refine ⟨121228518278894472030678925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161638024371859296040905233 121228518278894472030678925)
                ·
                  refine ⟨45460694354585427011504597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121228518278894472030678925 45460694354585427011504597)
                  ·
                    refine ⟨1065485023935595945582139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45460694354585427011504597 1065485023935595945582139)
                    ·
                      rfl

theorem cell22_3112537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 7].length) (baseStart_3112537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112537 prefixEnd_3112537 := by exact prefixLift 3112537
  have htrace : WordTrace (prefixWord ++ tailWord_3112537) baseStart_3112537 baseEnd_3112537 := by
    simpa [prefixWord, tailWord_3112537, baseEnd_3112537] using wordTrace_append hprefix tailTrace_3112537
  have hstable : (prefixWord ++ tailWord_3112537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112537).length < 2 ^ (prefixWord ++ tailWord_3112537).sum := by decide
  have hdescent : baseEnd_3112537 < baseStart_3112537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112554 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 1, 7]
def baseStart_3112554 : Nat := 118140960795 + 3112554 * 2 ^ 59
def prefixEnd_3112554 : Nat := 4983230072969 + 3 ^ 40 * 3112554 * 2
def baseEnd_3112554 : Nat := 1065490843383013567907087

theorem tailTrace_3112554 : CollatzResearch.WordTrace tailWord_3112554 prefixEnd_3112554 1065490843383013567907087 := by
  unfold tailWord_3112554
  simp only [CollatzResearch.WordTrace]
  refine ⟨28381042691438978686728179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75682780510503943164608477 28381042691438978686728179)
  ·
    refine ⟨42571564037158468030092269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28381042691438978686728179 42571564037158468030092269)
    ·
      refine ⟨15964336513934425511284601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42571564037158468030092269 15964336513934425511284601)
      ·
        refine ⟨11973252385450819133463451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15964336513934425511284601 11973252385450819133463451)
        ·
          refine ⟨17959878578176228700195177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11973252385450819133463451 17959878578176228700195177)
          ·
            refine ⟨13469908933632171525146383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17959878578176228700195177 13469908933632171525146383)
            ·
              refine ⟨20204863400448257287719575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13469908933632171525146383 20204863400448257287719575)
              ·
                refine ⟨30307295100672385931579363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20204863400448257287719575 30307295100672385931579363)
                ·
                  refine ⟨45460942651008578897369045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30307295100672385931579363 45460942651008578897369045)
                  ·
                    refine ⟨1065490843383013567907087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45460942651008578897369045 1065490843383013567907087)
                    ·
                      rfl

theorem cell22_3112554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_3112554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112554 prefixEnd_3112554 := by exact prefixLift 3112554
  have htrace : WordTrace (prefixWord ++ tailWord_3112554) baseStart_3112554 baseEnd_3112554 := by
    simpa [prefixWord, tailWord_3112554, baseEnd_3112554] using wordTrace_append hprefix tailTrace_3112554
  have hstable : (prefixWord ++ tailWord_3112554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112554).length < 2 ^ (prefixWord ++ tailWord_3112554).sum := by decide
  have hdescent : baseEnd_3112554 < baseStart_3112554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112569 : List Nat := [1, 2, 1, 3, 3, 1, 1, 3, 3, 4]
def baseStart_3112569 : Nat := 118140960795 + 3112569 * 2 ^ 59
def prefixEnd_3112569 : Nat := 4983230072969 + 3 ^ 40 * 3112569 * 2
def baseEnd_3112569 : Nat := 1065495978189558528782041

theorem tailTrace_3112569 : CollatzResearch.WordTrace tailWord_3112569 prefixEnd_3112569 1065495978189558528782041 := by
  unfold tailWord_3112569
  simp only [CollatzResearch.WordTrace]
  refine ⟨113524717860701572308708761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75683145240467714872472507 113524717860701572308708761)
  ·
    refine ⟨85143538395526179231531571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113524717860701572308708761 85143538395526179231531571)
    ·
      refine ⟨127715307593289268847297357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85143538395526179231531571 127715307593289268847297357)
      ·
        refine ⟨47893240347483475817736509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127715307593289268847297357 47893240347483475817736509)
        ·
          refine ⟨17959965130306303431651191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47893240347483475817736509 17959965130306303431651191)
          ·
            refine ⟨26939947695459455147476787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17959965130306303431651191 26939947695459455147476787)
            ·
              refine ⟨40409921543189182721215181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26939947695459455147476787 40409921543189182721215181)
              ·
                refine ⟨15153720578695943520455693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40409921543189182721215181 15153720578695943520455693)
                ·
                  refine ⟨5682645217010978820170885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15153720578695943520455693 5682645217010978820170885)
                  ·
                    refine ⟨1065495978189558528782041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5682645217010978820170885 1065495978189558528782041)
                    ·
                      rfl

theorem cell22_3112569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 4].length) (baseStart_3112569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112569 prefixEnd_3112569 := by exact prefixLift 3112569
  have htrace : WordTrace (prefixWord ++ tailWord_3112569) baseStart_3112569 baseEnd_3112569 := by
    simpa [prefixWord, tailWord_3112569, baseEnd_3112569] using wordTrace_append hprefix tailTrace_3112569
  have hstable : (prefixWord ++ tailWord_3112569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112569).length < 2 ^ (prefixWord ++ tailWord_3112569).sum := by decide
  have hdescent : baseEnd_3112569 < baseStart_3112569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112708 : List Nat := [2, 3, 2, 2, 1, 3, 2, 2, 5]
def baseStart_3112708 : Nat := 118140960795 + 3112708 * 2 ^ 59
def prefixEnd_3112708 : Nat := 4983230072969 + 3 ^ 40 * 3112708 * 2
def baseEnd_3112708 : Nat := 355181186910069499852205

theorem tailTrace_3112708 : CollatzResearch.WordTrace tailWord_3112708 prefixEnd_3112708 355181186910069499852205 := by
  unfold tailWord_3112708
  simp only [CollatzResearch.WordTrace]
  refine ⟨56764893803598999524009389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75686525071465332698679185 56764893803598999524009389)
  ·
    refine ⟨21286835176349624821503521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56764893803598999524009389 21286835176349624821503521)
    ·
      refine ⟨15965126382262218616127641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21286835176349624821503521 15965126382262218616127641)
      ·
        refine ⟨11973844786696663962095731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15965126382262218616127641 11973844786696663962095731)
        ·
          refine ⟨17960767180044995943143597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11973844786696663962095731 17960767180044995943143597)
          ·
            refine ⟨6735287692516873478678849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17960767180044995943143597 6735287692516873478678849)
            ·
              refine ⟨5051465769387655109009137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6735287692516873478678849 5051465769387655109009137)
              ·
                refine ⟨3788599327040741331756853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5051465769387655109009137 3788599327040741331756853)
                ·
                  refine ⟨355181186910069499852205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3788599327040741331756853 355181186910069499852205)
                  ·
                    rfl

theorem cell22_3112708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_3112708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112708 prefixEnd_3112708 := by exact prefixLift 3112708
  have htrace : WordTrace (prefixWord ++ tailWord_3112708) baseStart_3112708 baseEnd_3112708 := by
    simpa [prefixWord, tailWord_3112708, baseEnd_3112708] using wordTrace_append hprefix tailTrace_3112708
  have hstable : (prefixWord ++ tailWord_3112708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112708).length < 2 ^ (prefixWord ++ tailWord_3112708).sum := by decide
  have hdescent : baseEnd_3112708 < baseStart_3112708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112736 : List Nat := [2, 1, 1, 5, 1, 1, 3, 2, 6]
def baseStart_3112736 : Nat := 118140960795 + 3112736 * 2 ^ 59
def prefixEnd_3112736 : Nat := 4983230072969 + 3 ^ 40 * 3112736 * 2
def baseEnd_3112736 : Nat := 355184381900808586618843

theorem tailTrace_3112736 : CollatzResearch.WordTrace tailWord_3112736 prefixEnd_3112736 355184381900808586618843 := by
  unfold tailWord_3112736
  simp only [CollatzResearch.WordTrace]
  refine ⟨56765404425548279915019031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75687205900731039886692041 56765404425548279915019031)
  ·
    refine ⟨85148106638322419872528547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56765404425548279915019031 85148106638322419872528547)
    ·
      refine ⟨127722159957483629808792821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85148106638322419872528547 127722159957483629808792821)
      ·
        refine ⟨11973952496014090294574327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127722159957483629808792821 11973952496014090294574327)
        ·
          refine ⟨17960928744021135441861491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11973952496014090294574327 17960928744021135441861491)
          ·
            refine ⟨26941393116031703162792237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17960928744021135441861491 26941393116031703162792237)
            ·
              refine ⟨10103022418511888686047089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26941393116031703162792237 10103022418511888686047089)
              ·
                refine ⟨7577266813883916514535317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10103022418511888686047089 7577266813883916514535317)
                ·
                  refine ⟨355184381900808586618843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7577266813883916514535317 355184381900808586618843)
                  ·
                    rfl

theorem cell22_3112736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 6].length) (baseStart_3112736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112736 prefixEnd_3112736 := by exact prefixLift 3112736
  have htrace : WordTrace (prefixWord ++ tailWord_3112736) baseStart_3112736 baseEnd_3112736 := by
    simpa [prefixWord, tailWord_3112736, baseEnd_3112736] using wordTrace_append hprefix tailTrace_3112736
  have hstable : (prefixWord ++ tailWord_3112736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112736).length < 2 ^ (prefixWord ++ tailWord_3112736).sum := by decide
  have hdescent : baseEnd_3112736 < baseStart_3112736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112738 : List Nat := [3, 3, 1, 1, 2, 1, 2, 4, 1, 4]
def baseStart_3112738 : Nat := 118140960795 + 3112738 * 2 ^ 59
def prefixEnd_3112738 : Nat := 4983230072969 + 3 ^ 40 * 3112738 * 2
def baseEnd_3112738 : Nat := 1065553830343298421306523

theorem tailTrace_3112738 : CollatzResearch.WordTrace tailWord_3112738 prefixEnd_3112738 1065553830343298421306523 := by
  unfold tailWord_3112738
  simp only [CollatzResearch.WordTrace]
  refine ⟨28382720449272328542902717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75687254531392876114407245 28382720449272328542902717)
  ·
    refine ⟨10643520168477123203588519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28382720449272328542902717 10643520168477123203588519)
    ·
      refine ⟨15965280252715684805382779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10643520168477123203588519 15965280252715684805382779)
      ·
        refine ⟨23947920379073527208074169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15965280252715684805382779 23947920379073527208074169)
        ·
          refine ⟨17960940284305145406055627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23947920379073527208074169 17960940284305145406055627)
          ·
            refine ⟨26941410426457718109083441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17960940284305145406055627 26941410426457718109083441)
            ·
              refine ⟨20206057819843288581812581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26941410426457718109083441 20206057819843288581812581)
              ·
                refine ⟨3788635841220616609089859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20206057819843288581812581 3788635841220616609089859)
                ·
                  refine ⟨5682953761830924913634789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3788635841220616609089859 5682953761830924913634789)
                  ·
                    refine ⟨1065553830343298421306523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5682953761830924913634789 1065553830343298421306523)
                    ·
                      rfl

theorem cell22_3112738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_3112738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112738 prefixEnd_3112738 := by exact prefixLift 3112738
  have htrace : WordTrace (prefixWord ++ tailWord_3112738) baseStart_3112738 baseEnd_3112738 := by
    simpa [prefixWord, tailWord_3112738, baseEnd_3112738] using wordTrace_append hprefix tailTrace_3112738
  have hstable : (prefixWord ++ tailWord_3112738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112738).length < 2 ^ (prefixWord ++ tailWord_3112738).sum := by decide
  have hdescent : baseEnd_3112738 < baseStart_3112738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112751 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 6, 3]
def baseStart_3112751 : Nat := 118140960795 + 3112751 * 2 ^ 59
def prefixEnd_3112751 : Nat := 4983230072969 + 3 ^ 40 * 3112751 * 2
def baseEnd_3112751 : Nat := 1065558280508970720731483

theorem tailTrace_3112751 : CollatzResearch.WordTrace tailWord_3112751 prefixEnd_3112751 1065558280508970720731483 := by
  unfold tailWord_3112751
  simp only [CollatzResearch.WordTrace]
  refine ⟨113531355946042217391834107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75687570630694811594556071 113531355946042217391834107)
  ·
    refine ⟨170297033919063326087751161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113531355946042217391834107 170297033919063326087751161)
    ·
      refine ⟨127722775439297494565813371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170297033919063326087751161 127722775439297494565813371)
      ·
        refine ⟨191584163158946241848720057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127722775439297494565813371 191584163158946241848720057)
        ·
          refine ⟨143688122369209681386540043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191584163158946241848720057 143688122369209681386540043)
          ·
            refine ⟨215532183553814522079810065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143688122369209681386540043 215532183553814522079810065)
            ·
              refine ⟨161649137665360891559857549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215532183553814522079810065 161649137665360891559857549)
              ·
                refine ⟨60618426624510334334946581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161649137665360891559857549 60618426624510334334946581)
                ·
                  refine ⟨2841488748023921921950621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60618426624510334334946581 2841488748023921921950621)
                  ·
                    refine ⟨1065558280508970720731483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2841488748023921921950621 1065558280508970720731483)
                    ·
                      rfl

theorem cell22_3112751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 6, 3].length) (baseStart_3112751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112751 prefixEnd_3112751 := by exact prefixLift 3112751
  have htrace : WordTrace (prefixWord ++ tailWord_3112751) baseStart_3112751 baseEnd_3112751 := by
    simpa [prefixWord, tailWord_3112751, baseEnd_3112751] using wordTrace_append hprefix tailTrace_3112751
  have hstable : (prefixWord ++ tailWord_3112751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112751).length < 2 ^ (prefixWord ++ tailWord_3112751).sum := by decide
  have hdescent : baseEnd_3112751 < baseStart_3112751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112753 : List Nat := [1, 2, 2, 3, 2, 2, 1, 5, 4]
def baseStart_3112753 : Nat := 118140960795 + 3112753 * 2 ^ 59
def prefixEnd_3112753 : Nat := 4983230072969 + 3 ^ 40 * 3112753 * 2
def baseEnd_3112753 : Nat := 355186321716614460727159

theorem tailTrace_3112753 : CollatzResearch.WordTrace tailWord_3112753 prefixEnd_3112753 355186321716614460727159 := by
  unfold tailWord_3112753
  simp only [CollatzResearch.WordTrace]
  refine ⟨113531428892034971733406913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75687619261356647822271275 113531428892034971733406913)
  ·
    refine ⟨85148571669026228800055185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113531428892034971733406913 85148571669026228800055185)
    ·
      refine ⟨63861428751769671600041389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85148571669026228800055185 63861428751769671600041389)
      ·
        refine ⟨23948035781913626850015521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63861428751769671600041389 23948035781913626850015521)
        ·
          refine ⟨17961026836435220137511641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23948035781913626850015521 17961026836435220137511641)
          ·
            refine ⟨13470770127326415103133731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17961026836435220137511641 13470770127326415103133731)
            ·
              refine ⟨20206155190989622654700597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13470770127326415103133731 20206155190989622654700597)
              ·
                refine ⟨1894327049155277123878181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20206155190989622654700597 1894327049155277123878181)
                ·
                  refine ⟨355186321716614460727159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1894327049155277123878181 355186321716614460727159)
                  ·
                    rfl

theorem cell22_3112753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 5, 4].length) (baseStart_3112753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112753 prefixEnd_3112753 := by exact prefixLift 3112753
  have htrace : WordTrace (prefixWord ++ tailWord_3112753) baseStart_3112753 baseEnd_3112753 := by
    simpa [prefixWord, tailWord_3112753, baseEnd_3112753] using wordTrace_append hprefix tailTrace_3112753
  have hstable : (prefixWord ++ tailWord_3112753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112753).length < 2 ^ (prefixWord ++ tailWord_3112753).sum := by decide
  have hdescent : baseEnd_3112753 < baseStart_3112753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112813 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 5, 3]
def baseStart_3112813 : Nat := 118140960795 + 3112813 * 2 ^ 59
def prefixEnd_3112813 : Nat := 4983230072969 + 3 ^ 40 * 3112813 * 2
def baseEnd_3112813 : Nat := 1065579504376023225681293

theorem tailTrace_3112813 : CollatzResearch.WordTrace tailWord_3112813 prefixEnd_3112813 1065579504376023225681293 := by
  unfold tailWord_3112813
  simp only [CollatzResearch.WordTrace]
  refine ⟨113533617271817601980591093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75689078181211734653727395 113533617271817601980591093)
  ·
    refine ⟨10643776619232900185680415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113533617271817601980591093 10643776619232900185680415)
    ·
      refine ⟨15965664928849350278520623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10643776619232900185680415 15965664928849350278520623)
      ·
        refine ⟨23948497393274025417780935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15965664928849350278520623 23948497393274025417780935)
        ·
          refine ⟨35922746089911038126671403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23948497393274025417780935 35922746089911038126671403)
          ·
            refine ⟨53884119134866557190007105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35922746089911038126671403 53884119134866557190007105)
            ·
              refine ⟨40413089351149917892505329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53884119134866557190007105 40413089351149917892505329)
              ·
                refine ⟨30309817013362438419378997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40413089351149917892505329 30309817013362438419378997)
                ·
                  refine ⟨2841545345002728601816781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30309817013362438419378997 2841545345002728601816781)
                  ·
                    refine ⟨1065579504376023225681293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2841545345002728601816781 1065579504376023225681293)
                    ·
                      rfl

theorem cell22_3112813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_3112813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112813 prefixEnd_3112813 := by exact prefixLift 3112813
  have htrace : WordTrace (prefixWord ++ tailWord_3112813) baseStart_3112813 baseEnd_3112813 := by
    simpa [prefixWord, tailWord_3112813, baseEnd_3112813] using wordTrace_append hprefix tailTrace_3112813
  have hstable : (prefixWord ++ tailWord_3112813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112813).length < 2 ^ (prefixWord ++ tailWord_3112813).sum := by decide
  have hdescent : baseEnd_3112813 < baseStart_3112813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112826 : List Nat := [3, 1, 1, 1, 1, 1, 6, 1, 7]
def baseStart_3112826 : Nat := 118140960795 + 3112826 * 2 ^ 59
def prefixEnd_3112826 : Nat := 4983230072969 + 3 ^ 40 * 3112826 * 2
def baseEnd_3112826 : Nat := 355194651513898508368751

theorem tailTrace_3112826 : CollatzResearch.WordTrace tailWord_3112826 prefixEnd_3112826 355194651513898508368751 := by
  unfold tailWord_3112826
  simp only [CollatzResearch.WordTrace]
  refine ⟨28383522855192626300203583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75689394280513670133876221 28383522855192626300203583)
  ·
    refine ⟨42575284282788939450305375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28383522855192626300203583 42575284282788939450305375)
    ·
      refine ⟨63862926424183409175458063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42575284282788939450305375 63862926424183409175458063)
      ·
        refine ⟨95794389636275113763187095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63862926424183409175458063 95794389636275113763187095)
        ·
          refine ⟨143691584454412670644780643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95794389636275113763187095 143691584454412670644780643)
          ·
            refine ⟨215537376681619005967170965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143691584454412670644780643 215537376681619005967170965)
            ·
              refine ⟨10103314531950890904711139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 215537376681619005967170965 10103314531950890904711139)
              ·
                refine ⟨15154971797926336357066709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10103314531950890904711139 15154971797926336357066709)
                ·
                  refine ⟨355194651513898508368751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15154971797926336357066709 355194651513898508368751)
                  ·
                    rfl

theorem cell22_3112826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 7].length) (baseStart_3112826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112826 prefixEnd_3112826 := by exact prefixLift 3112826
  have htrace : WordTrace (prefixWord ++ tailWord_3112826) baseStart_3112826 baseEnd_3112826 := by
    simpa [prefixWord, tailWord_3112826, baseEnd_3112826] using wordTrace_append hprefix tailTrace_3112826
  have hstable : (prefixWord ++ tailWord_3112826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112826).length < 2 ^ (prefixWord ++ tailWord_3112826).sum := by decide
  have hdescent : baseEnd_3112826 < baseStart_3112826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112841 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 1, 7]
def baseStart_3112841 : Nat := 118140960795 + 3112841 * 2 ^ 59
def prefixEnd_3112841 : Nat := 4983230072969 + 3 ^ 40 * 3112841 * 2
def baseEnd_3112841 : Nat := 1065589089348240485981207

theorem tailTrace_3112841 : CollatzResearch.WordTrace tailWord_3112841 prefixEnd_3112841 1065589089348240485981207 := by
  unfold tailWord_3112841
  simp only [CollatzResearch.WordTrace]
  refine ⟨113534638515716162762610377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75689759010477441841740251 113534638515716162762610377)
  ·
    refine ⟨85150978886787122071957783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113534638515716162762610377 85150978886787122071957783)
    ·
      refine ⟨127726468330180683107936675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85150978886787122071957783 127726468330180683107936675)
      ·
        refine ⟨191589702495271024661905013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127726468330180683107936675 191589702495271024661905013)
        ·
          refine ⟨17961534608931658562053595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 191589702495271024661905013 17961534608931658562053595)
          ·
            refine ⟨26942301913397487843080393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17961534608931658562053595 26942301913397487843080393)
            ·
              refine ⟨20206726435048115882310295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26942301913397487843080393 20206726435048115882310295)
              ·
                refine ⟨30310089652572173823465443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20206726435048115882310295 30310089652572173823465443)
                ·
                  refine ⟨45465134478858260735198165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30310089652572173823465443 45465134478858260735198165)
                  ·
                    refine ⟨1065589089348240485981207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45465134478858260735198165 1065589089348240485981207)
                    ·
                      rfl

theorem cell22_3112841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 7].length) (baseStart_3112841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112841 prefixEnd_3112841 := by exact prefixLift 3112841
  have htrace : WordTrace (prefixWord ++ tailWord_3112841) baseStart_3112841 baseEnd_3112841 := by
    simpa [prefixWord, tailWord_3112841, baseEnd_3112841] using wordTrace_append hprefix tailTrace_3112841
  have hstable : (prefixWord ++ tailWord_3112841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112841).length < 2 ^ (prefixWord ++ tailWord_3112841).sum := by decide
  have hdescent : baseEnd_3112841 < baseStart_3112841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112903 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 6, 3]
def baseStart_3112903 : Nat := 118140960795 + 3112903 * 2 ^ 59
def prefixEnd_3112903 : Nat := 4983230072969 + 3 ^ 40 * 3112903 * 2
def baseEnd_3112903 : Nat := 1065610313215292990931017

theorem tailTrace_3112903 : CollatzResearch.WordTrace tailWord_3112903 prefixEnd_3112903 1065610313215292990931017 := by
  unfold tailWord_3112903
  simp only [CollatzResearch.WordTrace]
  refine ⟨113536899841491547351367363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75691266560994364900911575 113536899841491547351367363)
  ·
    refine ⟨170305349762237321027051045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113536899841491547351367363 170305349762237321027051045)
    ·
      refine ⟨31932253080419497692572071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170305349762237321027051045 31932253080419497692572071)
      ·
        refine ⟨47898379620629246538858107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31932253080419497692572071 47898379620629246538858107)
        ·
          refine ⟨71847569430943869808287161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47898379620629246538858107 71847569430943869808287161)
          ·
            refine ⟨53885677073207902356215371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71847569430943869808287161 53885677073207902356215371)
            ·
              refine ⟨80828515609811853534323057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53885677073207902356215371 80828515609811853534323057)
              ·
                refine ⟨60621386707358890150742293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80828515609811853534323057 60621386707358890150742293)
                ·
                  refine ⟨2841627501907447975816045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60621386707358890150742293 2841627501907447975816045)
                  ·
                    refine ⟨1065610313215292990931017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2841627501907447975816045 1065610313215292990931017)
                    ·
                      rfl

theorem cell22_3112903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_3112903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112903 prefixEnd_3112903 := by exact prefixLift 3112903
  have htrace : WordTrace (prefixWord ++ tailWord_3112903) baseStart_3112903 baseEnd_3112903 := by
    simpa [prefixWord, tailWord_3112903, baseEnd_3112903] using wordTrace_append hprefix tailTrace_3112903
  have hstable : (prefixWord ++ tailWord_3112903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112903).length < 2 ^ (prefixWord ++ tailWord_3112903).sum := by decide
  have hdescent : baseEnd_3112903 < baseStart_3112903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
